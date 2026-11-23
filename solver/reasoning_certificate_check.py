#!/usr/bin/env python3
"""Kernel-check concrete reasoning receipts and reject false nearby claims."""
from __future__ import annotations

import hashlib
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

import verify

ROOT = Path(__file__).resolve().parents[1]
CLAIMS = [
    ("controller_value", "IncrementalControl.value chain 1 chainCache 0", "1", "2"),
    ("dependency_count", "changedChain.val.work", "9", "8"),
    ("complete_frontier", "(ParametricPareto.frontier pointCache.val).map (·.id)", "[0,1,2,4]", "[0,1,2]"),
    ("parameter_choice", "(ParametricPareto.selectFrontier xPareto.val (fun i => if i = 0 then 0 else 1)).map (·.id)", "some 4", "some 1"),
    ("policy_frontier", "(ParametricPareto.frontier (ParetoPolicy.state vectorModel 2 1 ())).map (·.id)", "[1]", "[0]"),
    ("original_hma_choice", "xOutput.value.chosen", "some [0]", "some [2]"),
]
HEADER = "import ReasoningControls\nset_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\nopen ReasoningControls\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    lean = os.environ.get("LEAN", "lean")
    verify.need("HMA_BUILD_DIR" in os.environ, "reasoning certificates require cold-built gate modules")
    env = dict(os.environ, LEAN_PATH=os.environ["HMA_BUILD_DIR"])
    source = HEADER + "namespace ConcreteReasoning\n" + "".join(
        f"theorem {name} : {expr} = {correct} := by decide\n" for name, expr, correct, _ in CLAIMS) + \
        "end ConcreteReasoning\n" + "".join(f"#print axioms ConcreteReasoning.{c[0]}\n" for c in CLAIMS)
    with tempfile.TemporaryDirectory(prefix="hma-reasoning-certificates-") as tmp:
        tmp = Path(tmp)
        accepted = tmp / "Accepted.lean"
        accepted.write_text(source)

        def compile_file(path):
            return subprocess.run([lean, "-DwarningAsError=true", "--root=" + str(tmp), str(path)],
                                  env=env, capture_output=True, timeout=180)

        result = compile_file(accepted)
        verify.need(result.returncode == 0, "kernel rejected concrete reasoning receipt:\n" +
                    result.stdout.decode() + result.stderr.decode())
        audited = {}
        for line in result.stdout.decode().splitlines():
            match = re.fullmatch(r"'ConcreteReasoning\.([^']+)' depends on axioms: \[(.*)\]", line)
            if match:
                used = sorted(filter(None, (x.strip() for x in match[2].split(","))))
            else:
                match = re.fullmatch(r"'ConcreteReasoning\.([^']+)' does not depend on any axioms", line)
                verify.need(match is not None, "unexpected kernel audit line: " + line)
                used = []
            verify.need(set(used) <= {"propext", "Classical.choice", "Quot.sound"}, "unexpected principle")
            audited[match[1]] = used
        verify.need(set(audited) == {c[0] for c in CLAIMS}, "incomplete concrete reasoning axiom audit")
        for name, expr, _, wrong in CLAIMS:
            bad = tmp / ("Rejected_" + name + ".lean")
            bad.write_text(HEADER + f"theorem claimed : {expr} = {wrong} := by decide\n")
            result = compile_file(bad)
            output = (result.stdout + result.stderr).decode()
            verify.need(result.returncode != 0 and "tactic 'decide' proved that the proposition" in output and "is false" in output,
                        "wrong reasoning receipt did not fail for the expected logical reason: " + name + "\n" + output)
        report = {"schema": 1, "kernel_checked": len(CLAIMS), "rejected_false_claims": [c[0] for c in CLAIMS],
                  "source_sha256": hashlib.sha256(source.encode()).hexdigest(), "axioms": audited}
        path = ROOT / "solver/results/reasoning-certificates.json"
        encoded = verify.canonical(report)
        if args.record:
            path.write_text(encoded)
        else:
            verify.need(path.is_file() and path.read_text() == encoded, "reasoning kernel receipts are absent or stale")
        print(f"REASONING CERTIFICATE GATE PASS: {len(CLAIMS)} concrete outputs kernel-checked; "
              f"{len(CLAIMS)} false nearby receipts rejected by kernel reduction; standard dependencies only")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
