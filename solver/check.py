#!/usr/bin/env python3
"""Required implementation checks, called by the cold proof/check.sh gate."""
from __future__ import annotations

import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

import verify

HERE = Path(__file__).resolve().parent
REQUIRED = {"X", "D", "E-empty", "E-singleton", "arena", "tie", "typed-weighted", "empty-universe"}


def need(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def run_solver(path: Path, seed: int = 1) -> bytes:
    result = subprocess.run([sys.executable, str(HERE / "solve.py"), str(path)],
                            env=dict(os.environ, PYTHONHASHSEED=str(seed)),
                            capture_output=True, timeout=120)
    need(result.returncode == 0, "Solver failed: " + result.stderr.decode(errors="replace"))
    need(not result.stderr, "Unexpected solver diagnostics")
    return result.stdout


def permute(instance: dict) -> dict:
    """The same finite instance with every set declaration ordered differently."""
    changed = copy.deepcopy(instance)
    changed["axes"].reverse()
    for axis in changed["axes"]:
        axis["values"].reverse()
    changed["components"].reverse()
    changed["contract"].reverse()
    for row in changed["contract"]:
        row["axes"].reverse()
        row["behavior"].reverse()
    changed["hyperedges"].reverse()
    for edge in changed["hyperedges"]:
        edge["components"].reverse()
    return changed


def rejection_controls(expected: dict) -> int:
    mutations = []

    def change(label, action):
        value = copy.deepcopy(expected)
        action(value)
        mutations.append((label, value))

    change("chosen non-highest", lambda x: x["chosen"].update(axes=["c"], rho=[1, 2]))
    change("rho", lambda x: x["chosen"].update(rho=[1, 4]))
    change("full emergence", lambda x: x["full"].update(mu=2))
    change("full live set", lambda x: x["full"].update(live=[]))
    change("engaged structure", lambda x: x["full"].update(engaged=[]))
    change("omitted minimal", lambda x: x["minimal"].pop())
    change("spurious minimal", lambda x: x["minimal"].append({"axes": ["b"], "rho": [0, 1]}))
    change("minimal rho", lambda x: x["minimal"][1].update(rho=[1, 3]))
    change("dead disposition", lambda x: x["dispositions"][2].update(emergent_dead=False))
    change("membership disposition", lambda x: x["dispositions"][2].update(membership="none"))
    change("search count", lambda x: x["counts"].update(subsets=7))
    change("missing subset", lambda x: x["subsets"].pop())
    change("subset live", lambda x: x["subsets"][0].update(live=["p"]))
    change("subset rho", lambda x: x["subsets"][0].update(rho=[1, 0]))
    change("subset sufficiency", lambda x: x["subsets"][0].update(sufficient=True))
    change("subset minimality", lambda x: x["subsets"][0].update(minimal=True))
    change("subset highest", lambda x: x["subsets"][0].update(highest=True))
    change("extra field", lambda x: x.update(unchecked=True))
    change("numeric boolean coercion", lambda x: x["subsets"][0].update(sufficient=0))
    for label, value in mutations:
        try:
            verify.compare_result(expected, value)
        except verify.Rejected:
            continue
        raise RuntimeError("Checker accepted corrupt output: " + label)
    return len(mutations)


def malformed_controls(base: dict, directory: Path) -> int:
    bad = []

    def change(label, action):
        value = copy.deepcopy(base)
        action(value)
        bad.append((label, json.dumps(value)))

    change("duplicate axis", lambda x: x["axes"].append(copy.deepcopy(x["axes"][0])))
    change("duplicate component", lambda x: x["components"].append("p"))
    change("duplicate finite value", lambda x: x["axes"][0]["values"].append(False))
    change("duplicate configuration", lambda x: x["contract"].append(copy.deepcopy(x["contract"][0])))
    change("inconsistent behavior", lambda x: x["contract"].append({"axes": x["contract"][0]["axes"], "behavior": [True] * 4}))
    change("unknown component", lambda x: x["hyperedges"][0]["components"].append("absent"))
    change("repeated edge member", lambda x: x["hyperedges"][0]["components"].append("p"))
    change("repeated edge set", lambda x: x["hyperedges"].append(copy.deepcopy(x["hyperedges"][0])))
    change("nonpositive interacting weight", lambda x: x["hyperedges"][0].update(weight=0))
    change("boolean weight", lambda x: x["hyperedges"][0].update(weight=True))
    change("negative weight", lambda x: x["hyperedges"][0].update(weight=-1))
    change("float value", lambda x: x["axes"][0]["values"].append(0.5))
    change("value outside range", lambda x: x["contract"][0]["axes"].__setitem__(0, "bad"))
    change("incomplete configuration", lambda x: x["contract"][0]["axes"].pop())
    change("incomplete behavior", lambda x: x["contract"][0]["behavior"].pop())
    change("empty range with row", lambda x: x["axes"][0].update(values=[]))
    change("boolean schema", lambda x: x.update(schema=True))
    change("unknown field", lambda x: x.update(unchecked=1))
    change("invalid Unicode", lambda x: x.update(name="\ud800"))
    source = json.dumps(base)
    bad.append(("duplicate JSON key", source.replace('"schema": 1', '"schema": 1, "schema": 1', 1)))
    bad.append(("non-finite JSON", source.replace('"schema": 1', '"schema": NaN', 1)))
    for label, source in bad:
        path = directory / "malformed.json"
        path.write_text(source)
        result = subprocess.run([sys.executable, str(HERE / "solve.py"), str(path)],
                                capture_output=True, timeout=30)
        need(result.returncode != 0 and not result.stdout, "Solver accepted malformed input: " + label)
        try:
            verify.decode(verify.read_json(path))
        except (verify.Rejected, ValueError):
            continue
        raise RuntimeError("Checker accepted malformed input: " + label)
    return len(bad)


def main() -> int:
    try:
        need(os.environ.get("HMA_BUILD_DIR") is not None,
             "Run proof/check.sh; this gate requires its isolated freshly compiled Lean modules")
        source = subprocess.run([sys.executable, str(HERE / "arena/check.py")],
                                text=True, capture_output=True, timeout=180)
        need(source.returncode == 0, source.stdout + source.stderr)
        print(source.stdout.rstrip(), flush=True)
        paths = sorted((HERE / "instances").glob("*.json"))
        need({path.stem for path in paths} == REQUIRED, "Validation fixture inventory changed; update its explicit required set")
        results = {}
        with tempfile.TemporaryDirectory(prefix="hma-validation-") as temporary:
            work = Path(temporary)
            for path in paths:
                first = run_solver(path, 1)
                second = run_solver(path, 2)
                need(first == second, f"Non-deterministic bytes for {path.stem}")
                output = work / (path.stem + ".json")
                output.write_bytes(first)
                actual = verify.read_json(output)
                control = path.stem if path.stem in {"X", "D", "E-empty", "E-singleton"} else None
                expected = verify.compute_expected(path, build_dir=os.environ["HMA_BUILD_DIR"], control=control)
                verify.compare_result(expected, actual)
                need(first == verify.canonical(actual).encode("utf-8"), "Noncanonical output bytes")
                recorded = HERE / "results" / path.name
                need(recorded.is_file() and recorded.read_bytes() == first,
                     f"Recorded output missing or stale: {recorded.relative_to(HERE.parent)}")
                reordered = work / "reordered.json"
                reordered.write_text(json.dumps(permute(verify.read_json(path))))
                need(run_solver(reordered, 3) == first, f"Declaration order changes result for {path.stem}")
                # Exercise the independent decoder's column and type handling too.
                if path.stem in {"X", "typed-weighted"}:
                    verify.compare_result(expected, verify.compute_expected(reordered, build_dir=os.environ["HMA_BUILD_DIR"], control=control))
                sha = hashlib.sha256(first).hexdigest()
                minimal = "; ".join(str(row["axes"]) + ":" + str(row["rho"]) for row in actual["minimal"])
                print(f"INSTANCE {path.stem}: PASS; subsets={actual['counts']['subsets']}; rows={actual['counts']['contract_rows']}; chosen={actual['chosen']['axes']}; rho={actual['chosen']['rho']}; minimal={minimal}", flush=True)
                print(f"  Lean definitions=AGREE; deterministic bytes=EXACT (2 processes); declaration order=INVARIANT; output sha256={sha}", flush=True)
                mode = "compiled Lean executable" if verify.uses_compiled_checker(actual["counts"]["axes"], actual["counts"]["contract_rows"]) else "Lean interpreter"
                print(f"  Checker execution={mode}; finite-instance runtime check", flush=True)
                if control:
                    print(f"  Original Controls.lean instance={control}: exact contract/behavior AGREEMENT", flush=True)
                results[path.stem] = expected
            mutations = rejection_controls(results["X"])
            # The same highest score with a later lexical choice must be rejected.
            wrong_tie = copy.deepcopy(results["tie"])
            wrong_tie["chosen"] = {"axes": ["c"], "rho": [1, 2]}
            try:
                verify.compare_result(results["tie"], wrong_tie)
            except verify.Rejected:
                mutations += 1
            else:
                raise RuntimeError("Checker accepted the wrong tie break")
            invalid = malformed_controls(verify.read_json(HERE / "instances/X.json"), work)
            print(f"REJECTION CONTROLS: PASS ({mutations} corrupted outputs; {invalid} malformed inputs rejected by both decoders)", flush=True)
        print(f"SOLVER GATE PASS: {len(paths)} instances; every subset checked against imported Lean definitions; recorded bytes current", flush=True)
        return 0
    except (RuntimeError, verify.Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        print("SOLVER GATE REJECTED: " + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
