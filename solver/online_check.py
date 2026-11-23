#!/usr/bin/env python3
"""Persistent online execution, typed boundary attacks, and suffix reconstruction."""
from __future__ import annotations

import argparse
import copy
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

import certified
import certified_check
import incremental
import incremental_check
import online
import verify

HERE = Path(__file__).resolve().parent


def native_session(binary: Path) -> online.Native:
    shared = os.environ.get("HMA_REASONING_BINARY")
    lane = ["hma"] if shared and binary.resolve() == Path(shared).resolve() else []
    return online.Native(binary, args=lane)


def digest(value) -> str:
    return hashlib.sha256(verify.canonical(value).encode()).hexdigest()


def execute(binary: Path, campaign: dict, rebuild_at: int | None = None) -> tuple[list[dict], list[bytes]]:
    receipts, raw = [], []
    with native_session(binary) as native:
        session = online.Session(native)
        receipts.append(session.apply({"op": "start", "instance": campaign["initial"]}))
        raw.append(native.last_line)
        for i, event in enumerate(campaign["events"], 1):
            if rebuild_at == i - 1:
                before = receipts[-1]
                checkpoint = session.apply({"op": "checkpoint", "seq": session.next_seq,
                                            "epoch": session.epoch})
                verify.need(verify.canonical(before["result"]) == verify.canonical(checkpoint["result"]) and
                            before["cells"] == checkpoint["cells"] and before["support"] == checkpoint["support"],
                            "online checkpoint reconstruction changed current state")
                count = len(session.current["contract"])
                verify.need(checkpoint["pair_additions"] == count * (count - 1) // 2,
                            "checkpoint reconstruction work hidden")
            receipts.append(session.apply(event))
            raw.append(native.last_line)
    return receipts, raw


def controls(binary: Path) -> dict:
    fixture = verify.read_json(HERE / "instances/typed-weighted.json")
    public, native_attacks = 0, 0
    with native_session(binary) as native:
        session = online.Session(native)
        baseline = session.apply({"op": "start", "instance": fixture})
        before_input = verify.canonical(session.current)
        for field, value in (("seq", 0), ("seq", True), ("seq", 2), ("epoch", 1), ("epoch", False)):
            attack = {"op": "edges", "seq": 1, "epoch": 0, "hyperedges": []}
            attack[field] = value
            count = native.response_count
            try:
                session.apply(attack)
            except verify.Rejected:
                public += 1
            else:
                raise RuntimeError("public stale clock accepted")
            verify.need(native.response_count == count and verify.canonical(session.current) == before_input,
                        "rejected public transaction altered current state")
        for line in ('{"op":"inspect","op":"checkpoint","seq":1,"epoch":0}',
                     '{"op":"inspect","seq":1.0,"epoch":0}',
                     '{"op":"inspect","seq":NaN,"epoch":0}'):
            try:
                online.load_line(line)
            except verify.Rejected:
                public += 1
            else:
                raise RuntimeError("ambiguous public JSON accepted")
        good = {"op": "advance", "seq": 1, "epoch": 0, "input": online.encode(session.current)}
        attacks = []
        for field, value in (("seq", 0), ("seq", True), ("epoch", 9), ("op", "unknown")):
            attack = copy.deepcopy(good)
            attack[field] = value
            attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["scope"] += "changed"
        attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["rows"][0][0].pop()
        attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["rows"].append(copy.deepcopy(attack["input"]["rows"][0]))
        attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["rows"][0][0][0] = False
        attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["rows"][0][0][0] = "not-in-declared-domain"
        attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["domains"][0].append("new-value-without-rebase")
        attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["edges"] = [[[0, 1], 0]]
        attacks.append(attack)
        attack = copy.deepcopy(good)
        attack["input"]["edges"] = [[[1, 0], 1]]
        attacks.append(attack)
        attacks.append({"op": "start", "input": good["input"]})
        for attack in attacks:
            reply = native.exchange(attack)
            verify.need(not reply["ok"], "malformed native transaction accepted")
            native_attacks += 1
            inspection = session.apply({"op": "inspect", "seq": 1, "epoch": 0})
            verify.need(inspection["result"] == baseline["result"] and inspection["cells"] == baseline["cells"] and
                        inspection["support"] == baseline["support"], "native refusal altered carried state")
        # The next accepted input is constructed only after inspecting the previous result.
        chosen = baseline["result"]["chosen"]["axes"]
        row = next(r for r in session.current["contract"] if r["axes"])
        removed = session.apply({"op": "remove", "seq": 1, "epoch": 0, "axes": [row["axes"]]})
        verify.need(bool(chosen) and removed["pair_removals"] == len(fixture["contract"]) - 1,
                    "response-dependent online action failed")
        restored = session.apply({"op": "append", "seq": 2, "epoch": 0, "rows": [row]})
        verify.need(restored["result"] == baseline["result"], "valid retry failed after refused inputs")
    # Empty and singleton hyperedges may lawfully carry zero weight.
    edge_case = copy.deepcopy(fixture)
    edge_case["hyperedges"] = [{"components": [], "weight": 0},
                              {"components": [fixture["components"][0]], "weight": 0}]
    with native_session(binary) as native:
        state = online.Session(native)
        output = state.apply({"op": "start", "instance": edge_case})
        verify.compare_result(output["result"], incremental.Incremental(edge_case).observe())
    return {"public_refusals": public, "native_refusals": native_attacks,
            "refusals_atomic": True, "valid_retry": True, "response_dependent_next_input": True,
            "zero_noninteracting_weights": True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--binary", type=Path)
    args = parser.parse_args()
    try:
        report = {"schema": 1, "mode": "persistent-compiled-once-online", "cases": {}, "controls": {}}
        with tempfile.TemporaryDirectory(prefix="hma-online-gate-") as temp:
            if args.binary or os.environ.get("HMA_REASONING_BINARY"):
                binary = args.binary or Path(os.environ["HMA_REASONING_BINARY"])
            else:
                verify.need(bool(os.environ.get("HMA_BUILD_DIR")), "requires cold-built Lean modules")
                binary = online.build_binary(Path(os.environ["HMA_BUILD_DIR"]),
                    os.environ.get("LEAN", "lean"), Path(temp))
            prior = verify.read_json(HERE / "results/certified.json")
            for name, campaign in incremental_check.campaigns().items():
                first, raw1 = execute(binary, campaign)
                second, raw2 = execute(binary, campaign)
                verify.need(raw1 == raw2, name + ": online raw bytes differ between fresh processes")
                verify.need(verify.canonical(first) == verify.canonical(second), "online decoded records differ")
                inputs = certified.inputs(campaign)
                state = incremental.Incremental(campaign["initial"])
                summaries = []
                for i, receipt in enumerate(first):
                    if i:
                        state.apply(campaign["events"][i - 1])
                    verify.compare_result(receipt["result"], state.observe())
                    certified_check.check_cells(state, receipt, inputs[i])
                    work = state.diagnostics()["last"]
                    verify.need(receipt["pair_additions"] == work["pair_additions"] and
                                receipt["pair_removals"] == work["pair_removals"], "online pair work mismatch")
                    expected = prior["cases"][name]["prefixes"][i]
                    verify.need(digest(receipt["result"]) == expected["output_sha256"] and
                                digest(receipt["cells"]) == expected["cell_sha256"] and
                                digest(receipt["support"]) == expected["support_sha256"],
                                "online state disagrees with original-definition campaign receipt")
                    summaries.append({"prefix": i, "rows": len(inputs[i]["contract"]),
                        "next_seq": receipt["next_seq"], "epoch": receipt["epoch"],
                        "pair_additions": receipt["pair_additions"], "pair_removals": receipt["pair_removals"],
                        "output_sha256": digest(receipt["result"]), "cell_sha256": digest(receipt["cells"]),
                        "support_sha256": digest(receipt["support"])})
                reconstruction = None
                if name in {"X", "arena", "schema-rebase", "mixed-36"}:
                    prefix = max(0, len(first) - 3)
                    rebuilt, raw = execute(binary, campaign, prefix)
                    verify.need(raw == raw1 and verify.canonical(rebuilt) == verify.canonical(first),
                                "online checkpoint changed future raw receipts")
                    reconstruction = {"prefix": prefix, "future_prefixes": len(first) - prefix - 1,
                                      "raw_suffix_bytes": "EXACT"}
                report["cases"][name] = {"prefixes": summaries, "byte_exact": True,
                    "execution_sha256": hashlib.sha256(b"".join(raw1)).hexdigest(),
                    "reconstruction": reconstruction}
                print(f"ONLINE {name}: {len(first)} prefixes; one fixed process; current counts/output=EXACT; raw bytes=EXACT",
                      flush=True)
            report["controls"] = controls(binary)
        report["total_prefixes"] = sum(len(v["prefixes"]) for v in report["cases"].values())
        path = HERE / "results/online.json"
        if args.record:
            path.write_text(verify.canonical(report), encoding="utf-8")
        else:
            verify.need(path.is_file() and path.read_text() == verify.canonical(report),
                        "recorded online results disagree with fresh execution")
        print(f"ONLINE GATE PASS: {len(report['cases'])} campaigns; {report['total_prefixes']} prefixes; "
              "compiled once, no future inputs, one native session per campaign; exact state/output; "
              "raw determinism, transactional refusal and checkpoint suffixes PASS", flush=True)
        return 0
    except (RuntimeError, verify.Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        print("ONLINE GATE REJECTED: " + str(error), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
