#!/usr/bin/env python3
"""Check every carried multiplicity and output against the proved Lean engine."""
from __future__ import annotations

import argparse
import copy
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

import certified
import incremental
import incremental_check
import verify

HERE = Path(__file__).resolve().parent


def digest(value) -> str:
    return hashlib.sha256(verify.canonical(value).encode()).hexdigest()


def scalar_key(value):
    """Independent typed key for inspecting the Python cache's dictionary."""
    verify.label(value)
    if value is None:
        return (0, 0)
    if type(value) is bool:
        return (1, 1 if value else 0)
    if type(value) is int:
        return (2, value)
    return (3, value)


def check_cells(state: incremental.Incremental, receipt: dict, expected_input: dict) -> None:
    actual = [[mask, b, count] for (mask, b), count in sorted(state._exact.items())]
    verify.need(verify.canonical(actual) == verify.canonical(receipt["cells"]),
                "Python carried witness multiplicities disagree with certified Lean state")
    verify.need(verify.canonical(state._support) == verify.canonical(receipt["support"]),
                "Python carried occupancy multiplicities disagree with certified Lean state")
    expected_live = [sum(1 << b for b, count in enumerate(row) if count > 0)
                     for row in receipt["support"]]
    verify.need(verify.canonical(state._live) == verify.canonical(expected_live),
                "Python live cache disagrees with certified Lean occupancy")
    expected = certified.normalized(expected_input)
    verify.need([axis["name"] for axis in state._data["axes"]] ==
                [axis["name"] for axis in expected["axes"]] and
                state._data["components"] == expected["components"],
                "Python active columns disagree with independently replayed input")
    verify.need(verify.canonical(certified.normalized(state._data)) == verify.canonical(expected),
                "Python active input disagrees with independently replayed input")
    expected_rows = {verify.canonical(tuple(scalar_key(v) for v in row["axes"])): row
                     for row in expected["contract"]}
    verify.need(type(state._rows) is dict, "Python row cache is not a mapping")
    actual_rows = {}
    for key, row in state._rows.items():
        verify.need(type(key) is tuple and all(type(part) is tuple and len(part) == 2 for part in key),
                    "Python row cache has a malformed typed key")
        actual_rows[verify.canonical(key)] = row
    verify.need(verify.canonical(actual_rows) == verify.canonical(expected_rows),
                "Python cached row identities or observations disagree with independently replayed input")


def controls(executor: certified.Executor) -> dict:
    # Present liveness can agree while a positive support count is incorrect.
    fixture = incremental_check.exponential(1)
    test = {"schema": 1, "initial": fixture, "events": []}
    receipts, _ = executor.execute(test)
    state = incremental.Incremental(fixture)
    verify.compare_result(receipts[0]["result"], state.observe())
    cell = next(iter(state._exact))
    state._exact[cell] += 1
    verify.compare_result(receipts[0]["result"], state.observe())
    try:
        check_cells(state, receipts[0], fixture)
    except verify.Rejected:
        pass
    else:
        raise RuntimeError("hidden multiplicity corruption passed immediate certification")
    state = incremental.Incremental(fixture)
    support_cell = next((mask, b) for mask, row in enumerate(state._support)
                        for b, count in enumerate(row) if count > 0)
    state._support[support_cell[0]][support_cell[1]] += 1
    verify.compare_result(receipts[0]["result"], state.observe())
    try:
        check_cells(state, receipts[0], fixture)
    except verify.Rejected:
        pass
    else:
        raise RuntimeError("hidden occupancy corruption passed immediate certification")
    state = incremental.Incremental(fixture)
    state._rows.pop(next(iter(state._rows)))
    verify.compare_result(receipts[0]["result"], state.observe())
    try:
        check_cells(state, receipts[0], fixture)
    except verify.Rejected:
        pass
    else:
        raise RuntimeError("hidden active-row corruption passed immediate certification")
    state = incremental.Incremental(fixture)
    state._data["contract"][0]["behavior"][0] = "corrupted input observation"
    verify.compare_result(receipts[0]["result"], state.observe())
    try:
        check_cells(state, receipts[0], fixture)
    except verify.Rejected:
        pass
    else:
        raise RuntimeError("hidden active-input corruption passed immediate certification")
    attacks = []
    for field, value in (("seq", 0), ("seq", True), ("seq", 2), ("epoch", 1)):
        event = {"seq": 1, "epoch": 0, "op": "edges", "hyperedges": []}
        event[field] = value
        attacks.append({"schema": 1, "initial": fixture, "events": [event]})
    attacks += [{"schema": 1, "initial": fixture, "events": [event]} for event in (
        {"seq": 1, "epoch": 0, "op": "append", "rows": [fixture["contract"][0]]},
        {"seq": 1, "epoch": 0, "op": "remove", "axes": [[1, 1]]},
        {"seq": 1, "epoch": 0, "op": "replace", "rows": [{"axes": [1, 1], "behavior": [0, 0]}]},
        {"seq": 1, "epoch": 0, "op": "edges", "hyperedges": [], "unchecked": 1})]
    for attack in attacks:
        try:
            certified.inputs(attack)
        except verify.Rejected:
            pass
        else:
            raise RuntimeError("malformed certified input was accepted")
    changed = copy.deepcopy(receipts[0]["result"])
    changed["minimal"] = []
    try:
        verify.compare_result(receipts[0]["result"], changed)
    except verify.Rejected:
        pass
    else:
        raise RuntimeError("missing minimal results were accepted")
    return {"latent_support_corruption_rejected_immediately": True,
            "latent_occupancy_corruption_rejected_immediately": True,
            "hidden_rows_corruption_rejected_immediately": True,
            "hidden_input_corruption_rejected_immediately": True,
            "invalid_inputs_rejected": len(attacks), "incomplete_output_rejected": True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    try:
        verify.need(bool(os.environ.get("HMA_BUILD_DIR")), "requires cold-built Lean modules")
        report = {"schema": 1, "engine": "HmaExecutable materialized HashMap + HmaReplay + HmaCertified",
                  "cases": {}, "controls": {}}
        with tempfile.TemporaryDirectory(prefix="hma-certified-gate-") as temporary:
            executor = certified.Executor(Path(os.environ["HMA_BUILD_DIR"]),
                                          os.environ.get("LEAN", "lean"), Path(temporary))
            for name, campaign in incremental_check.campaigns().items():
                receipts, execution = executor.execute(campaign)
                expected_inputs = certified.inputs(campaign)
                state = incremental.Incremental(campaign["initial"])
                summaries = []
                total_pairs = 0
                for i, receipt in enumerate(receipts):
                    if i:
                        state.apply(campaign["events"][i - 1])
                    verify.compare_result(receipt["result"], state.observe())
                    check_cells(state, receipt, expected_inputs[i])
                    work = state.diagnostics()["last"]
                    verify.need(receipt["pair_additions"] == work["pair_additions"] and
                                receipt["pair_removals"] == work["pair_removals"],
                                f"{name}/{i}: actual Lean incident-pair loop count disagrees")
                    verify.need(receipt["epoch"] == state.epoch and receipt["next_seq"] == state.next_seq,
                                "certified replay clock mismatch")
                    total_pairs += receipt["pair_additions"] + receipt["pair_removals"]
                    summaries.append({"prefix": i, "rows": receipt["result"]["counts"]["contract_rows"],
                        "chosen": receipt["result"]["chosen"],
                        "minimal_count": len(receipt["result"]["minimal"]),
                        "materialized_cells": len(receipt["cells"]),
                        "pair_additions": receipt["pair_additions"], "pair_removals": receipt["pair_removals"],
                        "cumulative_pairs": total_pairs, "cell_sha256": digest(receipt["cells"]),
                        "support_sha256": digest(receipt["support"]),
                        "input_sha256": digest(expected_inputs[i]),
                        "output_sha256": digest(receipt["result"])})
                restoration = None
                if name in {"X", "arena", "schema-rebase", "mixed-36"}:
                    boundary = max(0, len(receipts) - 3)
                    rebuilt, reconstruction_execution = executor.execute(campaign, reconstruct_at=boundary)
                    verify.need(verify.canonical(rebuilt) == verify.canonical(receipts),
                                "materialized checkpoint reconstruction changed suffix outcomes or counts")
                    restoration = {"prefix": boundary, "future_prefixes": len(receipts) - boundary - 1,
                                   "execution": reconstruction_execution}
                report["cases"][name] = {"execution": execution, "prefixes": summaries,
                                          "reconstruction": restoration}
                print(f"CERTIFIED {name}: {len(receipts)} prefixes; materialized counts=EXACT; "
                      f"complete outputs=EXACT; actual incident pairs={total_pairs}; byte-exact=PASS", flush=True)
            report["controls"] = controls(executor)
        report["total_prefixes"] = sum(len(case["prefixes"]) for case in report["cases"].values())
        path = HERE / "results/certified.json"
        if args.record:
            path.write_text(verify.canonical(report), encoding="utf-8")
        else:
            verify.need(path.is_file() and path.read_text() == verify.canonical(report),
                        "recorded certified results disagree with fresh execution")
        print(f"CERTIFIED GATE PASS: {len(report['cases'])} campaigns; {report['total_prefixes']} prefixes; "
              "proved materialized transitions and renderer executed; no fresh full-pair search at an update; "
              "exact/occupancy multiplicities, live cache and active rows checked; latent corruption rejected immediately", flush=True)
        return 0
    except (RuntimeError, verify.Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        print("CERTIFIED GATE REJECTED: " + str(error), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
