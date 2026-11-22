#!/usr/bin/env python3
"""Fail-closed prefix, replay, compaction, and work-accounting validation.

An independent input replay builds each current Hma instance. The existing
independent decoder evaluates the imported Lean definitions on that instance;
no Python liveness oracle decides whether an outcome passes. A separate pair
enumeration checks work counters, which are measurements rather than proofs.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
from typing import Any

import incremental
import solve
import verify

HERE = Path(__file__).resolve().parent


def need(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def encoded(value: Any) -> bytes:
    return verify.canonical(value).encode("utf-8")


def sha(value: Any) -> str:
    return hashlib.sha256(encoded(value)).hexdigest()


def row_identity(row: dict) -> tuple[str, ...]:
    return tuple(verify.label(v) for v in row["axes"])


def current_input(source: dict) -> dict:
    """Independent named-column adapter; never read the materializer's state."""
    verify.decode(source)
    data = copy.deepcopy(source)
    ai = sorted(range(len(data["axes"])), key=lambda i: data["axes"][i]["name"])
    ci = sorted(range(len(data["components"])), key=data["components"].__getitem__)
    data["axes"] = [data["axes"][i] for i in ai]
    for axis in data["axes"]:
        axis["values"].sort(key=verify.label)
    data["components"] = [data["components"][i] for i in ci]
    data["contract"] = [{"axes": [r["axes"][i] for i in ai],
                         "behavior": [r["behavior"][i] for i in ci]}
                        for r in source["contract"]]
    data["contract"].sort(key=row_identity)
    data["hyperedges"] = sorted(({"components": sorted(e["components"]), "weight": e["weight"]}
                                 for e in data["hyperedges"]), key=lambda e: e["components"])
    return data


def reference_apply(data: dict, event: dict) -> dict:
    candidate = copy.deepcopy(data)
    op = event["op"]
    if op == "rebase":
        return current_input(event["instance"])
    if op == "edges":
        candidate["hyperedges"] = copy.deepcopy(event["hyperedges"])
    elif op == "append":
        candidate["contract"].extend(copy.deepcopy(event["rows"]))
    elif op == "remove":
        keys = {tuple(verify.label(v) for v in vector) for vector in event["axes"]}
        candidate["contract"] = [r for r in candidate["contract"] if row_identity(r) not in keys]
    elif op == "replace":
        rows = {row_identity(r): r for r in event["rows"]}
        candidate["contract"] = [copy.deepcopy(rows.get(row_identity(r), r))
                                 for r in candidate["contract"]]
    else:
        raise RuntimeError("unrecognized reference operation")
    return current_input(candidate)


def empty(source: dict) -> dict:
    source = copy.deepcopy(source)
    source["contract"] = []
    return source


def campaign(initial: dict, operations: list[dict]) -> dict:
    epoch = 0
    events = []
    for seq, op in enumerate(operations, 1):
        events.append({"seq": seq, "epoch": epoch, **copy.deepcopy(op)})
        epoch += int(op["op"] == "rebase")
    return {"schema": 1, "initial": initial, "events": events}


def exponential(groups: int) -> dict:
    axes = [{"name": f"a{i}{side}", "values": [0, 1]}
            for i in range(groups) for side in range(2)]
    components = [f"b{i}{side}" for i in range(groups) for side in range(2)]
    rows = [{"axes": [0] * (2 * groups), "behavior": [0] * (2 * groups)}]
    for axis in range(2 * groups):
        vector, behavior = [0] * (2 * groups), [0] * (2 * groups)
        vector[axis] = 1
        behavior[2 * (axis // 2)] = behavior[2 * (axis // 2) + 1] = 1
        rows.append({"axes": vector, "behavior": behavior})
    return {"schema": 1, "name": f"exponential-{groups}", "axes": axes,
            "components": components, "contract": rows,
            "hyperedges": [{"components": components[2 * i:2 * i + 2], "weight": 1}
                           for i in range(groups)]}


def campaigns() -> dict[str, dict]:
    cases = {}
    for name in ("X", "D", "E-empty", "E-singleton", "arena", "tie", "typed-weighted", "empty-universe"):
        fixture = current_input(verify.read_json(HERE / "instances" / (name + ".json")))
        rows = fixture["contract"]
        groups = ([rows[:1], rows[1:32], rows[32:]] if name == "arena" else [[r] for r in rows])
        operations = [{"op": "append", "rows": group} for group in groups if group]
        if rows:
            operations += [{"op": "remove", "axes": [rows[0]["axes"]]},
                           {"op": "append", "rows": [rows[0]]}]
        if name == "X":
            altered = copy.deepcopy(rows[1])
            altered["behavior"][0] = "changed-observation"
            operations += [{"op": "replace", "rows": [altered]},
                           {"op": "edges", "hyperedges": []},
                           {"op": "replace", "rows": [rows[1]]},
                           {"op": "edges", "hyperedges": fixture["hyperedges"]},
                           {"op": "edges", "hyperedges": [{"components": ["p", "q"], "weight": 7}]},
                           {"op": "edges", "hyperedges": fixture["hyperedges"]}]
        cases[name] = campaign(empty(fixture), operations)

    # Reordering the axis universe changes mask positions and must rebuild.
    fixture = current_input(verify.read_json(HERE / "instances/X.json"))
    extended = copy.deepcopy(fixture)
    extended["axes"].append({"name": "0-new-axis", "values": [False, True]})
    for row in extended["contract"]:
        row["axes"].append(False)
    extended = current_input(extended)
    row = copy.deepcopy(extended["contract"][0])
    row["axes"][0] = True
    row["behavior"][0] = "schema-extension"
    cases["schema-rebase"] = campaign(fixture, [
        {"op": "rebase", "instance": extended}, {"op": "append", "rows": [row]},
        {"op": "rebase", "instance": fixture}])

    # Deterministic mixed transactions, each prefix independently checked in Lean.
    rng = random.Random(1729)
    active = empty(fixture)
    operations = []
    for step in range(36):
        present = {row_identity(r) for r in active["contract"]}
        available = [r for r in fixture["contract"] if row_identity(r) not in present]
        op = rng.choice(("append", "remove", "replace", "edges"))
        if op == "append" and available:
            event = {"op": op, "rows": [copy.deepcopy(rng.choice(available))]}
        elif op == "remove" and present:
            event = {"op": op, "axes": [rng.choice(active["contract"])["axes"]]}
        elif op == "replace" and present:
            row = copy.deepcopy(rng.choice(active["contract"]))
            row["behavior"][rng.randrange(len(row["behavior"]))] = f"measurement-{step}"
            event = {"op": op, "rows": [row]}
        else:
            event = {"op": "edges", "hyperedges": ([] if step % 3 == 0 else
                     [{"components": ["p", "q"], "weight": 1 + step % 5}])}
        operations.append(event)
        active = reference_apply(active, event)
    cases["mixed-36"] = campaign(empty(fixture), operations)
    for groups in range(1, 5):
        fixture = exponential(groups)
        cases[fixture["name"]] = campaign(empty(fixture), [{"op": "append", "rows": fixture["contract"]}])
    return cases


def exact_counts(data: dict) -> dict[tuple[int, int], int]:
    """Independent diagnostic oracle; outcome truth comes only from Lean."""
    counts: dict[tuple[int, int], int] = {}
    rows = [(tuple(verify.label(v) for v in r["axes"]),
             tuple(verify.label(v) for v in r["behavior"])) for r in data["contract"]]
    for left, right in itertools.combinations(rows, 2):
        difference = sum(1 << i for i, (x, y) in enumerate(zip(left[0], right[0])) if x != y)
        for b, (x, y) in enumerate(zip(left[1], right[1])):
            if x != y:
                counts[(difference, b)] = counts.get((difference, b), 0) + 1
    return counts


def choose_two(n: int) -> int:
    return n * (n - 1) // 2


def expected_work(old: dict, new: dict, before: dict, after: dict,
                  prior: dict, current: dict, rebuild: bool) -> dict:
    axes = len(new["axes"])
    if rebuild:
        old = empty(new)
        before = {}
        prior = {"subsets": [{"live": []} for _ in range(1 << axes)]}
    old_rows = {row_identity(r): tuple(verify.label(v) for v in r["behavior"]) for r in old["contract"]}
    new_rows = {row_identity(r): tuple(verify.label(v) for v in r["behavior"]) for r in new["contract"]}
    unchanged = sum(key in new_rows and value == new_rows[key] for key, value in old_rows.items())
    removed = choose_two(len(old_rows)) - choose_two(unchanged)
    added = choose_two(len(new_rows)) - choose_two(unchanged)
    changed = [key for key in before.keys() | after.keys() if before.get(key, 0) != after.get(key, 0)]
    threshold = [key for key in changed if bool(before.get(key, 0)) != bool(after.get(key, 0))]
    return {"pair_evaluations": removed + added, "pair_additions": added, "pair_removals": removed,
            "exact_cells_changed": len(changed), "support_threshold_changes": len(threshold),
            "cone_visits": sum(1 << (axes - mask.bit_count()) for mask, _ in threshold),
            "live_cells_changed": sum(len(set(a["live"]) ^ set(b["live"]))
                                      for a, b in zip(prior["subsets"], current["subsets"])),
            "full_rebuilds": int(rebuild)}


def run_process(campaign_path: Path, seed: int) -> bytes:
    result = subprocess.run([sys.executable, str(HERE / "incremental.py"), str(campaign_path)],
                            env=dict(os.environ, PYTHONHASHSEED=str(seed)), capture_output=True, timeout=180)
    need(result.returncode == 0 and not result.stderr,
         "incremental process rejected campaign: " + result.stderr.decode(errors="replace"))
    return result.stdout


def controls(expected_for) -> dict:
    base = current_input(verify.read_json(HERE / "instances/X.json"))
    state = incremental.Incremental(base)
    checkpoint = state.checkpoint()
    observed = state.observe()
    diagnostic = state.diagnostics()
    row = copy.deepcopy(base["contract"][0])
    event = {"seq": 1, "epoch": 0, "op": "append", "rows": [row]}
    bad = [event,
           {"seq": 0, "epoch": 0, "op": "edges", "hyperedges": []},
           {"seq": 2, "epoch": 0, "op": "edges", "hyperedges": []},
           {"seq": True, "epoch": 0, "op": "edges", "hyperedges": []},
           {"seq": 1, "epoch": 1, "op": "edges", "hyperedges": []},
           {"seq": 1, "epoch": 0, "op": "remove", "axes": [row["axes"], row["axes"]]},
           {"seq": 1, "epoch": 0, "op": "remove", "axes": [["absent", False, False]]},
           {"seq": 1, "epoch": 0, "op": "replace", "rows": [{"axes": [], "behavior": []}]},
           {"seq": 1, "epoch": 0, "op": "edges", "hyperedges": [{"components": ["p", "q"], "weight": 0}]},
           {"seq": 1, "epoch": 0, "op": "rebase", "instance": {}},
           {"seq": 1, "epoch": 0, "op": "edges", "hyperedges": [], "unchecked": True}]
    for item in bad:
        try:
            state.apply(item)
        except (solve.InvalidInstance, ValueError):
            pass
        else:
            raise RuntimeError("invalid event was accepted")
        need(state.checkpoint() == checkpoint and state.observe() == observed and state.diagnostics() == diagnostic,
             "rejected event mutated state")
    leaked = state.observe()
    leaked["axes"].clear()
    leaked["full"]["engaged"][0]["components"].clear()
    need(state.observe() == observed, "caller mutated active state through output")

    corrupted = []
    for field, value in (("next_seq", 0), ("next_seq", True), ("epoch", 1), ("schema", 2)):
        cp = copy.deepcopy(checkpoint)
        cp[field] = value
        corrupted.append(cp)
    cp = copy.deepcopy(checkpoint)
    cp["events"] = []
    corrupted.append(cp)
    cp = copy.deepcopy(checkpoint)
    cp["cumulative"]["pair_evaluations"] += 1
    corrupted.append(cp)
    for cp in corrupted:
        try:
            incremental.Incremental.restore(cp)
        except (solve.InvalidInstance, ValueError):
            pass
        else:
            raise RuntimeError("malformed checkpoint accepted")

    # Current answer/liveness alone cannot determine the effect of a new row.
    example = exponential(1)
    no_rows = empty(example)
    one_row = copy.deepcopy(no_rows)
    one_row["contract"] = [example["contract"][0]]
    left, right = incremental.Incremental(no_rows), incremental.Incremental(one_row)
    need(left.observe()["subsets"] == right.observe()["subsets"], "future-information control malformed")
    event_row = example["contract"][1]
    left.append_rows([event_row])
    right.append_rows([event_row])
    need(left.observe()["full"] != right.observe()["full"], "answer-only compaction was not challenged")
    lone, pair = copy.deepcopy(no_rows), copy.deepcopy(one_row)
    lone["contract"].append(event_row)
    pair["contract"].append(event_row)
    verify.compare_result(expected_for(lone), left.observe())
    verify.compare_result(expected_for(pair), right.observe())

    # An already correct live bit with a corrupt redundant support becomes
    # wrong only after withdrawal: the gate must test subsequent outcomes.
    victim = incremental.Incremental(pair)
    key = next(iter(victim._exact))
    victim._exact[key] += 1
    verify.compare_result(expected_for(pair), victim.observe())
    victim.remove_rows([event_row["axes"]])
    try:
        verify.compare_result(expected_for(one_row), victim.observe())
    except verify.Rejected:
        pass
    else:
        raise RuntimeError("stale redundant support survived suffix validation")
    victim = incremental.Incremental(pair)
    victim._live[0] = 1
    try:
        verify.compare_result(expected_for(pair), victim.observe())
    except verify.Rejected:
        pass
    else:
        raise RuntimeError("corrupt live cache passed Lean outcome check")

    # Clock and epoch boundaries survive restoration; old transactions refuse.
    one_event = {"seq": 1, "epoch": 0, "op": "edges", "hyperedges": []}
    state.apply(one_event)
    restored = incremental.Incremental.restore(state.checkpoint())
    try:
        restored.apply(one_event)
    except solve.InvalidInstance:
        pass
    else:
        raise RuntimeError("pre-checkpoint event replay was accepted")
    return {"atomic_event_rejections": len(bad), "checkpoint_rejections": len(corrupted),
            "caller_mutation_isolated": True, "answer_only_checkpoint_counterexample": True,
            "stale_support_suffix_rejected": True, "corrupt_live_rejected": True,
            "pre_checkpoint_sequence_rejected": True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="record only after all checks pass")
    args = parser.parse_args()
    try:
        need(bool(os.environ.get("HMA_BUILD_DIR")), "requires freshly built modules from proof/check.sh")
        expected_cache = {}
        count_cache = {}

        def expected_for(data):
            key = sha(current_input(data))
            if key not in expected_cache:
                expected_cache[key] = verify.compute_expected(data, build_dir=os.environ["HMA_BUILD_DIR"])
            return expected_cache[key]

        def counts_for(data):
            key = sha(current_input(data))
            if key not in count_cache:
                count_cache[key] = exact_counts(data)
            return count_cache[key]

        report = {"schema": 1, "cases": {}, "controls": {}}
        with tempfile.TemporaryDirectory(prefix="hma-incremental-") as tmp:
            path = Path(tmp) / "campaign.json"
            for name, test in campaigns().items():
                path.write_bytes(encoded(test))
                first, second = run_process(path, 1), run_process(path, 2)
                need(first == second, name + ": process bytes differ")
                transcript = json.loads(first)
                need(first == encoded(transcript), name + ": noncanonical transcript")
                state = incremental.Incremental(test["initial"])
                active = current_input(test["initial"])
                outputs, checkpoints, summaries, observations = [], [], [], []
                expected_epoch = 0
                previous = empty(active)
                previous_expected = {"subsets": [{"live": []} for _ in range(1 << len(active["axes"]))]}
                cumulative = incremental.zero_counters()
                for index in range(len(test["events"]) + 1):
                    op = "initial" if index == 0 else test["events"][index - 1]["op"]
                    if index:
                        event = test["events"][index - 1]
                        state.apply(event)
                        active = reference_apply(active, event)
                        expected_epoch += int(op == "rebase")
                    expected = expected_for(active)
                    actual = state.observe()
                    verify.compare_result(expected, actual)
                    verify.compare_result(expected, transcript["observations"][index]["result"])
                    before = {} if index == 0 or op == "rebase" else counts_for(previous)
                    after = counts_for(active)
                    work = expected_work(previous, active, before, after, previous_expected, expected,
                                         index == 0 or op == "rebase")
                    diag = state.diagnostics()
                    need(set(diag) == {"next_seq", "epoch", "last", "cumulative", "reconstruction", "storage", "observation"},
                         "unexpected diagnostic fields")
                    need(encoded(diag["last"]) == encoded(work), f"{name}/{index}: incorrect delta work accounting")
                    for field in cumulative:
                        cumulative[field] += work[field]
                    need(encoded(diag["cumulative"]) == encoded(cumulative), f"{name}/{index}: noncumulative accounting")
                    n, m = len(active["axes"]), len(active["components"])
                    need(encoded(diag["storage"]) == encoded({
                        "active_rows": len(active["contract"]), "active_pairs": choose_two(len(active["contract"])),
                        "retained_pair_records": 0, "retained_events": 0, "exact_support_cells": len(after),
                        "subset_table_slots": 1 << n, "subset_support_cells": (1 << n) * m}),
                        f"{name}/{index}: retained storage accounting incorrect")
                    need(encoded(diag["reconstruction"]) == encoded(incremental.zero_counters()),
                         "non-restored state has reconstruction accounting")
                    need(encoded(diag["observation"]) == encoded({"subsets_rendered": 1 << n,
                         "edge_subset_checks": (1 << n) * len(active["hyperedges"]),
                         "minimal_neighbor_upper_bound": n * (1 << n) // 2}),
                         "observation work accounting changed")
                    need(type(diag["next_seq"]) is int and type(diag["epoch"]) is int and
                         diag["next_seq"] == index + 1 and diag["epoch"] == expected_epoch,
                         f"{name}/{index}: replay boundary changed")
                    cp = state.checkpoint()
                    need(encoded(current_input(cp["instance"])) == encoded(current_input(active)),
                         f"{name}/{index}: checkpoint lost future-relevant input")
                    need(cp["next_seq"] == index + 1 and cp["epoch"] == expected_epoch and
                         cp["cumulative"] == cumulative, "checkpoint clock/accounting mismatch")
                    observations.append({"next_seq": 1, "epoch": 0, "result": actual} if index == 0 else
                        {"receipt": {"seq": index, "op": op, "epoch": expected_epoch,
                                     "next_seq": index + 1, "work": work, "cumulative": dict(cumulative)},
                         "result": actual})
                    need(set(cp) == {"schema", "kind", "next_seq", "epoch", "instance", "cumulative"},
                         "checkpoint retained history or cache fields")
                    checkpoints.append(cp)
                    outputs.append(actual)
                    summaries.append({"prefix": index, "operation": op, "rows": len(active["contract"]),
                                      "chosen": actual["chosen"], "minimal_count": len(actual["minimal"]),
                                      "output_sha256": sha(actual), "work": work})
                    if name == "arena":
                        print(f"  ARENA PREFIX {index}: Lean=AGREE; rows={len(active['contract'])}; "
                              f"pairs this update={work['pair_evaluations']}; chosen={actual['chosen']['axes']}", flush=True)
                    previous, previous_expected = active, expected
                expected_transcript = {"schema": 1, "observations": observations,
                                       "checkpoint": state.checkpoint(), "diagnostics": state.diagnostics()}
                need(first == encoded(expected_transcript), "complete process transcript mismatch")
                # Every suffix of each tested transaction prefix, not just the final state.
                for start, cp in enumerate(checkpoints):
                    resumed = incremental.Incremental.restore(cp)
                    verify.compare_result(outputs[start], resumed.observe())
                    recovered_input = current_input(cp["instance"])
                    recovery_work = expected_work(empty(recovered_input), recovered_input, {},
                        counts_for(recovered_input), {}, outputs[start], True)
                    need(encoded(resumed.diagnostics()["reconstruction"]) == encoded(recovery_work),
                         "checkpoint reconstruction work was not reported exactly")
                    need(encoded(resumed.checkpoint()) == encoded(cp), "checkpoint roundtrip changed bytes")
                    for i in range(start, len(test["events"])):
                        resumed.apply(test["events"][i])
                        verify.compare_result(outputs[i + 1], resumed.observe())
                    need(encoded(resumed.checkpoint()) == encoded(checkpoints[-1]), "resumed suffix checkpoint differs")
                    path.write_bytes(encoded({"schema": 1, "initial": cp, "events": test["events"][start:]}))
                    resume_first, resume_second = run_process(path, 1), run_process(path, 2)
                    need(resume_first == resume_second, "restored suffix process bytes differ")
                    suffix_observations = [{"next_seq": cp["next_seq"], "epoch": cp["epoch"],
                                            "result": outputs[start]}, *observations[start + 1:]]
                    suffix_diagnostics = copy.deepcopy(state.diagnostics())
                    suffix_diagnostics["reconstruction"] = recovery_work
                    if start == len(test["events"]):
                        suffix_diagnostics["last"] = incremental.zero_counters()
                    need(encoded(resumed.diagnostics()) == encoded(suffix_diagnostics),
                         "restored suffix diagnostic mismatch")
                    suffix_expected = {"schema": 1, "observations": suffix_observations,
                                       "checkpoint": checkpoints[-1], "diagnostics": suffix_diagnostics}
                    need(resume_first == encoded(suffix_expected), "restored suffix complete transcript mismatch")
                if name.startswith("exponential-"):
                    k = int(name.split("-")[1])
                    final = outputs[-1]
                    need(len(final["minimal"]) == 1 << k and final["counts"]["subsets"] == 1 << (2 * k),
                         "exponential complete-list control failed")
                    choices = {tuple(f"a{i}{side}" for i, side in enumerate(bits))
                               for bits in itertools.product(range(2), repeat=k)}
                    need({tuple(v["axes"]) for v in final["minimal"]} == choices,
                         "exponential control has wrong minimal vectors")
                    need(all(v["rho"] == [k, 2 * k] for v in final["minimal"]), "wrong exponential rho")
                report["cases"][name] = {"prefixes": summaries, "checkpoint_suffixes": len(checkpoints),
                                        "transcript_sha256": hashlib.sha256(first).hexdigest(),
                                        "two_process_bytes": "EXACT", "last_diagnostics": state.diagnostics()}
                print(f"INCREMENTAL {name}: PASS; prefixes={len(outputs)}; all Lean outcomes=AGREE; "
                      f"checkpoint suffixes={len(checkpoints)}; process bytes=EXACT; "
                      f"cumulative pairs={cumulative['pair_evaluations']}; retained events=0", flush=True)
        report["controls"] = controls(expected_for)
        cone_cases = 0
        for n in range(8):
            for mask in range(1 << n):
                cone = list(incremental.supersets(mask, n))
                need(len(cone) == len(set(cone)) == 1 << (n - mask.bit_count()), "cone count failed")
                need(set(cone) == {s for s in range(1 << n) if mask & s == mask}, "cone coverage failed")
                cone_cases += 1
        report["controls"]["exact_cone_cases"] = cone_cases
        report["lean_instances_evaluated"] = len(expected_cache)
        report["checked_prefixes"] = sum(len(case["prefixes"]) for case in report["cases"].values())
        recorded = HERE / "results/incremental.json"
        if args.record:
            recorded.write_bytes(encoded(report))
        need(recorded.is_file() and recorded.read_bytes() == encoded(report), "incremental receipt absent or stale")
        print(f"INCREMENTAL GATE PASS: {len(report['cases'])} campaigns; {report['checked_prefixes']} prefixes; "
              f"{len(expected_cache)} distinct Lean inputs; reconstruction/suffix replay, rejected transactions, "
              "stale-support attacks, exact delta counts and exponential controls PASS", flush=True)
        return 0
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print("INCREMENTAL REJECTED: " + str(error), file=sys.stderr, flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
