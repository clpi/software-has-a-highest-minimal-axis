#!/usr/bin/env python3
"""Execute globally optimized finite qualification schedules against live HMA.

The policy chooses each next batch; the harness executes it, checks measured
pair work and the complete HMA outcome, and only then admits the outcome into
the policy session. Batch-square charge is an explicit tariff, not measured
CPU time. Optimality is relative to the full declared three-step action model.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import itertools
import os
from pathlib import Path
import subprocess

import certified
import certified_check
import incremental
import online
import verify

HERE = Path(__file__).resolve().parent
HORIZON = 3


def digest(value) -> str:
    return hashlib.sha256(verify.canonical(value).encode()).hexdigest()


def state_id(rows: int, budget: int) -> int:
    return rows * (HORIZON + 1) + budget


def model_for(total: int) -> dict:
    states = []
    for rows in range(total + 1):
        for budget in range(HORIZON + 1):
            remaining = total - rows
            admitted = [0] if not remaining or not budget else (
                [remaining] if budget == 1 else list(range(1, remaining + 1)))
            actions = []
            for action in admitted:
                batch = action
                costs = [rows * batch + batch * (batch - 1) // 2, int(batch > 0), batch * batch]
                actions.append({"id": action, "outcomes": [{"id": 0,
                    "next": state_id(rows + batch, max(0, budget - 1)), "costs": costs}]})
            states.append({"terminal": [0, 0, 0], "actions": actions})
    return {"actions": total + 1, "outcomes": 1, "dimensions": 3, "states": states}


def branch(model: dict, state: int, action: int) -> dict | None:
    found = next((item for item in model["states"][state]["actions"] if item["id"] == action), None)
    return None if found is None else found["outcomes"][0]


def enumerate_schedules(model: dict, start: int, horizon: int) -> dict[int, dict]:
    """Independent exhaustive schedules, including every action at every step."""
    legal = {}
    for identity, actions in enumerate(itertools.product(range(model["actions"]), repeat=horizon)):
        state, profile = start, [0, 0, 0]
        for action in actions:
            edge = branch(model, state, action)
            if edge is None:
                break
            profile = [x + y for x, y in zip(profile, edge["costs"])]
            state = edge["next"]
        else:
            profile = [x + y for x, y in zip(profile, model["states"][state]["terminal"])]
            legal[identity] = {"profile": profile, "actions": list(actions), "final_state": state}
    return legal


def dominates(left: list[int], right: list[int]) -> bool:
    return all(x <= y for x, y in zip(left, right)) and any(x < y for x, y in zip(left, right))


def policy_actions(policy: dict | None, horizon: int) -> list[int]:
    if horizon == 0:
        verify.need(policy is None, "nonempty terminal policy")
        return []
    verify.obj(policy, {"action", "after"}, "selected policy node")
    verify.need(type(policy["action"]) is int and type(policy["after"]) is list and len(policy["after"]) == 1,
                "malformed finite selected policy")
    return [policy["action"], *policy_actions(policy["after"][0], horizon - 1)]


def check_decision(observation: dict, model: dict, total: int, weights: list[int],
                   initial: bool = False) -> dict:
    horizon, state = observation["remaining"], observation["state"]
    verify.need(type(horizon) is int and type(state) is int and 0 <= horizon <= HORIZON and
                0 <= state < len(model["states"]), "invalid policy state")
    legal = enumerate_schedules(model, state, horizon)
    verify.need(bool(legal), "qualification model has no admitted schedule")
    # Every admissible schedule from the actual current budget completes the corpus.
    verify.need(all(entry["final_state"] // (HORIZON + 1) == total for entry in legal.values()),
                "admitted schedule can stop before full qualification")
    for field in ("initial_bound", "budget", "spent"):
        verify.need(type(observation[field]) is list and len(observation[field]) == 3 and
                    all(type(value) is int and value >= 0 for value in observation[field]),
                    "malformed committed component bound")
    budget = observation["budget"]
    verify.need([x + y for x, y in zip(observation["spent"], budget)] == observation["initial_bound"],
                "residual budget lost its original commitment")
    unrestricted = [{"id": identity, "profile": record["profile"]} for identity, record in legal.items()]
    expected = [point for point in unrestricted if all(x <= y for x, y in zip(point["profile"], budget))]
    verify.need(bool(expected), "no continuation fits the committed component bound")
    verify.need(verify.canonical(observation["catalogue"]) == verify.canonical(expected),
                "policy catalogue omits or changes a budget-feasible admitted schedule")
    all_records = observation["policies"]
    verify.need(len(all_records) == model["actions"] ** horizon and
                all(type(r["id"]) is int for r in all_records) and
                [r["id"] for r in all_records] == list(range(model["actions"] ** horizon)),
                "policy universe was truncated")
    verify.need(all(type(r["admitted"]) is bool and r["admitted"] == (r["id"] in legal)
                    for r in all_records), "policy admission flags disagree")
    frontier = [p for p in expected if not any(dominates(q["profile"], p["profile"]) for q in expected)]
    verify.need(verify.canonical(observation["frontier"]) == verify.canonical(frontier),
                "policy frontier is not the complete exact frontier")
    selected = observation["selected"]
    verify.need(any(verify.canonical(selected) == verify.canonical(point) for point in frontier),
                "selected policy is dominated, malformed, or absent")
    score = lambda p: sum(w * c for w, c in zip(weights, p["profile"]))
    verify.need(type(observation["weighted_cost"]) is int and
                observation["weighted_cost"] == score(selected) == min(map(score, expected)),
                "selected schedule is not globally weighted-optimal")
    unrestricted_best = min(map(score, unrestricted))
    if initial:
        verify.need(score(selected) == unrestricted_best and selected["profile"] == observation["initial_bound"],
                    "initial commitment was not optimized over the entire unrestricted policy universe")
    verify.need(all(x + y <= z for x, y, z in
                    zip(observation["spent"], selected["profile"], observation["initial_bound"])),
                "selected continuation can violate an already committed component bound")
    chosen = legal[selected["id"]]
    verify.need(policy_actions(observation["policy"], horizon) == chosen["actions"] and
                observation["action"] == (chosen["actions"][0] if horizon else None),
                "executed first action differs from the certified selected policy")
    verify.need(verify.canonical(observation["weights"]) == verify.canonical(weights),
                "policy parameter mismatch")
    unrestricted_frontier = [p for p in unrestricted if not any(
        dominates(q["profile"], p["profile"]) for q in unrestricted)]
    verify.need(any(verify.canonical(selected) == verify.canonical(point) for point in unrestricted_frontier),
                "budget-feasible selected policy lost global Pareto nondominance")
    return {"admitted_schedules": len(legal), "all_schedules": model["actions"] ** horizon,
            "feasible_schedules": len(expected), "initial_bound": observation["initial_bound"],
            "budget": budget, "frontier": frontier, "unrestricted_frontier": unrestricted_frontier,
            "selected": selected, "weighted_cost": observation["weighted_cost"],
            "globally_pareto_nondominated": True,
            "unrestricted_weighted_cost": unrestricted_best,
            "commitment_restricts_preference": unrestricted_best < score(selected)}


def verify_measured(receipt: dict, before: int, count: int, predicted: list[int]) -> list[int]:
    verify.need(type(receipt["pair_additions"]) is int and type(receipt["pair_removals"]) is int,
                "malformed measured pair count")
    measured = [receipt["pair_additions"], int(count > 0), count * count]
    verify.need(receipt["pair_removals"] == 0 and
                receipt["result"]["counts"]["contract_rows"] == before + count and
                measured == predicted, "empirical qualification outcome contradicts selected model branch")
    return measured


def request(native: online.Native, command: dict, transcript: list[bytes], tag: bytes) -> dict:
    reply = native.exchange(command)
    transcript.extend([tag + b"\n", native.last_line])
    verify.need(reply["ok"], "autonomous lane refused: " + reply.get("error", ""))
    return reply["observation"]


def run_case(binary: Path, fixture: dict, initial_weights: list[int],
             change_after: int | None, changed_weights: list[int] | None,
             expected_cache: dict[str, dict]) -> tuple[dict, bytes]:
    table = certified.normalized(fixture)
    total = len(table["contract"])
    model = model_for(total)
    empty = copy.deepcopy(table)
    empty["contract"] = []
    transcript: list[bytes] = []
    weights = list(initial_weights)
    summaries, parameter_events = [], []
    with online.Native(binary, args=["hma"]) as native_hma, online.Native(binary, args=["policy"]) as native_policy:
        hma = online.Session(native_hma)
        initial = hma.apply({"op": "start", "instance": empty})
        transcript.extend([b"hma\n", native_hma.last_line])
        initial_key = digest(hma.current)
        if initial_key not in expected_cache:
            expected_cache[initial_key] = verify.compute_expected(hma.current)
        verify.compare_result(expected_cache[initial_key], initial["result"])
        certified_check.check_cells(incremental.Incremental(hma.current), initial, hma.current)
        observation = request(native_policy, {"op": "start", "model": model, "weights": weights,
            "horizon": HORIZON, "state": state_id(0, HORIZON)}, transcript, b"policy")
        rows, total_work, spent = 0, 0, [0, 0, 0]
        for step in range(HORIZON):
            if change_after == step:
                verify.need(changed_weights is not None, "missing changed parameter vector")
                weights = list(changed_weights)
                observation = request(native_policy, {"op": "parameters", "seq": observation["next_seq"],
                    "epoch": observation["epoch"], "weights": weights}, transcript, b"policy")
                verify.need(observation["profiles_needed"] == 0 and observation["comparisons_needed"] == 0,
                            "weight-only update recomputed policy evidence")
                parameter_events.append({"after_decisions": step, "weights": weights,
                    "profiles_reused": observation["profiles_reused"],
                    "comparisons_reused": observation["comparisons_reused"], "evidence_recomputations": 0})
            decision = check_decision(observation, model, total, weights, initial=step == 0)
            action = observation["action"]
            edge = branch(model, observation["state"], action)
            verify.need(edge is not None, "autonomous decision has no model branch")
            expected_rows = edge["next"] // (HORIZON + 1)
            batch = expected_rows - rows
            # This command is built only after the optimizer's preceding response.
            if batch:
                receipt = hma.apply({"op": "append", "seq": hma.next_seq, "epoch": hma.epoch,
                                     "rows": table["contract"][rows:expected_rows]})
            else:
                receipt = hma.apply({"op": "inspect", "seq": hma.next_seq, "epoch": hma.epoch})
            transcript.extend([b"hma\n", native_hma.last_line])
            measured = verify_measured(receipt, rows, batch, edge["costs"])
            # Independent original-definition execution for each newly encountered input.
            key = digest(hma.current)
            if key not in expected_cache:
                expected_cache[key] = verify.compute_expected(hma.current)
            verify.compare_result(expected_cache[key], receipt["result"])
            reference = incremental.Incremental(hma.current)
            certified_check.check_cells(reference, receipt, hma.current)
            # Corrupt observed work must be refused before policy outcome admission.
            corrupt = copy.deepcopy(receipt)
            corrupt["pair_additions"] += 1
            try:
                verify_measured(corrupt, rows, batch, edge["costs"])
            except verify.Rejected:
                pass
            else:
                raise RuntimeError("contradicted measured outcome was accepted")
            total_work += measured[0]
            spent = [x + y for x, y in zip(spent, measured)]
            summaries.append({"decision": step, "weights": list(weights), "before_rows": rows,
                "after_rows": expected_rows, "action": action, "batch": batch,
                "predicted_costs": edge["costs"], "measured_costs": measured,
                "cumulative_pairs": total_work, "chosen_hma": receipt["result"]["chosen"],
                "outcome_sha256": digest(receipt["result"]), **decision})
            rows = expected_rows
            observation = request(native_policy, {"op": "outcome", "seq": observation["next_seq"],
                "epoch": observation["epoch"], "outcome": 0}, transcript, b"policy")
            verify.need(type(observation["state"]) is int and observation["state"] == edge["next"] and
                        verify.canonical(observation["spent"]) == verify.canonical(spent),
                        "policy continuation does not reflect validated empirical outcome")
        terminal = check_decision(observation, model, total, weights)
        verify.need(rows == total and total_work == total * (total - 1) // 2 and
                    observation["remaining"] == 0 and terminal["weighted_cost"] == 0,
                    "autonomous schedule did not complete the qualified corpus")
        verify.compare_result(verify.read_json(HERE / "results/X.json"), receipt["result"])
        verify.need(initial["pair_additions"] == 0, "nonempty autonomous starting state")
        return {"initial_weights": initial_weights, "parameter_changes": parameter_events,
                "decisions": summaries, "nonempty_batches": [d["batch"] for d in summaries if d["batch"]],
                "final_rows": rows, "cumulative_costs": spent, "cumulative_pairs": total_work,
                "committed_bound": summaries[0]["initial_bound"], "terminal_budget": observation["budget"],
                "final_hma": receipt["result"]["chosen"], "contradicted_outcomes_rejected": HORIZON,
                "full_qualification": True}, b"".join(transcript)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--binary", type=Path)
    args = parser.parse_args()
    try:
        verify.need(bool(args.binary or os.environ.get("HMA_REASONING_BINARY")),
                    "requires fixed shared reasoning executable")
        binary = args.binary or Path(os.environ["HMA_REASONING_BINARY"])
        fixture = verify.read_json(HERE / "instances/X.json")
        expected_cache: dict[str, dict] = {}
        cases = {"single-batch": ([0, 100, 1], None, None),
                 "balanced": ([0, 1, 10], None, None),
                 "zero-weights": ([0, 0, 0], None, None),
                 "weighted-tie": ([0, 10, 1], None, None),
                 "reparameterized": ([0, 1, 10], 1, [0, 100, 1])}
        report = {"schema": 1, "scope": "every partition of eight ordered X rows into at most three nonempty batches",
                  "costs": ["measured incident row pairs", "nonempty batch submissions", "declared batch-square tariff"],
                  "horizon": HORIZON, "cases": {}}
        for name, (weights, change_after, changed_weights) in cases.items():
            first, raw_first = run_case(binary, fixture, weights, change_after, changed_weights, expected_cache)
            second, raw_second = run_case(binary, fixture, weights, change_after, changed_weights, expected_cache)
            verify.need(raw_first == raw_second and verify.canonical(first) == verify.canonical(second),
                        "autonomous two-session outcome bytes disagree")
            if name == "single-batch":
                verify.need(first["nonempty_batches"] == [8], "submission tariff did not select one batch")
            if name == "balanced":
                verify.need(sorted(first["nonempty_batches"]) == [2, 3, 3] and
                            first["cumulative_costs"] == [28, 3, 22],
                            "batch tariff did not select globally balanced batches")
            if name == "reparameterized":
                verify.need(sorted(first["nonempty_batches"]) == [2, 3, 3] and
                            any(d["commitment_restricts_preference"] for d in first["decisions"]),
                            "parameter change escaped the previously committed component bound")
            report["cases"][name] = {**first, "byte_exact": True,
                                     "execution_sha256": hashlib.sha256(raw_first).hexdigest()}
            print(f"AUTONOMOUS {name}: batches={first['nonempty_batches']}; "
                  "all schedules/frontier/weighted optimum within committed bounds=EXACT; "
                  "full X qualified; measured pairs=28; raw bytes=EXACT",
                  flush=True)
        report["original_definition_inputs"] = len(expected_cache)
        report["empirical_decisions"] = HORIZON * len(cases)
        path = HERE / "results/autonomous.json"
        if args.record:
            path.write_text(verify.canonical(report), encoding="utf-8")
        else:
            verify.need(path.is_file() and path.read_text() == verify.canonical(report),
                        "recorded autonomous results disagree with fresh execution")
        print(f"AUTONOMOUS GATE PASS: {len(cases)} parameter regimes; {report['empirical_decisions']} decisions; "
              "complete initial optimum and Pareto/weighted-optimal budget-feasible continuations; "
              "real online HMA execution and original-definition agreement; "
              "validated outcomes before admission; parameter-only evidence reuse; byte-exact replay", flush=True)
        return 0
    except (RuntimeError, verify.Rejected, OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print("AUTONOMOUS GATE REJECTED: " + str(error), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
