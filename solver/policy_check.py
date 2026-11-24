#!/usr/bin/env python3
"""Check persistent adaptive-policy Pareto execution against exhaustive traces.

The oracle enumerates every full outcome-contingent policy tree, enumerates
its supported traces, and derives coordinatewise worst total costs. The
native process executes the universally proved cache and frontier operations.
"""
from __future__ import annotations

import argparse
import copy
import functools
import hashlib
import itertools
import json
import os
from pathlib import Path
import tempfile

import online
import reasoning
import verify

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "solver/results/policy.json"


def need(test: bool, reason: str) -> None:
    verify.need(test, "policy gate: " + reason)


@functools.lru_cache(maxsize=None)
def trees(actions: int, outcomes: int, horizon: int) -> tuple:
    if horizon == 0:
        return (None,)
    children = trees(actions, outcomes, horizon - 1)
    return tuple((a, rest) for a in range(actions)
                 for rest in itertools.product(children, repeat=outcomes))


def action(model: dict, state: int, identifier: int) -> dict | None:
    return next((a for a in model["states"][state]["actions"] if a["id"] == identifier), None)


def tree_json(tree):
    return None if tree is None else {"action": tree[0], "after": [tree_json(t) for t in tree[1]]}


def evaluate(model: dict, state: int, tree) -> tuple[bool, list[list[int]], list[list]]:
    """List full supported path costs, independently of max-before-sum code."""
    d = model["dimensions"]
    if tree is None:
        return True, [model["states"][state]["terminal"][:]], [["terminal", state]]
    aid, following = tree
    act = action(model, state, aid)
    dependencies = [["branch", state, aid]]
    if act is None:
        return False, [[0] * d], dependencies
    allowed = True
    paths: list[list[int]] = []
    for out in act["outcomes"]:
        valid, suffixes, sources = evaluate(model, out["next"], following[out["id"]])
        allowed &= valid
        dependencies.extend(sources)
        paths.extend([[c + tail for c, tail in zip(out["costs"], suffix)] for suffix in suffixes])
    return allowed, paths or [[0] * d], dependencies


def all_profiles(model: dict, horizon: int, state: int) -> list[dict]:
    records = []
    for identifier, tree in enumerate(trees(model["actions"], model["outcomes"], horizon)):
        admitted, paths, dependencies = evaluate(model, state, tree)
        records.append({"id": identifier, "admitted": admitted,
                        "profile": [max(path[i] for path in paths) for i in range(model["dimensions"])],
                        "dependencies": dependencies})
    return records


def dominates(left: dict, right: dict) -> bool:
    return (all(a <= b for a, b in zip(left["profile"], right["profile"])) and
            any(a < b for a, b in zip(left["profile"], right["profile"])))


def support_equal(old: dict, new: dict, source: list) -> bool:
    _, state, *ids = source
    if source[0] == "terminal":
        return old["states"][state]["terminal"] == new["states"][state]["terminal"]
    if [a["id"] for a in old["states"][state]["actions"]] != [a["id"] for a in new["states"][state]["actions"]]:
        return False
    before, after = action(old, state, ids[0]), action(new, state, ids[0])
    return (before or {"outcomes": []})["outcomes"] == (after or {"outcomes": []})["outcomes"]


class Reference:
    def __init__(self):
        self.model = None
        self.weights = []
        self.state = self.horizon = self.epoch = 0
        self.seq = 1
        self.cumulative_profiles = self.cumulative_comparisons = 0
        self.spent = []
        self.budget = None
        self.initial_bound = []
        self.records = self.catalogue = []

    def build(self):
        self.records = all_profiles(self.model, self.horizon, self.state)
        self.catalogue = [{"id": r["id"], "profile": r["profile"]} for r in self.records if r["admitted"]]
        if self.budget is not None:
            self.catalogue = [p for p in self.catalogue if all(c <= b for c,b in zip(p["profile"],self.budget))]

    def choices(self):
        frontier = [p for p in self.catalogue if not any(dominates(q, p) for q in self.catalogue)]
        chosen = min(frontier, key=lambda p: (sum(a*b for a, b in zip(self.weights, p["profile"])),
                                               sum(p["profile"]), p["id"]))
        return frontier, chosen

    def apply(self, request: dict) -> dict:
        op = request["op"]
        ids, reused, comparisons, comp_reused, reset = [], len(self.records), 0, len(self.catalogue) ** 2, False
        if op in {"start", "rebase"}:
            if op == "rebase":
                self.seq += 1
                self.epoch += 1
            self.model = copy.deepcopy(request["model"])
            self.weights = request["weights"][:]
            self.horizon, self.state = request["horizon"], request["state"]
            self.spent = [0] * self.model["dimensions"]
            self.budget = None
            self.build()
            _, commitment = self.choices()
            self.budget = commitment["profile"][:]
            self.initial_bound = self.budget[:]
            self.build()
            ids, reused, comparisons, comp_reused, reset = list(range(len(self.records))), 0, len(self.catalogue)**2, 0, True
        elif op == "parameters":
            self.weights = request["weights"][:]
            self.seq += 1
        elif op == "revise":
            previous, previous_catalogue = self.model, self.catalogue
            candidate = copy.deepcopy(request["model"])
            ids = [r["id"] for r in self.records if not all(support_equal(previous, candidate, d)
                                                           for d in r["dependencies"])]
            reused = len(self.records) - len(ids)
            self.model, self.weights = candidate, request["weights"][:]
            self.build()
            retained = sum(p in previous_catalogue for p in self.catalogue)
            comp_reused = retained * retained
            comparisons = len(self.catalogue)**2 - comp_reused
            self.seq += 1
        elif op == "outcome":
            _, picked = self.choices()
            tree = trees(self.model["actions"], self.model["outcomes"], self.horizon)[picked["id"]]
            act = action(self.model, self.state, tree[0])
            outcome = next(o for o in act["outcomes"] if o["id"] == request["outcome"])
            self.spent = [x + y for x, y in zip(self.spent, outcome["costs"])]
            self.budget = [x - y for x,y in zip(self.budget,outcome["costs"])]
            need(all(b >= 0 for b in self.budget), "negative residual commitment")
            self.state, self.horizon = outcome["next"], self.horizon - 1
            self.build()
            self.seq += 1
            ids, reused, comparisons, comp_reused, reset = list(range(len(self.records))), 0, len(self.catalogue)**2, 0, True
        elif op == "checkpoint":
            self.build()
            ids, reused, comparisons, comp_reused, reset = list(range(len(self.records))), 0, len(self.catalogue)**2, 0, True
        elif op != "inspect":
            raise AssertionError(op)
        self.cumulative_profiles += len(ids)
        self.cumulative_comparisons += comparisons
        frontier, picked = self.choices()
        tree = trees(self.model["actions"], self.model["outcomes"], self.horizon)[picked["id"]]
        return {"objective": "weighted-coordinatewise-worst", "state": self.state, "remaining": self.horizon,
                "next_seq": self.seq, "epoch": self.epoch, "weights": self.weights, "spent": self.spent,
                "budget": self.budget, "initial_bound": self.initial_bound,
                "selected": picked, "action": None if tree is None else tree[0], "policy": tree_json(tree),
                "weighted_cost": sum(a*b for a, b in zip(self.weights, picked["profile"])),
                "policies": self.records, "catalogue": self.catalogue, "frontier": frontier,
                "comparisons": [[p["id"], q["id"], dominates(p, q)] for p in self.catalogue for q in self.catalogue],
                "profiles_needed": len(ids), "profiles_reused": reused, "recomputed_ids": ids,
                "comparisons_needed": comparisons, "comparisons_reused": comp_reused,
                "cumulative_profiles": self.cumulative_profiles, "cumulative_comparisons": self.cumulative_comparisons,
                "problem_reset": reset}


def model(rows: list, actions: int, outcomes: int, dimensions: int) -> dict:
    return {"states": rows, "actions": actions, "outcomes": outcomes, "dimensions": dimensions}


def row(profiles: list[list[int]], next_state: int = 0) -> dict:
    return {"terminal": [0] * len(profiles[0]),
            "actions": [{"id": a, "outcomes": [{"id": 0, "next": next_state, "costs": costs}]}
                        for a, costs in enumerate(profiles)]}


def campaign_cases() -> dict[str, list[tuple[dict, bool]]]:
    trade = model([row([[0,4],[2,3],[4,0]]), row([[0,0],[0,0],[0,0]], 1)], 3, 1, 2)
    bad = copy.deepcopy(trade); bad["states"][0]["actions"][1]["outcomes"][0]["costs"] = [5,5]
    removed = copy.deepcopy(trade); del removed["states"][0]["actions"][1]
    unrelated = copy.deepcopy(trade); unrelated["states"][1]["terminal"] = [17,18]
    new_branch = model([row([[2,2],[2,2]])], 2, 2, 2)
    added_branch = copy.deepcopy(new_branch)
    added_branch["states"][0]["actions"][0]["outcomes"].append({"id":1,"next":0,"costs":[9,9]})
    mixed = model([{"terminal":[0,0],"actions":[
        {"id":0,"outcomes":[{"id":0,"next":0,"costs":[0,10]}, {"id":1,"next":0,"costs":[10,0]}]},
        {"id":1,"outcomes":[{"id":0,"next":0,"costs":[6,6]}, {"id":1,"next":0,"costs":[6,6]}]}]}],2,2,2)
    history = model([
        {"terminal":[0,0],"actions":[{"id":a,"outcomes":[
            {"id":0,"next":1,"costs":[10,0]}, {"id":1,"next":1,"costs":[0,10]}]} for a in range(2)]},
        {"terminal":[0,0],"actions":[{"id":a,"outcomes":[
            {"id":o,"next":2,"costs":[0,10] if a == 0 else [10,0]} for o in range(2)]} for a in range(2)]},
        {"terminal":[0,0],"actions":[{"id":a,"outcomes":[
            {"id":o,"next":2,"costs":[0,0]} for o in range(2)]} for a in range(2)]}], 2, 2, 2)
    greedy = model([row([[0],[2]], 0), row([[100],[100]], 2), row([[0],[0]], 2)], 2, 1, 1)
    greedy["states"][0]["actions"][0]["outcomes"][0]["next"] = 1
    greedy["states"][0]["actions"][1]["outcomes"][0]["next"] = 2
    zero = model([row([[],[]])],2,1,0)
    duplicate = copy.deepcopy(trade); duplicate["states"][0]["actions"].append(copy.deepcopy(duplicate["states"][0]["actions"][0]))
    wrong_dim = copy.deepcopy(trade); wrong_dim["states"][0]["terminal"] = [0]
    impossible = copy.deepcopy(trade); impossible["states"][0]["actions"][0]["outcomes"][0]["costs"] = [9,9]
    def start(m, weights, horizon=1):
        return ({"op":"start","model":m,"weights":weights,"horizon":horizon,"state":0},True)
    def revise(m, weights):
        return ({"op":"revise","model":m,"weights":weights},True)
    return {
        "parametric-nonconvex-retraction": [start(trade,[1,1]),
            ({"op":"parameters","weights":[0,1]},True), ({"op":"parameters","weights":[0,0]},True),
            revise(bad,[1,1]), revise(trade,[1,1]), revise(removed,[1,1]), revise(trade,[1,1]),
            revise(unrelated,[1,1]), ({"op":"checkpoint"},True), ({"op":"inspect"},True),
            ({"op":"revise","model":duplicate,"weights":[1,1]},False),
            ({"op":"revise","model":wrong_dim,"weights":[1,1]},False),
            ({"op":"revise","model":impossible,"weights":[1,1]},False),
            ({"op":"parameters","weights":[-1,0]},False),
            ({"op":"parameters","weights":[True,0]},False),
            ({"op":"parameters","weights":[1]},False),
            ({"op":"inspect","seq":0},False), ({"op":"inspect","epoch":1},False),
            ({"op":"inspect","extra":0},False), ({"op":"outcome","outcome":0},True),
            ({"op":"outcome","outcome":0},False), ({"op":"inspect"},True)],
        "new-supported-outcome": [start(new_branch,[1,1]), ({"op":"outcome","outcome":1},False),
            revise(added_branch,[1,1]), ({"op":"outcome","outcome":1},False),
            ({"op":"outcome","outcome":0},True)],
        "max-before-weight": [start(mixed,[1,1]), ({"op":"outcome","outcome":1},True)],
        "full-history-adaptation": [start(history,[1,1],2), ({"op":"parameters","weights":[0,0]},True),
            ({"op":"outcome","outcome":1},True), ({"op":"outcome","outcome":0},True)],
        "nongreedy-horizon": [start(greedy,[1],2), ({"op":"outcome","outcome":0},True),
            ({"op":"outcome","outcome":0},True)],
        "zero-dimension": [start(zero,[]), ({"op":"parameters","weights":[]},True),
            ({"op":"outcome","outcome":0},True)],
        "zero-horizon": [start(trade,[1,1],0), ({"op":"outcome","outcome":0},False),
            ({"op":"rebase","model":new_branch,"weights":[1,1],"horizon":1,"state":0},True),
            ({"op":"inspect","epoch":0},False), ({"op":"inspect"},True)],
    }


def run_case(binary: Path, name: str, actions: list[tuple[dict,bool]]) -> tuple[bytes,dict]:
    reference = Reference()
    transcript = bytearray()
    receipts = []
    refusals = 0
    with online.Native(binary, args=["policy"]) as native:
        for index, (source, accepted) in enumerate(actions):
            request = copy.deepcopy(source)
            if request["op"] != "start":
                request.setdefault("seq",reference.seq)
                request.setdefault("epoch",reference.epoch)
            response = native.exchange(request)
            transcript.extend(native.last_line)
            need(response["ok"] is accepted, f"{name}/{index}: unexpected admission: {response}")
            if not accepted:
                refusals += 1
                continue
            expected = reference.apply(request)
            actual = response["observation"]
            if verify.canonical(actual) != verify.canonical(expected):
                keys = set(actual) | set(expected)
                diff = {k: {"actual":actual.get(k),"expected":expected.get(k)} for k in keys
                        if verify.canonical(actual.get(k)) != verify.canonical(expected.get(k))}
                raise verify.Rejected(f"policy gate: {name}/{index}: full observation mismatch: {json.dumps(diff)[:5000]}")
            receipts.append({"request":index,"op":request["op"],"state":actual["state"],
                "remaining":actual["remaining"],"selected":actual["selected"],
                "spent":actual["spent"],"budget":actual["budget"],"initial_bound":actual["initial_bound"],
                "frontier_ids":[p["id"] for p in actual["frontier"]],
                "policy_count":len(actual["policies"]),"admitted_count":len(actual["catalogue"]),
                "profiles_needed":actual["profiles_needed"],"profiles_reused":actual["profiles_reused"],
                "comparisons_needed":actual["comparisons_needed"],"comparisons_reused":actual["comparisons_reused"],
                "observation_sha256":hashlib.sha256(verify.canonical(actual).encode()).hexdigest()})
            if index == 0 and name == "parametric-nonconvex-retraction":
                all_points = [{"id":r["id"],"profile":r["profile"]} for r in actual["policies"] if r["admitted"]]
                unbounded_front = [p for p in all_points if not any(dominates(q,p) for q in all_points)]
                need([p["id"] for p in unbounded_front] == [0,1,2], "nonconvex full-policy point lost")
                need(actual["budget"] == [0,4], "initial commitment not selected profile")
            if index == 0 and name == "max-before-weight":
                need(actual["action"] == 1 and actual["selected"]["profile"] == [6,6], "wrong robust objective")
                profiles = trees(2,2,1)
                worst_scalar = [max(sum(path) for path in evaluate(reference.model,0,t)[1]) for t in profiles]
                need(worst_scalar == [10,12], "scalar/Pareto separation control broken")
            if index == 0 and name == "full-history-adaptation":
                need(actual["selected"]["profile"] == [10,10], "history-contingent optimum lost")
                need([t["action"] for t in actual["policy"]["after"]] == [0,1], "policy collapsed equal-state histories")
            if index == 0 and name == "nongreedy-horizon":
                need(actual["action"] == 1 and actual["selected"]["profile"] == [2], "one-step greedy substituted")
            need([a+b for a,b in zip(actual["spent"],actual["budget"])] == actual["initial_bound"],
                 "cumulative budget ledger failed")
            need(all(a+b <= c for a,b,c in zip(actual["spent"],actual["selected"]["profile"],actual["initial_bound"])),
                 "selected remaining policy exceeds committed bound")
            need(not any(dominates(r,actual["selected"]) for r in actual["policies"] if r["admitted"]),
                 "budget-constrained selection globally dominated")
            if name == "full-history-adaptation" and index == 2:
                need(actual["budget"] == [10,0] and actual["action"] == 1,
                     "replanning discarded history-sensitive residual commitment")
    return bytes(transcript), {"accepted_prefixes":len(receipts),"refusals":refusals,"receipts":receipts,
        "execution_sha256":hashlib.sha256(transcript).hexdigest()}


def run(binary: Path) -> dict:
    result = {"schema":1,"engine":"persistent-proved-adaptive-policy-pareto", "cases":{}}
    for name, events in campaign_cases().items():
        first, receipt = run_case(binary,name,events)
        second, other = run_case(binary,name,events)
        need(first == second and receipt == other, name + " fresh-process bytes differ")
        receipt["byte_exact"] = True
        result["cases"][name] = receipt
        print(f"POLICY {name}: PASS; prefixes={receipt['accepted_prefixes']}; refusals={receipt['refusals']}; raw bytes EXACT")
    return result


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record",action="store_true")
    parser.add_argument("--lean",default=os.environ.get("LEAN","lean"))
    parser.add_argument("--lean-dir",type=Path,default=Path(os.environ["HMA_BUILD_DIR"]) if "HMA_BUILD_DIR" in os.environ else None)
    args=parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="hma-policy-") as temporary:
        tmp=Path(temporary)
        provided=os.environ.get("HMA_REASONING_BINARY")
        if provided:
            binary=Path(provided)
        else:
            build=args.lean_dir or tmp/"proof"
            if args.lean_dir is None:
                reasoning.cold_build(build,args.lean,lanes=["policy"])
            binary=reasoning.build_binary(build,args.lean,tmp/"native",lanes=["policy"])
        report=run(binary)
    output=verify.canonical(report)
    if args.record:
        RESULT.write_text(output,encoding="utf-8")
    else:
        need(RESULT.exists() and RESULT.read_text()==output,"recorded report stale")
    count=sum(v["accepted_prefixes"] for v in report["cases"].values())
    refused=sum(v["refusals"] for v in report["cases"].values())
    print(f"POLICY GATE PASS: {len(report['cases'])} campaigns; {count} prefixes; {refused} refusals; every adaptive policy/profile/frontier/selection/dependency/work field agrees; two-process raw bytes EXACT")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
