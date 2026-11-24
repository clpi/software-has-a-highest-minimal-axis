#!/usr/bin/env python3
"""Attack and compare the online certified controller with full adaptive trees."""
from __future__ import annotations

import copy
import argparse
import hashlib
import itertools
import json
import os
from pathlib import Path
import random
import sys
import tempfile

import online
import reasoning
import verify

ROOT = Path(__file__).resolve().parents[1]


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def trees(model, weights, state, horizon):
    """Enumerate adaptive branch choices; do not use Bellman backup or its cache."""
    row = model["states"][state]
    if horizon == 0:
        return [(dot(weights, row["terminal"]), None)]
    candidates = []
    for action in row["actions"]:
        branches = [trees(model, weights, b["next"], horizon - 1) for b in action["outcomes"]]
        for continuations in itertools.product(*branches):
            costs = [dot(weights, b["costs"]) + continuation[0]
                     for b, continuation in zip(action["outcomes"], continuations, strict=True)]
            candidates.append((max(costs), action["id"]))
    return candidates


def values(model, weights, horizon):
    return [[min(trees(model, weights, s, h))[0] for s in range(len(model["states"]))]
            for h in range(horizon + 1)]


def signature(model, weights, s):
    return [(a["id"], [(o["id"], o["next"], dot(weights, o["costs"])) for o in a["outcomes"]])
            for a in model["states"][s]["actions"]]


def layers(model, weights, horizon, old=None):
    current = values(model, weights, horizon)
    result = []
    for h, vector in enumerate(current):
        before = old["layers"][h]["values"] if old else [[i, 0] for i in range(len(vector))]
        changed = [i for i, v in enumerate(vector) if v != before[i][1]]
        if h == 0:
            dirty = changed
        elif old is None:
            dirty = list(range(len(vector)))
        else:
            dirty = [s for s in range(len(vector)) if
                     signature(old["model"], old["weights"], s) != signature(model, weights, s) or
                     any(o["next"] in result[h - 1]["changed"]
                         for a in model["states"][s]["actions"] for o in a["outcomes"])]
        # Fresh nonterminal layers intentionally mark all carried cells changed.
        result.append({"values": list(enumerate(vector)),
                       "changed": list(range(len(vector))) if h and old is None else changed,
                       "recomputed": dirty})
    return json.loads(json.dumps(result))


class Oracle:
    def __init__(self):
        self.data = None

    def apply(self, req):
        op = req["op"]
        if op in {"start", "rebase"}:
            previous = self.data
            model, weights, h = req["model"], req["weights"], req["horizon"]
            ls = layers(model, weights, h)
            work = sum(len(l["recomputed"]) for l in ls)
            self.data = {"model": copy.deepcopy(model), "weights": list(weights), "horizon": h,
                         "state": req["state"], "layers": ls, "seq": 1 if previous is None else previous["seq"] + 1,
                         "epoch": 0 if previous is None else previous["epoch"] + 1,
                         "spent": [0] * model["dimensions"],
                         "cumulative": work + (0 if previous is None else previous["cumulative"])}
        else:
            d = self.data
            if op in {"revise", "parameters"}:
                model, weights = req.get("model", d["model"]), req["weights"]
                ls = layers(model, weights, d["horizon"], d)
                work = sum(len(l["recomputed"]) for l in ls)
                d.update(model=copy.deepcopy(model), weights=list(weights), layers=ls, seq=d["seq"] + 1,
                         cumulative=d["cumulative"] + work)
            elif op == "outcome":
                candidates = trees(d["model"], d["weights"], d["state"], d["horizon"])
                action = min(candidates, key=lambda p: p[0])[1]
                act = next(a for a in d["model"]["states"][d["state"]]["actions"] if a["id"] == action)
                branch = next(o for o in act["outcomes"] if o["id"] == req["outcome"])
                d["spent"] = [x + y for x, y in zip(d["spent"], branch["costs"], strict=True)]
                d.update(state=branch["next"], horizon=d["horizon"] - 1, layers=d["layers"][:-1], seq=d["seq"] + 1)
                work = 0
            elif op == "checkpoint":
                d["layers"] = layers(d["model"], d["weights"], d["horizon"])
                work = sum(len(l["recomputed"]) for l in d["layers"])
                d["cumulative"] += work
            elif op == "inspect":
                work = 0
            else:
                raise AssertionError(op)
        d = self.data
        all_policies = trees(d["model"], d["weights"], d["state"], d["horizon"])
        best = min(all_policies, key=lambda p: p[0])
        return {"state": d["state"], "remaining": d["horizon"], "next_seq": d["seq"], "epoch": d["epoch"],
                "chosen": best[1], "spent": dot(d["weights"], d["spent"]), "spent_vector": d["spent"],
                "value": best[0], "recomputed_cells": work, "cumulative_cells": d["cumulative"],
                "stored_cells": (d["horizon"] + 1) * len(d["model"]["states"]), "layers": d["layers"]}


def act(i, branches):
    return {"id": i, "outcomes": [{"id": o, "next": s, "costs": costs} for o, s, costs in branches]}


def greedy_model():
    return {"actions": 2, "outcomes": 2, "dimensions": 2, "states": [
        {"terminal": [0, 0], "actions": [act(0, [(0, 1, [0, 0])]), act(1, [(0, 2, [2, 0])])]},
        {"terminal": [0, 0], "actions": [act(0, [(0, 1, [100, 0])])]},
        {"terminal": [0, 0], "actions": [act(0, [(0, 2, [0, 0])])]},
    ]}


def chain_model():
    return {"actions": 1, "outcomes": 2, "dimensions": 2, "states": [
        {"terminal": [0, 0], "actions": [act(0, [(0, 1, [0, 0])])]},
        {"terminal": [0, 0], "actions": [act(0, [(0, 2, [0, 0])])]},
        {"terminal": [1, 0], "actions": [act(0, [(0, 2, [0, 0])])]},
        {"terminal": [0, 0], "actions": [act(0, [(0, 3, [0, 0])])]},
    ]}


def run(binary):
    native = online.Native(binary, args=["controller"])
    oracle = Oracle()
    transcript = bytearray()
    receipts, rejections = [], []

    def request(req, label, reject=False):
        if oracle.data and req["op"] != "start":
            req = {"seq": oracle.data["seq"], "epoch": oracle.data["epoch"], **req}
        actual = native.exchange(req)
        transcript.extend(native.last_line)
        if reject:
            verify.need(actual["ok"] is False, "accepted bad controller request: " + label)
            rejections.append(label)
            return
        verify.need(actual["ok"], "controller refused valid request: " + label + str(actual))
        expected = oracle.apply(req)
        verify.need(verify.canonical(actual["observation"]) == verify.canonical(expected),
                    "controller/exhaustive-policy disagreement: " + label + "\n" +
                    verify.canonical(actual["observation"]) + verify.canonical(expected))
        receipts.append({"label": label, "chosen": expected["chosen"], "value": expected["value"],
                         "remaining": expected["remaining"], "recomputed_cells": expected["recomputed_cells"],
                         "stored_cells": expected["stored_cells"], "cumulative_cells": expected["cumulative_cells"],
                         "receipt_sha256": hashlib.sha256(native.last_line).hexdigest()})
        return expected

    try:
        r = request({"op": "start", "model": greedy_model(), "weights": [1, 0], "horizon": 2, "state": 0}, "anti-greedy")
        verify.need(r["chosen"] == 1 and r["value"] == 2, "greedy trap not avoided")
        r = request({"op": "parameters", "weights": [1, 0]}, "same-parameters")
        verify.need(r["recomputed_cells"] == 0, "identical parameters recomputed Bellman cells")
        request({"op": "outcome", "outcome": 1}, "unsupported-outcome", True)
        request({"op": "inspect"}, "atomic-after-outcome")
        request({"op": "parameters", "weights": [0, 0]}, "zero-parameters")
        zero_change = greedy_model()
        zero_change["states"][0]["actions"][1]["outcomes"][0]["costs"][0] = 3
        r = request({"op": "revise", "model": zero_change, "weights": [0, 0]}, "zero-weight-model-edit")
        verify.need(r["recomputed_cells"] == 0, "zero-weight costs changed scalar values")
        request({"op": "parameters", "weights": [1, 0]}, "restore-parameters")
        request({"op": "outcome", "outcome": 0}, "first-empirical-outcome")
        request({"op": "parameters", "weights": [2, 1]}, "reprice-cumulative-vector")
        request({"op": "checkpoint"}, "current-state-reconstruction")
        request({"op": "outcome", "outcome": 0}, "final-empirical-outcome")
        request({"op": "outcome", "outcome": 0}, "exhausted-horizon", True)
        request({"op": "parameters", "weights": [True, 1]}, "boolean-parameter", True)
        request({"op": "inspect", "seq": 0}, "stale-sequence", True)
        request({"op": "inspect", "epoch": 5}, "stale-epoch", True)
        request({"op": "parameters", "weights": [-1, 1]}, "negative-parameter", True)
        request({"op": "parameters", "weights": [1]}, "missing-parameter", True)
        request({"op": "inspect", "extra": 0}, "unknown-field", True)
        request({"op": "rebase", "model": chain_model(), "weights": [1, 0], "horizon": 3, "state": 0}, "dependency-chain")
        changed = chain_model()
        changed["states"][2]["terminal"][0] = 2
        r = request({"op": "revise", "model": changed, "weights": [1, 0]}, "terminal-propagation")
        verify.need(r["recomputed_cells"] == 9 < r["stored_cells"], "dependency cone not incremental")
        changed["states"][1]["actions"][0]["outcomes"].append({"id": 1, "next": 3, "costs": [20, 0]})
        request({"op": "revise", "model": changed, "weights": [1, 0]}, "new-supported-outcome")
        changed["states"][1]["actions"][0]["outcomes"] = changed["states"][1]["actions"][0]["outcomes"][:1]
        request({"op": "revise", "model": changed, "weights": [1, 0]}, "outcome-withdrawal")
        bad = copy.deepcopy(changed)
        bad["states"][0]["actions"] = []
        request({"op": "revise", "model": bad, "weights": [1, 0]}, "no-admitted-action", True)
        bad = copy.deepcopy(changed)
        bad["states"][0]["actions"][0]["outcomes"][0]["next"] = 4
        request({"op": "revise", "model": bad, "weights": [1, 0]}, "out-of-universe-successor", True)
        request({"op": "inspect"}, "atomic-after-malformed-model")
        rng = random.Random(6309)
        for k in range(12):
            model = {"actions": 2, "outcomes": 2, "dimensions": 3, "states": []}
            for _ in range(3):
                actions = [act(a, [(o, rng.randrange(3), [rng.randrange(5) for _ in range(3)])
                                   for o in range(2)]) for a in range(2)]
                model["states"].append({"terminal": [rng.randrange(4) for _ in range(3)], "actions": actions})
            weights = [rng.randrange(4) for _ in range(3)]
            request({"op": "rebase", "model": model, "weights": weights, "horizon": 2, "state": k % 3}, f"exhaustive-{k}")
            request({"op": "parameters", "weights": list(reversed(weights))}, f"parameters-{k}")
            model["states"][k % 3]["actions"][0]["outcomes"][0]["costs"][1] += 1
            request({"op": "revise", "model": model, "weights": list(reversed(weights))}, f"revision-{k}")
            request({"op": "outcome", "outcome": k % 2}, f"observation-{k}")
            request({"op": "outcome", "outcome": (k + 1) % 2}, f"completion-{k}")
        return bytes(transcript), receipts, rejections
    finally:
        native.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    binary = os.environ.get("HMA_REASONING_BINARY")
    with tempfile.TemporaryDirectory(prefix="hma-controller-check-") as tmp:
        tmp = Path(tmp)
        if binary is None:
            lean = os.environ.get("LEAN", "lean")
            build = Path(os.environ["HMA_BUILD_DIR"]) if "HMA_BUILD_DIR" in os.environ else tmp / "proof"
            if "HMA_BUILD_DIR" not in os.environ:
                reasoning.cold_build(build, lean, ["controller"])
            binary = reasoning.build_binary(build, lean, tmp / "native", ["controller"])
        first, receipts, rejected = run(Path(binary))
        second, receipts2, rejected2 = run(Path(binary))
        verify.need(first == second and receipts == receipts2 and rejected == rejected2,
                    "controller raw bytes differ across fresh processes")
        report = {"schema": 1, "raw_bytes_exact": True, "transcript_sha256": hashlib.sha256(first).hexdigest(),
                  "accepted_prefixes": len(receipts), "rejected": rejected, "receipts": receipts,
                  "oracle": "all supported adaptive policy trees; every state and layer",
                  "boundaries": "finite declared model/horizon; scalar worst-of-weighted objective"}
        path = ROOT / "solver/results/controller.json"
        output = verify.canonical(report)
        if args.record:
            path.write_text(output)
        else:
            verify.need(path.is_file() and path.read_text() == output, "controller recorded receipts are absent or stale")
        print(f"CONTROLLER GATE PASS: {len(receipts)} online prefixes; all adaptive policies checked; "
              f"{len(rejected)} malformed/outcome/clock attacks rejected atomically; dependency propagation, "
              "zero-work reuse, cumulative costs, reconstruction and raw byte determinism PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
