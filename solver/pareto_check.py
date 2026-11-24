#!/usr/bin/env python3
"""Exercise the fixed, persistent, proved Pareto engine against exhaustive results."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import tempfile

import certified
import online
import solve
import verify

ROOT = Path(__file__).resolve().parents[1]
MODULES = ("Exponential", "OnlineHma", "ParametricPareto", "HmaPareto", "OnlinePareto")


def cold_build(build: Path, lean: str) -> None:
    online.cold_build(build, lean)
    environment = dict(os.environ, LEAN_PATH=str(build.resolve()))
    for module in MODULES[2:]:
        path = build / (module + ".lean")
        path.write_bytes((ROOT / "proof" / path.name).read_bytes())
        result = subprocess.run([lean, "-DwarningAsError=true", "-o", module + ".olean", path.name],
                                cwd=build, env=environment, capture_output=True, timeout=120)
        verify.need(result.returncode == 0 and not result.stderr,
                    "Pareto dependency failed: " + module + "\n" + result.stdout.decode() + result.stderr.decode())


def build_binary(build: Path, lean: str, temporary: Path) -> Path:
    compiler = certified.Executor(build, lean, temporary)
    for module in MODULES:
        cfile, obj = temporary / (module + ".c"), temporary / (module + ".o")
        compiler.command([lean, "-DwarningAsError=true", "--root=" + str(ROOT / "proof"),
                          "-c", str(cfile), str(ROOT / "proof" / (module + ".lean"))])
        compiler.command([compiler.leanc, "-O2", "-c", "-o", str(obj), str(cfile)])
        compiler.objects.append(str(obj))
    runner = temporary / "ParetoMain.lean"
    runner.write_text("import OnlinePareto\ndef main : IO Unit := OnlinePareto.run\n", encoding="utf-8")
    cfile, binary = temporary / "ParetoMain.c", temporary / "hma-pareto"
    compiler.command([lean, "-DwarningAsError=true", "-c", str(cfile), str(runner)])
    compiler.command([compiler.leanc, "-O2", "-o", str(binary), str(cfile), *compiler.objects])
    return binary


def canonical(value) -> str:
    return verify.canonical(value)


def dominates(y: dict, x: dict) -> bool:
    return all(a <= b for a, b in zip(y["profile"], x["profile"], strict=True)) and any(
        a < b for a, b in zip(y["profile"], x["profile"], strict=True))


def expected(points: list[dict], weights: list[int]) -> tuple[list[dict], dict | None, int | None]:
    frontier = [x for x in points if not any(dominates(y, x) for y in points)]
    def score(p):
        return sum(w * c for w, c in zip(weights, p["profile"], strict=True)), sum(p["profile"]), p["id"]
    selected = min(frontier, key=score) if frontier else None
    return frontier, selected, score(selected)[0] if selected else None


def pair_work(previous: list[dict], current: list[dict]) -> tuple[int, int]:
    retained = sum(any(canonical(p) == canonical(old) for old in previous) for p in current)
    return len(current) ** 2 - retained ** 2, retained ** 2


def check(observation: dict, points: list[dict], weights: list[int], seq: int, epoch: int,
          needed: int, reused: int, cumulative: int, hma_result=None, resources=None,
          hma_observation=None) -> None:
    frontier, selected, cost = expected(points, weights)
    regions = [{"point": p["id"], "inequalities": [
        {"against": q["id"], "coefficients": [b - a for a, b in zip(p["profile"], q["profile"], strict=True)]}
        for q in points]} for p in frontier]
    active = [r["point"] for r in regions if all(sum(w * c for w, c in zip(weights,
        row["coefficients"], strict=True)) >= 0 for row in r["inequalities"])]
    wanted = {"next_seq": seq, "epoch": epoch, "dimensions": len(weights), "weights": weights,
              "catalogue": points, "frontier": frontier, "regions": regions, "active_regions": active,
              "selected": selected, "weighted_cost": cost,
              "comparisons": [[y["id"], x["id"], dominates(y, x)] for y in points for x in points],
              "comparisons_needed": needed, "comparisons_reused": reused,
              "cumulative_comparisons": cumulative, "hma_result": hma_result,
              "resources": resources, "hma_observation": hma_observation}
    verify.need(canonical(observation) == canonical(wanted), "Pareto receipt disagrees with complete current input")


class RecordedNative(online.Native):
    def __init__(self, binary: Path, args: list[str], transcript):
        if args:
            super().__init__(binary, args=args)
        else:
            super().__init__(binary)
        self.transcript = transcript

    def exchange(self, command):
        reply = super().exchange(command)
        self.transcript.write(self.last_line)
        return reply


def native(binary: Path, args: list[str], transcript):
    return RecordedNative(binary, args, transcript)


def run_generic(binary: Path, args: list[str], transcript) -> dict:
    points = [{"id": 0, "profile": [0, 2, 0]}, {"id": 1, "profile": [1, 1, 0]},
              {"id": 2, "profile": [2, 0, 0]}, {"id": 3, "profile": [3, 3, 1]},
              {"id": 4, "profile": [0, 2, 0]}]
    weights, seq, epoch, cumulative = [1, 1, 0], 1, 0, len(points) ** 2
    controls, prefixes, work_total = [], 0, cumulative
    requests = hashlib.sha256()
    with native(binary, args, transcript) as process:
        def exchange(command):
            requests.update(canonical(command).encode())
            reply = process.exchange(command)
            verify.need(reply["ok"], "Pareto native refused lawful input: " + reply.get("error", ""))
            return reply["observation"]
        receipt = exchange({"op": "start", "dimensions": 3, "catalogue": points, "weights": weights})
        check(receipt, points, weights, seq, epoch, cumulative, 0, cumulative)
        prefixes += 1
        verify.need([p["id"] for p in receipt["frontier"]] == [0, 1, 2, 4], "equal-profile identity lost")
        latent = copy.deepcopy(receipt)
        hidden = next(cell for cell in latent["comparisons"] if cell[:2] == [3, 3])
        hidden[2] = True
        try:
            check(latent, points, weights, seq, epoch, cumulative, 0, cumulative)
        except verify.Rejected:
            controls.append("latent-dominated-self-comparison")
        else:
            raise verify.Rejected("latent comparison corruption accepted")
        for new_weights in [[1, 0, 0], [0, 1, 0], [0, 0, 0], [10**30, 1, 0]]:
            receipt = exchange({"op": "weights", "seq": seq, "epoch": epoch, "weights": new_weights})
            weights, seq = new_weights, seq + 1
            check(receipt, points, weights, seq, epoch, 0, 0, cumulative)
            prefixes += 1
        rng = random.Random(271828)
        for index in range(32):
            current = copy.deepcopy(points)
            if index % 4 == 0:
                # The next observation is constructed only after the previous decision arrives.
                selected = receipt["selected"]
                ident = max((p["id"] for p in current), default=-1) + 1
                base = selected["profile"] if selected else [0, 0, 0]
                current.append({"id": ident, "profile": [v + rng.randint(-2, 3) for v in base]})
            elif index % 4 == 1 and len(current) > 1:
                current = [p for p in current if p["id"] != receipt["selected"]["id"]]
            elif index % 4 == 2:
                target = rng.randrange(len(current))
                current[target]["profile"] = [rng.randint(-6, 8) for _ in weights]
            else:
                current = current[:]
            needed, reused = pair_work(points, current)
            receipt = exchange({"op": "reconcile", "seq": seq, "epoch": epoch, "catalogue": current})
            seq, cumulative, points = seq + 1, cumulative + needed, current
            work_total += needed
            check(receipt, points, weights, seq, epoch, needed, reused, cumulative)
            prefixes += 1
        bad_requests = [
            {"op": "weights", "seq": seq - 1, "epoch": epoch, "weights": weights},
            {"op": "weights", "seq": seq, "epoch": epoch + 1, "weights": weights},
            {"op": "weights", "seq": seq, "epoch": epoch, "weights": [-1, 0, 0]},
            {"op": "weights", "seq": seq, "epoch": epoch, "weights": [True, 0, 0]},
            {"op": "weights", "seq": seq, "epoch": epoch, "weights": [0]},
            {"op": "reconcile", "seq": seq, "epoch": epoch, "catalogue": points + [points[0]]},
            {"op": "reconcile", "seq": seq, "epoch": epoch, "catalogue": [{"id": 0, "profile": [0]}]},
            {"op": "reconcile", "seq": seq, "epoch": epoch, "catalogue": [{"id": 0, "profile": [False, 0, 0]}]},
            {"op": "resources", "seq": seq, "epoch": epoch, "resources": []},
            {"op": "inspect", "seq": seq, "epoch": epoch, "unknown": 0},
        ]
        for index, bad in enumerate(bad_requests):
            requests.update(canonical(bad).encode())
            reply = process.exchange(bad)
            verify.need(not reply["ok"], "malformed Pareto input accepted")
            clean = exchange({"op": "inspect", "seq": seq, "epoch": epoch})
            check(clean, points, weights, seq, epoch, 0, 0, cumulative)
            controls.append("atomic-refusal-" + str(index))
        baseline = exchange({"op": "inspect", "seq": seq, "epoch": epoch})
        corruptions = []
        if baseline["comparisons"]:
            bad = copy.deepcopy(baseline)
            bad["comparisons"][0][2] = not bad["comparisons"][0][2]
            corruptions.append(("hidden-comparison", bad))
        for label, field, value in [("missing-frontier", "frontier", []),
                                    ("wrong-parameter", "weights", [7, 7, 7]),
                                    ("wrong-selected", "selected", None),
                                    ("missing-linear-region", "regions", []),
                                    ("wrong-active-region", "active_regions", []),
                                    ("false-counter", "comparisons_needed", True)]:
            bad = copy.deepcopy(baseline)
            bad[field] = value
            corruptions.append((label, bad))
        for label, bad in corruptions:
            try:
                check(bad, points, weights, seq, epoch, 0, 0, cumulative)
            except verify.Rejected:
                controls.append(label)
            else:
                raise verify.Rejected("corrupt receipt accepted: " + label)
        for current, dimension in [([], 0), ([{"id": 2, "profile": []}, {"id": 9, "profile": []}], 0),
                                   ([{"id": 1, "profile": [-5, 2]}, {"id": 2, "profile": [-2, -1]}], 2),
                                   ([{"id": 0, "profile": [0, 3]}, {"id": 1, "profile": [2, 2]},
                                     {"id": 2, "profile": [3, 0]}], 2)]:
            weights = [0] * dimension
            needed = len(current) ** 2
            receipt = exchange({"op": "rebase", "seq": seq, "epoch": epoch,
                                "dimensions": dimension, "catalogue": current, "weights": weights})
            points, seq, epoch, cumulative = current, seq + 1, epoch + 1, cumulative + needed
            check(receipt, points, weights, seq, epoch, needed, 0, cumulative)
            prefixes += 1
        receipt = exchange({"op": "weights", "seq": seq, "epoch": epoch, "weights": [1, 1]})
        weights, seq = [1, 1], seq + 1
        check(receipt, points, weights, seq, epoch, 0, 0, cumulative)
        verify.need([p["id"] for p in receipt["frontier"]] == [0, 1, 2] and
                    receipt["active_regions"] == [0, 2], "unsupported Pareto identity lost or scalarized incorrectly")
        controls.append("unsupported-Pareto-point-retained")
        prefixes += 1
        return {"prefixes": prefixes, "controls": controls,
                "output_sha256": process.output_digest.hexdigest(), "request_sha256": requests.hexdigest(),
                "responses": process.response_count, "cumulative_comparisons": cumulative}


def hma_points(source: dict, result: dict, resources: list[int]) -> list[dict]:
    data = verify.decode(source)
    indices = {a: i for i, a in enumerate(data["axes"])}
    # Hma.sublists enumerates recursively from the final axis, matching binary bit reversal.
    def order(row):
        return sum(1 << (len(data["axes"]) - 1 - indices[a]) for a in row["axes"])
    return [{"id": sum(1 << indices[a] for a in p["axes"]),
             "profile": [len(p["axes"]), -p["rho"][1], sum(resources[indices[a]] for a in p["axes"])]}
            for p in sorted(result["minimal"], key=order)]


def run_hma(binary: Path, args: list[str], transcript) -> dict:
    cases = {}
    for name in ["X", "D", "E-empty", "E-singleton", "arena", "tie", "typed-weighted", "empty-universe"]:
        source = online.load_line((ROOT / "solver" / "instances" / (name + ".json")).read_bytes())
        source = certified.normalized(source)
        result = solve.solve(source)
        resources = [1] * len(source["axes"])
        weights, seq, epoch = [1, 1, 1], 1, 0
        points = hma_points(source, result, resources)
        cumulative = len(points) ** 2
        with native(binary, args, transcript) as process:
            reply = process.exchange({"op": "hma_start", "input": online.encode(source),
                                      "resources": resources, "weights": weights})
            verify.need(reply["ok"], "HMA Pareto start rejected: " + reply.get("error", ""))
            receipt = reply["observation"]
            online.decode_record(source, receipt["hma_observation"], 1, 0)
            original = receipt["hma_result"]
            check(receipt, points, weights, seq, epoch, cumulative, 0, cumulative,
                  original, resources, receipt["hma_observation"])
            for new_weights in [[0, 0, 0], [0, 1, 0], [0, 0, 1]]:
                reply = process.exchange({"op": "weights", "seq": seq, "epoch": epoch, "weights": new_weights})
                verify.need(reply["ok"], "HMA parameter update rejected")
                weights, seq = new_weights, seq + 1
                check(reply["observation"], points, weights, seq, epoch, 0, 0, cumulative, original, resources)
            new_resources = [9] + resources[1:] if resources else []
            current = hma_points(source, result, new_resources)
            needed, reused = pair_work(points, current)
            reply = process.exchange({"op": "resources", "seq": seq, "epoch": epoch, "resources": new_resources})
            verify.need(reply["ok"], "HMA resource update rejected")
            points, resources, seq, cumulative = current, new_resources, seq + 1, cumulative + needed
            check(reply["observation"], points, weights, seq, epoch, needed, reused, cumulative, original, resources)
            if name == "X":
                verify.need(reply["observation"]["selected"]["id"] == 4, "X resource-sensitive choice missing")
            before = copy.deepcopy(source)
            if source["contract"]:
                source["contract"] = source["contract"][:-1]
            result = solve.solve(source)
            current = hma_points(source, result, resources)
            needed, reused = pair_work(points, current)
            reply = process.exchange({"op": "hma_advance", "seq": seq, "epoch": epoch,
                                      "input": online.encode(source), "resources": resources})
            verify.need(reply["ok"], "HMA data update rejected: " + reply.get("error", ""))
            receipt = reply["observation"]
            online.decode_record(source, receipt["hma_observation"], 2, 0)
            original = receipt["hma_result"]
            points, seq, cumulative = current, seq + 1, cumulative + needed
            check(receipt, points, weights, seq, epoch, needed, reused, cumulative,
                  original, resources, receipt["hma_observation"])
            cases[name] = {"prefixes": 6, "initial_rows": len(before["contract"]),
                           "final_rows": len(source["contract"]), "frontier": receipt["frontier"],
                           "selected": receipt["selected"], "output_sha256": process.output_digest.hexdigest(),
                           "cumulative_comparisons": cumulative}
    return cases


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--lean-dir", default=os.environ.get("HMA_BUILD_DIR"))
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    try:
        with tempfile.TemporaryDirectory(prefix="hma-pareto-") as temp:
            temporary = Path(temp)
            shared = os.environ.get("HMA_REASONING_BINARY")
            if shared:
                binary, mode = Path(shared), ["pareto"]
            else:
                build = Path(args.lean_dir) if args.lean_dir else temporary / "proof"
                if not args.lean_dir:
                    cold_build(build, args.lean)
                binary, mode = build_binary(build, args.lean, temporary), []
            first_path, second_path = temporary / "first.jsonl", temporary / "second.jsonl"
            with first_path.open("wb") as transcript:
                first = {"generic": run_generic(binary, mode, transcript), "hma": run_hma(binary, mode, transcript)}
            with second_path.open("wb") as transcript:
                second = {"generic": run_generic(binary, mode, transcript), "hma": run_hma(binary, mode, transcript)}
            verify.need(first_path.read_bytes() == second_path.read_bytes(),
                        "Pareto raw transcript bytes differ across fresh processes")
            verify.need(canonical(first) == canonical(second), "Pareto receipts differ across fresh processes")
            report = {"schema": 1, "engine": "fixed-persistent-Lean-Pareto",
                      "two_process_bytes": "EXACT", **first}
            path = ROOT / "solver" / "results" / "pareto.json"
            if args.record:
                path.write_text(json.dumps(report, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
            else:
                verify.need(path.exists() and path.read_text() == json.dumps(report, ensure_ascii=False,
                    sort_keys=True, indent=2) + "\n", "recorded Pareto receipts are absent or stale")
            prefixes = report["generic"]["prefixes"] + sum(c["prefixes"] for c in report["hma"].values())
            print(f"PARETO GATE PASS: {prefixes} online prefixes; original-HMA profiles, complete frontiers, "
                  "all-parameter linear regions, unsupported Pareto points, resurrection, exact incremental comparisons, atomic refusals, "
                  "latent output controls, fresh-process raw bytes EXACT")
        return 0
    except (verify.Rejected, OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print("PARETO GATE REJECTED: " + str(error))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
