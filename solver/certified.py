#!/usr/bin/env python3
"""Execute the proved materialized Lean engine and complete result renderer.

The JSON adapter supplies finite inputs. Every carried Lean state has its
Valid proof, and a result is exposed only through CertifiedReplay.finish.
Two independent executions must produce identical bytes. The JSON adapter,
Lean compiler, and runtime are execution boundaries, not kernel theorems.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any

import verify

ROOT = Path(__file__).resolve().parents[1]
MODULES = ("Hma", "FiniteCheck", "Incremental", "IncrementalCounts", "Qualification", "FiniteFrontier",
           "ExecutableClosure", "HypergraphIncremental", "HmaGraph", "ExecutableWitness",
           "CertifiedTable", "CertifiedReplay")


def normalized(source: Any) -> dict:
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
    data["contract"].sort(key=lambda r: tuple(map(verify.label, r["axes"])))
    data["hyperedges"] = sorted(({"components": sorted(e["components"]), "weight": e["weight"]}
                                 for e in data["hyperedges"]), key=lambda e: e["components"])
    return data


def key(vector: list) -> tuple[str, ...]:
    return tuple(map(verify.label, vector))


def inputs(campaign: Any) -> list[dict]:
    """Strict journal replay, independent of the Python materializer."""
    verify.obj(campaign, {"schema", "initial", "events"}, "campaign")
    verify.need(type(campaign["schema"]) is int and campaign["schema"] == 1, "campaign schema")
    states = [normalized(campaign["initial"])]
    epoch = 0
    payloads = {"append": "rows", "remove": "axes", "replace": "rows",
                "edges": "hyperedges", "rebase": "instance"}
    for seq, event in enumerate(verify.seq(campaign["events"], "events"), 1):
        verify.need(type(event) is dict and type(event.get("op")) is str and
                    event["op"] in payloads, "unknown event")
        op = event["op"]
        verify.obj(event, {"seq", "epoch", "op", payloads[op]}, "event")
        verify.need(type(event["seq"]) is int and event["seq"] == seq and
                    type(event["epoch"]) is int and event["epoch"] == epoch, "event clock mismatch")
        if op == "rebase":
            states.append(normalized(event["instance"]))
            epoch += 1
            continue
        candidate = copy.deepcopy(states[-1])
        previous = {key(r["axes"]): r for r in candidate["contract"]}
        if op == "edges":
            candidate["hyperedges"] = copy.deepcopy(event["hyperedges"])
        elif op == "remove":
            vectors = verify.seq(event["axes"], "withdrawn configurations")
            ids = [key(verify.seq(v, "configuration")) for v in vectors]
            verify.need(len(set(ids)) == len(ids) and all(k in previous for k in ids),
                        "duplicate or absent withdrawal")
            candidate["contract"] = [r for r in candidate["contract"] if key(r["axes"]) not in ids]
        else:
            incoming = copy.deepcopy(candidate)
            incoming["contract"] = event["rows"]
            rows = normalized(incoming)["contract"]
            if op == "append":
                verify.need(all(key(r["axes"]) not in previous for r in rows), "duplicate append")
                candidate["contract"].extend(rows)
            else:
                verify.need(all(key(r["axes"]) in previous for r in rows), "absent replacement")
                replacement = {key(r["axes"]): r for r in rows}
                candidate["contract"] = [replacement.get(key(r["axes"]), r)
                                         for r in candidate["contract"]]
        states.append(normalized(candidate))
    return states


def encode(states: list[dict]) -> list[dict]:
    # One injective value code across the entire execution preserves identities
    # when an observation changes or a removed configuration returns later.
    labels = set()
    for state in states:
        labels.update(verify.label(v) for a in state["axes"] for v in a["values"])
        labels.update(verify.label(v) for r in state["contract"] for v in r["axes"] + r["behavior"])
    codes = {label: i + 1 for i, label in enumerate(sorted(labels))}
    encoded = []
    for state in states:
        data = verify.decode(state)
        data["rows"] = [([codes[verify.label(v)] for v in r["axes"]],
                         [codes[verify.label(v)] for v in r["behavior"]]) for r in state["contract"]]
        encoded.append(data)
    return encoded


def declaration(index: int, data: dict) -> str:
    n, m = len(data["axes"]), len(data["components"])
    rows = ",\n".join(f"(#{verify.lean_list(x)},#{verify.lean_list(y)})" for x, y in data["rows"])
    edges = "[" + ",".join(verify.lean_list(e) for e, _ in data["edges"]) + "]"
    weight = "".join(f"if e = {verify.lean_list(e)} then {w} else " for e, w in data["edges"]) + "0"
    positivity = ("intro e he _; exact (List.not_mem_nil he).elim" if not data["edges"] else
        "intro e he hs\n    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he\n    rcases he with " +
        " | ".join("rfl" for _ in data["edges"]) + "\n    all_goals simp_all")
    return f'''
def raw{index} : Array (Array Nat × Array Nat) := #[{rows}]
def behavior{index} : Std.HashMap (List Nat) (Array Nat) :=
  Std.HashMap.ofList (raw{index}.toList.map (fun r => (r.1.toList, r.2)))
def input{index} : Hma.Inst (Fin {n}) Nat (Fin {m}) Nat where
  axes := List.finRange {n}
  axesnodup := by decide
  axescomplete := by decide
  comps := List.finRange {m}
  contract := raw{index}.toList.map (fun r a => (r.1[a.val]?).getD 0)
  beh := fun x b => ((behavior{index}.getD (List.ofFn x) #[])[b.val]?).getD 0
  edges := {edges}
  weight := fun e => {weight}
  weightpos := by
    {positivity}
'''


PRINT = r'''
def numbers (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def groups (xs : List (List Nat)) : String :=
  "[" ++ String.intercalate "," (xs.map numbers) ++ "]"
def snapshotJson {m : Nat} (s : HmaCheck.Snapshot (Fin m)) : String :=
  "{\"live\":" ++ numbers (s.live.map Fin.val) ++
  ",\"edges\":" ++ groups (s.edges.map (fun e => e.map Fin.val)) ++
  ",\"rho\":" ++ numbers [s.measure.1, s.measure.2] ++ "}"
def rowJson {n m : Nat} (r : HmaCertified.Classified (Fin n) (Fin m)) : String :=
  "{\"axes\":" ++ numbers (r.axes.map Fin.val) ++
  ",\"live\":" ++ numbers (r.value.live.map Fin.val) ++
  ",\"edges\":" ++ groups (r.value.edges.map (fun e => e.map Fin.val)) ++
  ",\"rho\":" ++ numbers [r.value.measure.1, r.value.measure.2] ++
  ",\"sufficient\":" ++ toString r.sufficient ++
  ",\"minimal\":" ++ toString r.minimal ++
  ",\"highest\":" ++ toString r.highest ++ "}"
def dispositionJson {n : Nat} (d : HmaCertified.Disposition (Fin n)) : String :=
  let tag := match d.membership with
    | .chosen => "chosen" | .alternative => "alternative" | .none => "none"
  "{\"axis\":" ++ toString d.axis.val ++ ",\"membership\":\"" ++ tag ++
  "\",\"emergent_dead\":" ++ toString d.emergentDead ++ "}"
def resultJson {n m : Nat} (r : HmaCertified.Rendered (Fin n) (Fin m)) : String :=
  let chosen := match r.chosen with
    | none => "null" | some xs => numbers (xs.map Fin.val)
  "{\"full\":" ++ snapshotJson r.full ++
  ",\"subsets\":[" ++ String.intercalate "," (r.subsets.map rowJson) ++ "]" ++
  ",\"minimal\":" ++ groups (r.minimal.map (fun xs => xs.map Fin.val)) ++
  ",\"highest\":" ++ groups (r.highest.map (fun xs => xs.map Fin.val)) ++
  ",\"chosen\":" ++ chosen ++
  ",\"dispositions\":[" ++ String.intercalate "," (r.dispositions.map dispositionJson) ++ "]}"
def emit {n m : Nat} (prefixIndex : Nat) (I : Hma.Inst (Fin n) Nat (Fin m) Nat)
    (session : HmaReplay.Session I) (insertions removals : Nat) : IO Unit := do
  let some output := HmaReplay.finish I session.state HmaCertified.finLexPrefer
    | throw (IO.userError "carried rows do not reconstruct the requested instance")
  let mut cells : List String := []
  for D in Hma.sublists I.axes do
    for b in I.comps do
      let count := HmaExecutable.read session.state.val.hist (D,b)
      if count > 0 then
        cells := ("[" ++ numbers (D.map Fin.val) ++ "," ++ toString b.val ++
          "," ++ toString count ++ "]") :: cells
  let rows := session.state.val.rows.map (fun x =>
    "[" ++ numbers (List.ofFn x) ++ "," ++ numbers (List.ofFn (I.beh x)) ++ "]")
  let support := (Hma.sublists I.axes).map (fun S =>
    "[" ++ numbers (S.map Fin.val) ++ "," ++ numbers (I.comps.map (fun b =>
      HmaReplay.occupancy I session.state.val (HmaCheck.axisSet S) b)) ++ "]")
  IO.println ("{\"prefix\":" ++ toString prefixIndex ++
    ",\"next_seq\":" ++ toString session.nextSeq ++ ",\"epoch\":" ++ toString session.epoch ++
    ",\"pair_additions\":" ++ toString insertions ++ ",\"pair_removals\":" ++ toString removals ++
    ",\"rows\":[" ++ String.intercalate "," rows ++ "]" ++
    ",\"cells\":[" ++ String.intercalate "," cells.reverse ++ "]" ++
    ",\"support\":[" ++ String.intercalate "," support ++ "]" ++
    ",\"result\":" ++ resultJson output.value ++ "}")
'''


def source(campaign: dict, data: list[dict], reconstruct_at: int | None = None) -> str:
    definitions = [declaration(i, item) for i, item in enumerate(data)]
    initial_work = len(data[0]["rows"]) * (len(data[0]["rows"]) - 1) // 2
    body = ["  let session0 : HmaReplay.Session input0 := ⟨HmaReplay.start input0 (by decide), 1, 0⟩",
            f"  emit 0 input0 session0 {initial_work} 0"]
    for i, event in enumerate(campaign["events"], 1):
        if reconstruct_at == i - 1:
            body.append(f"  let session{i-1} : HmaReplay.Session input{i-1} := "
                        f"⟨HmaReplay.start input{i-1} (by decide), session{i-1}.nextSeq, session{i-1}.epoch⟩")
        if event["op"] == "rebase":
            count = len(data[i]["rows"]) * (len(data[i]["rows"]) - 1) // 2
            body.extend([
                f"  let some session{i} := HmaReplay.rebase input{i-1} input{i} (by decide)",
                f"    session{i-1} {event['seq']} {event['epoch']}",
                '    | throw (IO.userError "rebase clock mismatch")',
                f"  emit {i} input{i} session{i} {count} 0"])
        else:
            body.extend([
                f"  let some (session{i}, additions{i}, removals{i}) := HmaReplay.advance input{i-1} input{i}",
                f"    session{i-1} {event['seq']} {event['epoch']}",
                '    | throw (IO.userError "uncertified incremental transition")',
                f"  emit {i} input{i} session{i} additions{i} removals{i}"])
    return ("import CertifiedReplay\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" +
            PRINT + "\n".join(definitions) + "\ndef main : IO Unit := do\n" + "\n".join(body) + "\n")


class Executor:
    """One cold compiler-object set; fresh processes for each transcript."""
    def __init__(self, build: Path, lean: str, temporary: Path):
        self.build, self.lean, self.tmp = build.resolve(), lean, temporary.resolve()
        self.environment = dict(os.environ, LEAN_PATH=str(self.build))
        self.objects = []
        for module in MODULES:
            verify.need((self.build / (module + ".olean")).is_file(), f"missing cold-built {module}.olean")
        prefix = self.command([lean, "--print-prefix"]).stdout.strip()
        self.leanc = str(Path(prefix) / "bin/leanc")
        for module in MODULES:
            cfile, obj = self.tmp / (module + ".c"), self.tmp / (module + ".o")
            self.command([lean, "-DwarningAsError=true", "--root=" + str(ROOT / "proof"),
                          "-c", str(cfile), str(ROOT / "proof" / (module + ".lean"))])
            self.command([self.leanc, "-O2", "-c", "-o", str(obj), str(cfile)])
            self.objects.append(str(obj))

    def command(self, command: list[str], timeout: int = 600):
        process = subprocess.run(command, cwd=self.tmp, env=self.environment,
                                 text=True, capture_output=True, timeout=timeout)
        verify.need(process.returncode == 0 and not process.stderr,
                    "certified execution failed:\n" + " ".join(command) + "\n" +
                    process.stdout + process.stderr)
        return process

    def execute(self, campaign: dict, reconstruct_at: int | None = None) -> tuple[list[dict], dict]:
        states = inputs(campaign)
        data = encode(states)
        code = source(campaign, data, reconstruct_at)
        path, cfile, binary = self.tmp / "Campaign.lean", self.tmp / "Campaign.c", self.tmp / "campaign"
        path.write_text(code, encoding="utf-8")
        self.command([self.lean, "-DwarningAsError=true", "--root=" + str(self.tmp),
                      "-c", str(cfile), str(path)])
        self.command([self.leanc, "-O2", "-o", str(binary), str(cfile), *self.objects])
        executions = []
        for _ in range(2):
            process = subprocess.run([str(binary)], cwd=self.tmp, env=self.environment,
                                     capture_output=True, timeout=600)
            verify.need(process.returncode == 0 and not process.stderr,
                        "certified process failed: " + process.stderr.decode("utf-8", errors="replace"))
            executions.append(process.stdout)
        first, second = executions
        verify.need(first == second, "certified Lean processes differ byte-for-byte")
        records = [json.loads(line, object_pairs_hook=verify.unique_object,
                             parse_float=verify.no_float, parse_constant=verify.no_float)
                   for line in first.decode("utf-8").splitlines()]
        verify.need(len(records) == len(states), "missing or extra certified prefix")
        decoded = [decode_record(i, item, record) for i, (item, record) in enumerate(zip(data, records))]
        epoch = 0
        previous = {}
        for i, (state, receipt) in enumerate(zip(states, decoded)):
            rebuild = i == 0 or campaign["events"][i - 1]["op"] == "rebase"
            if i and rebuild:
                epoch += 1
            current = {key(r["axes"]): key(r["behavior"]) for r in state["contract"]}
            retained = 0 if rebuild else sum(previous.get(k) == value for k, value in current.items())
            pairs = lambda n: n * (n - 1) // 2
            additions = pairs(len(current)) - pairs(retained)
            removals = 0 if rebuild else pairs(len(previous)) - pairs(retained)
            verify.need(receipt["epoch"] == epoch, "certified epoch disagrees with journal")
            verify.need(receipt["pair_additions"] == additions and receipt["pair_removals"] == removals,
                        "certified pair work disagrees with independently replayed row changes")
            previous = current
        return decoded, {"source_sha256": hashlib.sha256(code.encode()).hexdigest(),
                         "execution_sha256": hashlib.sha256(first).hexdigest(),
                         "byte_exact": True}


def cold_build(build: Path, lean: str) -> None:
    """Build the backend dependency closure when used outside the full gate."""
    build.mkdir(parents=True)
    environment = dict(os.environ, LEAN_PATH=str(build.resolve()))
    for module in MODULES:
        path = build / (module + ".lean")
        path.write_bytes((ROOT / "proof" / path.name).read_bytes())
        result = subprocess.run([lean, "-DwarningAsError=true", "-o", module + ".olean", path.name],
                                cwd=build, env=environment, text=True, capture_output=True, timeout=120)
        verify.need(result.returncode == 0 and not result.stderr,
                    "certified dependency did not compile: " + module + "\n" + result.stdout + result.stderr)


def decode_record(index: int, data: dict, record: dict) -> dict:
    verify.obj(record, {"prefix", "next_seq", "epoch", "pair_additions", "pair_removals",
                        "rows", "cells", "support", "result"}, "certified receipt")
    for field in ("prefix", "next_seq", "epoch", "pair_additions", "pair_removals"):
        verify.need(type(record[field]) is int and record[field] >= 0, "malformed certified counter")
    verify.need(record["prefix"] == index and record["next_seq"] == index + 1, "certified sequence mismatch")
    verify.need(verify.canonical(sorted(record["rows"])) ==
                verify.canonical(sorted([[x, y] for x, y in data["rows"]])), "certified rows disagree with input")
    result = record["result"]
    verify.obj(result, {"full", "subsets", "minimal", "highest", "chosen", "dispositions"}, "certified result")
    dead = [d["emergent_dead"] for d in result["dispositions"]]
    decoded = verify.result_from_records(data, result["subsets"] + [{"dead": dead}])
    ids = {name: i for i, name in enumerate(data["axes"])}
    verify.need(verify.canonical(result["chosen"]) == verify.canonical([ids[a] for a in decoded["chosen"]["axes"]]),
                "Lean choice adapter mismatch")
    verify.need(verify.canonical(sorted(result["minimal"])) ==
                verify.canonical(sorted([[ids[a] for a in r["axes"]] for r in decoded["minimal"]])),
                "Lean minimal-list adapter mismatch")
    verify.need(verify.canonical(sorted(result["highest"])) ==
                verify.canonical(sorted([[ids[a] for a in r["axes"]]
                for r in decoded["subsets"] if r["highest"]])), "Lean highest-list adapter mismatch")
    expected_dispositions = [{**d, "axis": ids[d["axis"]]} for d in decoded["dispositions"]]
    verify.need(verify.canonical(result["dispositions"]) == verify.canonical(expected_dispositions),
                "Lean disposition adapter mismatch")
    full = next(r for r in result["subsets"] if len(r["axes"]) == len(data["axes"]))
    verify.need(verify.canonical(result["full"]) ==
                verify.canonical({k: full[k] for k in ("live", "edges", "rho")}), "Lean full-table adapter mismatch")
    cells = []
    for cell in verify.seq(record["cells"], "certified support cells"):
        verify.need(type(cell) is list and len(cell) == 3, "malformed certified support cell")
        axes, b, count = cell
        verify.need(type(axes) is list and all(type(a) is int and 0 <= a < len(data["axes"]) for a in axes)
                    and axes == sorted(set(axes)) and type(b) is int and 0 <= b < len(data["components"])
                    and type(count) is int and count > 0, "malformed certified support value")
        cells.append([sum(1 << a for a in axes), b, count])
    verify.need(len({(mask, b) for mask, b, _ in cells}) == len(cells), "duplicate certified support key")
    support = {}
    for entry in verify.seq(record["support"], "certified occupancy table"):
        verify.need(type(entry) is list and len(entry) == 2, "malformed certified occupancy row")
        axes, counts = entry
        verify.need(type(axes) is list and all(type(a) is int and 0 <= a < len(data["axes"]) for a in axes)
                    and axes == sorted(set(axes)), "malformed certified occupancy axes")
        mask = sum(1 << a for a in axes)
        verify.need(mask not in support and type(counts) is list and len(counts) == len(data["components"])
                    and all(type(count) is int and count >= 0 for count in counts), "malformed certified occupancy values")
        support[mask] = counts
    verify.need(set(support) == set(range(1 << len(data["axes"]))), "incomplete certified occupancy table")
    return {"prefix": index, "next_seq": record["next_seq"], "epoch": record["epoch"],
            "pair_additions": record["pair_additions"], "pair_removals": record["pair_removals"],
            "cells": sorted(cells), "support": [support[i] for i in range(len(support))], "result": decoded}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input")
    parser.add_argument("--campaign", action="store_true", help="input is a numbered event campaign")
    parser.add_argument("--lean-dir", default=os.environ.get("HMA_BUILD_DIR"))
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    args = parser.parse_args()
    try:
        data = verify.read_json(args.input)
        campaign = data if args.campaign else {"schema": 1, "initial": data, "events": []}
        with tempfile.TemporaryDirectory(prefix="hma-certified-") as tmp:
            build = Path(args.lean_dir) if args.lean_dir else Path(tmp) / "proof"
            if not args.lean_dir:
                cold_build(build, args.lean)
            executor = Executor(build, args.lean, Path(tmp))
            records, receipt = executor.execute(campaign)
        print(verify.canonical({"schema": 1, "observations": records, "execution": receipt}) if args.campaign
              else verify.canonical(records[0]["result"]), end="")
    except (verify.Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        print("Rejected: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
