#!/usr/bin/env python3
"""Check solver JSON against executable views proved equal to Hma's definitions.

The input decoder is independent of solve.py. A fresh Lean program embeds the
input table, imports Hma and FiniteCheck, and computes every subset's liveness,
engaged edges, rho, sufficiency, minimality, and highest status. The finite
minimal/highest views are linked to the original predicates by kernel-checked
lemmas in FiniteCheck. This is executable agreement, not a proof of Python.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
from typing import Any


ROOT = Path(__file__).resolve().parent.parent


class Rejected(ValueError):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def unique_object(items: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in items:
        need(key not in result, f"duplicate JSON key: {key!r}")
        result[key] = value
    return result


def no_float(value: str) -> None:
    raise Rejected(f"non-integer JSON number: {value}")


def read_json(path: str | Path) -> Any:
    return json.loads(Path(path).read_text(encoding="utf-8"),
                      object_pairs_hook=unique_object,
                      parse_float=no_float, parse_constant=no_float)


def canonical(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, sort_keys=True,
                      separators=(",", ":"), allow_nan=False) + "\n"


def obj(value: Any, keys: set[str], label: str) -> None:
    need(type(value) is dict and set(value) == keys, f"{label}: wrong object fields")


def seq(value: Any, label: str) -> list[Any]:
    need(type(value) is list, f"{label}: expected array")
    return value


def name(value: Any) -> str:
    need(type(value) is str and bool(value), "names must be nonempty strings")
    try:
        value.encode("utf-8")
    except UnicodeEncodeError as error:
        raise Rejected("invalid Unicode surrogate") from error
    return value


def label(value: Any) -> str:
    """Injective equality label, independent of the solver's integer encoding."""
    need(value is None or type(value) in (bool, int, str), "invalid finite scalar")
    if type(value) is str:
        try:
            value.encode("utf-8")
        except UnicodeEncodeError as error:
            raise Rejected("invalid Unicode surrogate") from error
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"))


def decode(source: Any) -> dict[str, Any]:
    obj(source, {"schema", "name", "axes", "components", "contract", "hyperedges"}, "input")
    need(type(source["schema"]) is int and source["schema"] == 1, "unsupported schema")
    title = name(source["name"])
    axes = seq(source["axes"], "axes")
    axis_names: list[str] = []
    domains: list[set[str]] = []
    for axis in axes:
        obj(axis, {"name", "values"}, "axis")
        axis_names.append(name(axis["name"]))
        values = [label(x) for x in seq(axis["values"], "axis values")]
        need(len(set(values)) == len(values), "duplicate axis value")
        domains.append(set(values))
    need(len(set(axis_names)) == len(axis_names), "duplicate axis name")
    comp_names = [name(x) for x in seq(source["components"], "components")]
    need(len(set(comp_names)) == len(comp_names), "duplicate component name")
    axis_indices = sorted(range(len(axes)), key=axis_names.__getitem__)
    comp_indices = sorted(range(len(comp_names)), key=comp_names.__getitem__)
    sorted_axes = [axis_names[i] for i in axis_indices]
    sorted_comps = [comp_names[i] for i in comp_indices]
    codes: dict[str, int] = {}

    def code(key: str) -> int:
        if key not in codes:
            codes[key] = len(codes) + 1
        return codes[key]

    for domain in domains:
        for key in sorted(domain):
            code(key)

    rows: list[tuple[list[int], list[int]]] = []
    seen: set[tuple[str, ...]] = set()
    for row in seq(source["contract"], "contract"):
        obj(row, {"axes", "behavior"}, "row")
        x = [label(v) for v in seq(row["axes"], "configuration")]
        y = [label(v) for v in seq(row["behavior"], "behavior")]
        need(len(x) == len(axes) and len(y) == len(comp_names), "incomplete table row")
        need(all(x[i] in domains[i] for i in range(len(axes))), "value outside declared range")
        key = tuple(x)
        need(key not in seen, "duplicate configuration")
        seen.add(key)
        rows.append(([code(x[i]) for i in axis_indices], [code(y[i]) for i in comp_indices]))
    comp_map = {value: i for i, value in enumerate(sorted_comps)}
    edges: list[tuple[list[int], int]] = []
    edge_seen: set[tuple[int, ...]] = set()
    for edge in seq(source["hyperedges"], "hyperedges"):
        obj(edge, {"components", "weight"}, "edge")
        members = [name(x) for x in seq(edge["components"], "edge members")]
        need(len(set(members)) == len(members), "duplicate edge member")
        need(all(x in comp_map for x in members), "unknown edge member")
        ids = sorted(comp_map[x] for x in members)
        need(tuple(ids) not in edge_seen, "duplicate edge set")
        edge_seen.add(tuple(ids))
        weight = edge["weight"]
        need(type(weight) is int and weight >= 0, "weight is not a natural number")
        need(len(ids) < 2 or weight > 0, "nonpositive interacting weight")
        edges.append((ids, weight))
    edges.sort()
    # Membership in the contract is extensional. Round-robin across behavior
    # groups to avoid a long constant prefix in existential witness searches.
    # Every input row occurs exactly once; only search order changes.
    groups: dict[tuple[int, ...], list[tuple[list[int], list[int]]]] = {}
    for row in sorted(rows, key=lambda row: (row[1], row[0])):
        groups.setdefault(tuple(row[1]), []).append(row)
    rows = [row for _, _, row in sorted(
        (i, behavior, row) for behavior, group in groups.items() for i, row in enumerate(group))]
    return {"name": title, "axes": sorted_axes, "components": sorted_comps,
            "rows": rows, "edges": edges, "codes": codes,
            "domains": [domains[i] for i in axis_indices]}


def lean_list(values: list[int]) -> str:
    return "[" + ",".join(map(str, values)) + "]"


def lean_source(data: dict[str, Any], control: str | None = None) -> str:
    n, m = len(data["axes"]), len(data["components"])
    rows = ",\n  ".join(f"(#{lean_list(x)},#{lean_list(y)})" for x, y in data["rows"])
    edges = "[" + ",".join(lean_list(ids) for ids, _ in data["edges"]) + "]"
    weight = "".join(f"if e = {lean_list(ids)} then {w} else " for ids, w in data["edges"]) + "0"
    if not data["edges"]:
        positivity = "intro e he _; exact (List.not_mem_nil he).elim"
    else:
        positivity = ("intro e he hs\n    "
                      "simp only [List.mem_cons, List.mem_nil_iff, or_false] at he\n    "
                      "rcases he with " + " | ".join("rfl" for _ in data["edges"]) +
                      "\n    all_goals simp_all")
    control_import = ""
    control_definition = ""
    control_check = ""
    if control is not None:
        reference = {"X": ("instx", ["p", "q", "r", "s"]),
                     "D": ("instd", ["p", "q"]),
                     "E-empty": ("inste1", ["p", "q"]),
                     "E-singleton": ("inste2", ["p", "q"])}
        need(control in reference, "unknown standing control")
        inst, components = reference[control]
        need(data["axes"] == ["a", "b", "c"] and data["components"] == components,
             "standing control axis/component declarations changed")
        need(data["domains"] == [{"false", "true"}] * 3 and data["edges"] == [([0, 1], 1)],
             "standing control domains/hyperedges changed")
        false, true = data["codes"]["false"], data["codes"]["true"]
        control_import = "import Controls\n"
        control_definition = f'''
def boolCode (value : Bool) : Nat := if value then {true} else {false}

def referenceRows : List (List Nat × List Nat) :=
  Ctl.{inst}.contract.map (fun x =>
    ((List.ofFn x).map boolCode, (List.ofFn (Ctl.{inst}.beh x)).map boolCode))

def suppliedRows : List (List Nat × List Nat) :=
  raw.toList.map (fun row => (row.1.toList, row.2.toList))
'''
        control_check = '''  if !(decide ((∀ row ∈ suppliedRows, row ∈ referenceRows) ∧
      (∀ row ∈ referenceRows, row ∈ suppliedRows))) then
    throw (IO.userError "standing fixture disagrees with Controls.lean")
'''
    return f'''import FiniteCheck
import Std.Data.HashMap
{control_import}

open Hma HmaCheck
set_option maxRecDepth 10000
set_option maxHeartbeats 0

abbrev Axis := Fin {n}
abbrev Component := Fin {m}

def raw : Array (Array Nat × Array Nat) := #[
  {rows}]
{control_definition}

def behavior : Std.HashMap (List Nat) (Array Nat) :=
  Std.HashMap.ofList (raw.toList.map (fun row => (row.1.toList, row.2)))

def input : Inst Axis Nat Component Nat where
  axes := List.finRange {n}
  axesnodup := by decide
  axescomplete := by decide
  comps := List.finRange {m}
  contract := raw.toList.map (fun row a => (row.1[a.val]?).getD 0)
  beh := fun x b => ((behavior.getD (List.ofFn x) #[])[b.val]?).getD 0
  edges := {edges}
  weight := fun e => {weight}
  weightpos := by
    {positivity}

def numbers (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def groups (xs : List (List Nat)) : String :=
  "[" ++ String.intercalate "," (xs.map numbers) ++ "]"

def main : IO Unit := do
{control_check}  let rows := table input
  let full := snapshot input allaxes
  for (axes, value) in rows do
    let sufficient := decide (value.measure.1 = full.measure.1)
    let minimal := decide (tableMinimal input rows full.measure.1 axes value)
    let highest := decide (tableHighest input rows full.measure.1 axes value)
    IO.println ("{{\\"axes\\":" ++ numbers (axes.map Fin.val) ++
      ",\\"live\\":" ++ numbers (value.live.map Fin.val) ++
      ",\\"edges\\":" ++ groups (value.edges.map (fun e => e.map Fin.val)) ++
      ",\\"rho\\":" ++ numbers [value.measure.1, value.measure.2] ++
      ",\\"sufficient\\":" ++ toString sufficient ++
      ",\\"minimal\\":" ++ toString minimal ++
      ",\\"highest\\":" ++ toString highest ++ "}}")
  let deadAxes := input.axes.map (fun a => toString (decide (dead input a)))
  IO.println ("{{\\"dead\\":[" ++ String.intercalate "," deadAxes ++ "]}}")
'''


def lean_rows(data: dict[str, Any], *, build_dir: str | Path | None = None,
              lean: str | None = None, timeout: int = 600,
              control: str | None = None) -> list[dict[str, Any]]:
    build = Path(build_dir or os.environ.get("HMA_BUILD_DIR", ROOT / "proof")).resolve()
    for module in (("Hma", "FiniteCheck", "Controls") if control else ("Hma", "FiniteCheck")):
        need((build / (module + ".olean")).is_file(), f"missing {module}.olean; run proof/check.sh")
    with tempfile.TemporaryDirectory(prefix="hma-lean-agreement-") as directory:
        source = Path(directory) / "Instance.lean"
        source.write_text(lean_source(data, control), encoding="utf-8")
        environment = dict(os.environ)
        environment["LEAN_PATH"] = str(build)
        executable = lean or os.environ.get("LEAN", "lean")
        deadline = time.monotonic() + timeout

        def run(command: list[str]) -> subprocess.CompletedProcess[str]:
            remaining = deadline - time.monotonic()
            need(remaining > 0, "Lean agreement time budget exhausted")
            process = subprocess.run(command, cwd=directory, env=environment, text=True,
                                     capture_output=True, timeout=remaining, check=False)
            need(process.returncode == 0, "Lean checker command failed:\n" +
                 " ".join(command) + "\n" + process.stdout + process.stderr)
            return process

        if len(data["rows"]) > 32:
            # This is ordinary execution of Lean-generated code, never a proof
            # tactic. The same definitions and bridge are used in both modes.
            prefix = run([executable, "--print-prefix"]).stdout.strip()
            leanc = str(Path(prefix) / "bin" / "leanc")
            generated: list[str] = []
            for module in ("Hma", "FiniteCheck"):
                cfile = Path(directory) / (module + ".c")
                run([executable, "-DwarningAsError=true", "--root=" + str(ROOT / "proof"),
                     "-c", str(cfile), str(ROOT / "proof" / (module + ".lean"))])
                generated.append(str(cfile))
            cfile = Path(directory) / "Instance.c"
            run([executable, "-DwarningAsError=true", "--root=" + directory,
                 "-c", str(cfile), str(source)])
            binary = str(Path(directory) / "checker")
            run([leanc, "-O2", "-o", binary, str(cfile), *generated])
            result = run([binary])
        else:
            result = run([executable, "-DwarningAsError=true", "--run", str(source)])
        need(result.returncode == 0, "Lean definition check failed:\n" + result.stdout + result.stderr)
        need(not result.stderr, "unexpected Lean diagnostics:\n" + result.stderr)
        try:
            return [json.loads(line, object_pairs_hook=unique_object,
                               parse_float=no_float, parse_constant=no_float)
                    for line in result.stdout.splitlines()]
        except (ValueError, TypeError) as error:
            raise Rejected("Lean checker returned malformed evidence") from error


def compute_expected(instance: Any, *, build_dir: str | Path | None = None,
                     lean: str | None = None, timeout: int = 600,
                     control: str | None = None) -> dict[str, Any]:
    """Run Lean once and decode its complete definition-derived table.

    Callers may reuse this returned value to challenge many corrupt outputs for
    this same instance. There is no disk cache or trusted historical receipt.
    """
    if isinstance(instance, (str, Path)):
        instance = read_json(instance)
    data = decode(instance)
    records = lean_rows(data, build_dir=build_dir, lean=lean, timeout=timeout, control=control)
    axes, comps, edges = data["axes"], data["components"], data["edges"]
    nsubsets = 1 << len(axes)
    need(len(records) == nsubsets + 1, "Lean did not enumerate the full subset space")
    final = records.pop()
    obj(final, {"dead"}, "Lean dead-axis record")
    need(type(final["dead"]) is list and len(final["dead"]) == len(axes) and
         all(type(x) is bool for x in final["dead"]), "malformed Lean dead-axis record")
    by_mask: dict[int, dict[str, Any]] = {}
    weights = {tuple(ids): weight for ids, weight in edges}
    for record in records:
        obj(record, {"axes", "live", "edges", "rho", "sufficient", "minimal", "highest"},
            "Lean subset record")
        ids = record["axes"]
        need(type(ids) is list and all(type(i) is int and 0 <= i < len(axes) for i in ids),
             "malformed Lean axis set")
        need(ids == sorted(set(ids)), "noncanonical Lean axis set")
        mask = sum(1 << i for i in ids)
        need(mask not in by_mask, "duplicate Lean subset")
        live = record["live"]
        need(type(live) is list and all(type(i) is int and 0 <= i < len(comps) for i in live),
             "malformed Lean live set")
        need(live == sorted(set(live)), "noncanonical Lean live set")
        engaged = record["edges"]
        need(type(engaged) is list, "malformed Lean edge list")
        need(all(type(e) is list and all(type(i) is int for i in e) and tuple(e) in weights
                 for e in engaged), "unknown Lean edge")
        need(engaged == sorted(engaged) and len(set(map(tuple, engaged))) == len(engaged),
             "noncanonical Lean edge list")
        measure = record["rho"]
        need(type(measure) is list and len(measure) == 2 and
             all(type(x) is int and x >= 0 for x in measure), "malformed Lean measure")
        for field in ("sufficient", "minimal", "highest"):
            need(type(record[field]) is bool, f"malformed Lean {field} predicate")
        by_mask[mask] = {
            "axes": [axes[i] for i in ids], "live": [comps[i] for i in live],
            "engaged": [{"components": [comps[i] for i in edge], "weight": weights[tuple(edge)]}
                        for edge in engaged], "rho": measure,
            "sufficient": record["sufficient"], "minimal": record["minimal"],
            "highest": record["highest"],
        }
    need(set(by_mask) == set(range(nsubsets)), "Lean subset enumeration is incomplete")
    subsets = [by_mask[mask] for mask in range(nsubsets)]
    minimal = sorted((row for row in subsets if row["minimal"]), key=lambda row: row["axes"])
    highest = sorted((row for row in subsets if row["highest"]), key=lambda row: row["axes"])
    need(bool(highest), "Lean reported no highest minimal set")
    chosen = highest[0]
    full = subsets[-1]
    dispositions = [
        {"axis": axis,
         "membership": "chosen" if axis in chosen["axes"] else
                       "alternative" if any(axis in row["axes"] for row in minimal) else "none",
         "emergent_dead": final["dead"][i]}
        for i, axis in enumerate(axes)
    ]
    return {
        "schema": 1, "name": data["name"], "axes": axes, "components": comps,
        "chosen": {"axes": chosen["axes"], "rho": chosen["rho"]},
        "full": {"mu": full["rho"][0], "live": full["live"], "engaged": full["engaged"]},
        "minimal": [{"axes": row["axes"], "rho": row["rho"]} for row in minimal],
        "dispositions": dispositions,
        "counts": {"axes": len(axes), "components": len(comps), "contract_rows": len(data["rows"]),
                   "hyperedges": len(edges), "subsets": nsubsets,
                   "row_pairs": len(data["rows"]) * (len(data["rows"]) - 1) // 2},
        "subsets": subsets,
    }


def compare_result(expected: Any, actual: Any) -> None:
    """Reject any missing, extra, wrongly typed, or semantically wrong field."""
    if canonical(expected) != canonical(actual):
        raise Rejected("solver output disagrees with the imported Lean definitions or output contract")


def check(instance: str | Path, output: str | Path, *, build_dir: str | Path | None = None,
          lean: str | None = None, timeout: int = 600, control: str | None = None) -> dict[str, Any]:
    actual = read_json(output)
    expected = compute_expected(instance, build_dir=build_dir, lean=lean, timeout=timeout, control=control)
    compare_result(expected, actual)
    return expected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("instance")
    parser.add_argument("output")
    parser.add_argument("--lean-dir")
    parser.add_argument("--lean")
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument("--control", choices=["X", "D", "E-empty", "E-singleton"])
    parser.add_argument("--emit", help="write definition-derived expected JSON after agreement")
    args = parser.parse_args()
    try:
        expected = check(args.instance, args.output, build_dir=args.lean_dir,
                         lean=args.lean, timeout=args.timeout, control=args.control)
        if args.emit:
            Path(args.emit).write_text(canonical(expected), encoding="utf-8")
        print(f"LEAN AGREEMENT PASS: {expected['name']}; {expected['counts']['subsets']} subsets; "
              f"{len(expected['minimal'])} minimal; chosen={expected['chosen']['axes']}")
    except (Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Rejected: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
