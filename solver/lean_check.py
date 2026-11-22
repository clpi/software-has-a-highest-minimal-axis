"""Generate and kernel-check concrete solver-output claims against Hma.Inst."""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from model import EncodedTable, Table, encode_table


def _fin(index: int, size: int) -> str:
    return f"({index} : Fin {size})"


def _fin_list(indices: list[int] | tuple[int, ...], size: int) -> str:
    return "[" + ", ".join(_fin(i, size) for i in indices) + "]"


def _list_type(items: list[str]) -> str:
    return "[" + ", ".join(items) + "]"


def _nat_if_chain(values: tuple[int, ...], binder: str, size: int) -> str:
    if size == 0:
        return "0"
    expr = "0"
    for index in reversed(range(size)):
        value = values[index]
        expr = f"(if {binder}.val = {index} then {value} else {expr})"
    return expr


def _row_match(row: tuple[int, ...], axis_count: int) -> str:
    if axis_count == 0:
        return "true"
    return " && ".join(
        f"decide (x {_fin(i, axis_count)} = {value})"
        for i, value in enumerate(row)
    )


def _lean_source(table: Table, output: dict[str, Any]) -> str:
    encoded = encode_table(table)
    n = len(encoded.axis_names)
    m = len(encoded.component_names)
    axis_id = {name: i for i, name in enumerate(encoded.axis_names)}
    component_id = {name: i for i, name in enumerate(encoded.component_names)}
    rows = encoded.configurations
    behaviors = encoded.behaviors
    lines: list[str] = [
        "import Hma",
        "open Hma",
        "namespace SolverCheck",
        "",
        f"def axes : List (Fin {n}) := List.finRange {n}",
        f"def components : List (Fin {m}) := List.finRange {m}",
    ]

    for row_index, row in enumerate(rows):
        lines.append(
            f"def row{row_index} : Fin {n} → Nat := fun a => {_nat_if_chain(row, 'a', n)}"
        )
        lines.append(
            f"def rowMatch{row_index} (x : Fin {n} → Nat) : Bool := {_row_match(row, n)}"
        )
    lines.append("")
    rows_expr = _list_type([f"row{i}" for i in range(len(rows))])
    lines.append(f"def contract : List (Fin {n} → Nat) := {rows_expr}")

    if m == 0 or not rows:
        lines.extend([
            f"def behavior : (Fin {n} → Nat) → Fin {m} → Nat := fun _ _ => 0",
            "",
        ])
    else:
        behavior_expr = "0"
        for component_index in reversed(range(m)):
            row_expr = "0"
            for row_index in reversed(range(len(rows))):
                row_expr = (
                    f"(if rowMatch{row_index} x = true then {behaviors[row_index][component_index]} "
                    f"else {row_expr})"
                )
            behavior_expr = f"(if b.val = {component_index} then {row_expr} else {behavior_expr})"
        lines.extend([
            f"def behavior (x : Fin {n} → Nat) (b : Fin {m}) : Nat := {behavior_expr}",
            "",
        ])

    for edge_index, (edge, _weight) in enumerate(encoded.edges):
        lines.append(f"def edge{edge_index} : List (Fin {m}) := {_fin_list(edge, m)}")
    edge_names = [f"edge{i}" for i in range(len(encoded.edges))]
    lines.append(f"def edges : List (List (Fin {m})) := {_list_type(edge_names)}")
    weight_expr = "0"
    for edge_index in reversed(range(len(encoded.edges))):
        weight = encoded.edges[edge_index][1]
        weight_expr = f"(if e = edge{edge_index} then {weight} else {weight_expr})"
    lines.append(f"def edgeWeight (e : List (Fin {m})) : Nat := {weight_expr}")
    lines.extend([
        "",
        f"def inst : Hma.Inst (Fin {n}) Nat (Fin {m}) Nat where",
        "  axes := axes",
        "  axesnodup := by decide",
        "  axescomplete := by",
        "    intro a",
        "    apply (List.mem_ofFn).2",
        "    exact ⟨a, rfl⟩",
        "  comps := components",
        "  contract := contract",
        "  beh := behavior",
        "  edges := edges",
        "  weight := edgeWeight",
    ])
    if not encoded.edges:
        lines.append("  weightpos := by intro e he hlen; simp [edges] at he")
    else:
        lines.extend([
            "  weightpos := by",
            "    intro e he hlen",
            f"    have hcases : {(' ∨ '.join(f'e = edge{i}' for i in range(len(encoded.edges))))} := by",
            "      simpa [edges] using he",
            "    rcases hcases with " + " | ".join(f"h{i}" for i in range(len(encoded.edges))),
        ])
        for edge_index in range(len(encoded.edges)):
            lines.extend([
                "    · subst e",
                "      simp [edgeWeight, " + ", ".join(edge_names) + "]",
            ])
    lines.append("")

    for row_index, row in enumerate(rows):
        for component_index in range(m):
            lines.append(
                f"example : behavior row{row_index} {_fin(component_index, m)} = "
                f"{behaviors[row_index][component_index]} := by decide"
            )
    lines.extend([
        "",
        f"def sub (l : List (Fin {n})) : Fin {n} → Bool := fun a => decide (a ∈ l)",
        f"def allSubsets : List (List (Fin {n})) := Hma.sublists axes",
        f"def finiteMinimal (l : List (Fin {n})) : Bool :=",
        "  decide (Hma.sufficient inst (sub l)) &&",
        "    allSubsets.all (fun t =>",
        "      decide (¬ (Hma.proper inst (sub t) (sub l) ∧ Hma.sufficient inst (sub t))))",
        "",
        f"theorem finiteMinimal_spec (l : List (Fin {n})) :",
        "    finiteMinimal l = true ↔ Hma.minimal inst (sub l) := by",
        "  unfold finiteMinimal",
        "  rw [Bool.and_eq_true]",
        "  constructor",
        "  · rintro ⟨hs, hforall⟩",
        "    refine ⟨of_decide_eq_true hs, ?_⟩",
        "    intro T hp hst",
        "    obtain ⟨t, ht, rfl⟩ := Hma.subsetrep inst T",
        "    have hcheck := of_decide_eq_true ((List.all_eq_true.mp hforall) t ht)",
        "    exact hcheck ⟨hp, hst⟩",
        "  · rintro ⟨hs, hmin⟩",
        "    refine ⟨decide_eq_true hs, ?_⟩",
        "    apply List.all_eq_true.mpr",
        "    intro t ht",
        "    by_cases hp : Hma.proper inst (sub t) (sub l)",
        "    · have hns := hmin (sub t) hp",
        "      exact decide_eq_true (by intro h; exact hns h.2)",
        "    · exact decide_eq_true (by intro h; exact hp h.1)",
        "",
    ])

    selected_names = output["selected"]
    selected_indices = [axis_id[name] for name in selected_names]
    selected_expr = _fin_list(selected_indices, n)
    minima_names = [item["axes"] for item in output["minimal_sufficient"]]
    minima_exprs = [_fin_list([axis_id[name] for name in names], n) for names in minima_names]
    lines.extend([
        f"def expectedMinima : List (List (Fin {n})) := {_list_type(minima_exprs)}",
        f"def selected : List (Fin {n}) := {selected_expr}",
        "def minimaAgree : Bool := allSubsets.all (fun l =>",
        "  decide ((finiteMinimal l = true) ↔ l ∈ expectedMinima))",
        "example : minimaAgree = true := by decide",
        "",
    ])

    listed_rhos = [
        f"({item['rho']['mu']}, {item['rho']['lambda']})"
        for item in output["minimal_sufficient"]
    ]
    lines.extend([
        "def listedRhos : List (Nat × Nat) := " + _list_type(listed_rhos),
        "example : expectedMinima.map (fun l => Hma.rho inst (sub l)) = listedRhos := by decide",
        f"example : Hma.rho inst (sub selected) = ({output['selected_rho']['mu']}, {output['selected_rho']['lambda']}) := by decide",
        f"example : Hma.mu inst (Hma.allaxes (A := Fin {n})) = {output['mu_all']} := by decide",
    ])

    full_live_indices = [component_id[name] for name in output["live_all"]]
    lines.append(
        f"example : Hma.livelist inst (Hma.allaxes (A := Fin {n})) = {_fin_list(full_live_indices, m)} := by decide"
    )
    full_engaged_indices = [
        [component_id[name] for name in edge["components"]]
        for edge in output["engaged_all"]
    ]
    engaged_expr = _list_type([_fin_list(edge, m) for edge in full_engaged_indices])
    lines.append(
        f"example : Hma.engagedlist inst (Hma.allaxes (A := Fin {n})) = {engaged_expr} := by decide"
    )
    lines.extend([
        "",
        "def actualMinima : List (List (Fin " + str(n) + ")) := allSubsets.filter finiteMinimal",
        f"def axisInActualMinimal (a : Fin {n}) : Bool := actualMinima.any (fun l => decide (a ∈ l))",
        "",
        "def lexLE : List Nat → List Nat → Bool",
        "  | [], _ => true",
        "  | _ :: _, [] => false",
        "  | x :: xs, y :: ys => if x = y then lexLE xs ys else decide (x < y)",
        "def tieBreakGuard : Bool := expectedMinima.all (fun l =>",
        "  if Hma.rho inst (sub l) = Hma.rho inst (sub selected) then",
        "    lexLE (selected.map Fin.val) (l.map Fin.val)",
        "  else true)",
        "example : tieBreakGuard = true := by decide",
        "",
        "def highestGuard : Bool := allSubsets.all (fun l =>",
        "  decide (finiteMinimal l = true → Hma.rhole inst (sub l) (sub selected)))",
        "theorem highestGuard_pass : highestGuard = true := by decide",
        "theorem selected_highest : Hma.highest inst (sub selected) := by",
        "  refine ⟨(finiteMinimal_spec selected).mp (by decide), ?_⟩",
        "  intro T hmin",
        "  obtain ⟨l, hl, rfl⟩ := Hma.subsetrep inst T",
        "  have hfinite : finiteMinimal l = true := (finiteMinimal_spec l).mpr hmin",
        "  have hbound := (List.all_eq_true.mp highestGuard_pass) l hl",
        "  exact (of_decide_eq_true hbound) hfinite",
        "",
    ])

    for axis_index, axis_name in enumerate(encoded.axis_names):
        disposition = output["axis_dispositions"][axis_name]
        selected_expected = disposition["membership"] == "in-selected"
        any_expected = disposition["membership"] != "in-none"
        dead_expected = disposition["emergent_dead"]
        expected_selected = "true" if selected_expected else "false"
        expected_any = "true" if any_expected else "false"
        expected_dead = "true" if dead_expected else "false"
        lines.append(
            f"example : (decide ({_fin(axis_index, n)} ∈ selected) = {expected_selected}) ∧ "
            f"(axisInActualMinimal {_fin(axis_index, n)} = {expected_any}) ∧ "
            f"(decide (Hma.dead inst {_fin(axis_index, n)}) = {expected_dead}) := by decide"
        )
    lines.extend(["", "end SolverCheck", ""])
    return "\n".join(lines)


def check_against_lean(
    table: Table,
    output: dict[str, Any],
    lean: str,
    proof_dir: str | Path,
) -> tuple[str, str]:
    version = subprocess.run([lean, "--version"], check=True, capture_output=True, text=True).stdout.strip()
    if "version 4.19.0" not in version:
        raise RuntimeError(f"expected pinned Lean 4.19.0, got: {version}")
    source = _lean_source(table, output)
    proof_path = str(Path(proof_dir).resolve())
    env = os.environ.copy()
    env["LEAN_PATH"] = proof_path + (os.pathsep + env["LEAN_PATH"] if env.get("LEAN_PATH") else "")
    with tempfile.TemporaryDirectory(prefix="hma-lean-check-") as directory:
        module = Path(directory) / "SolverCheck.lean"
        module.write_text(source, encoding="utf-8")
        result = subprocess.run(
            [lean, "-DwarningAsError=true", str(module)],
            cwd=directory,
            env=env,
            capture_output=True,
            text=True,
        )
    output_text = result.stdout + result.stderr
    if result.returncode != 0:
        raise RuntimeError(
            "generated Lean agreement certificate failed:\n" + output_text + "\nGenerated source:\n" + source
        )
    if "warning:" in output_text or "error:" in output_text:
        raise RuntimeError("generated Lean checker emitted diagnostics:\n" + output_text)
    return version, source
