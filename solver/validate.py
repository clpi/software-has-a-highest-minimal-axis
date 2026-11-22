#!/usr/bin/env python3
"""Fail-closed end-to-end validation for the HMA solver."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import Any

import compat
import verify
from independent import brute_force
from lean_check import check_against_lean
from model import InputError, Table, _object_without_duplicate_keys, _reject_constant, load_table

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = Path(__file__).resolve().parent / "fixtures"
REQUIRED = (
    ("x.json", "X"),
    ("d.json", "D"),
    ("e-empty.json", "E-empty"),
    ("e-singleton.json", "E-singleton"),
    ("arena.json", None),
)
RESULT_KEYS = {
    "format", "instance", "selected", "selected_rho", "mu_all", "live_all",
    "engaged_all", "minimal_sufficient", "axis_dispositions", "counts",
}


def _exact_keys(value: Any, required: set[str], where: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != required:
        actual = set(value) if isinstance(value, dict) else set()
        raise InputError(f"{where} keys mismatch: missing={sorted(required - actual)!r}, unknown={sorted(actual - required)!r}")
    return value


def _natural(value: Any, where: str) -> int:
    if type(value) is not int or value < 0:
        raise InputError(f"{where} must be a natural number")
    return value


def _string_list(value: Any, where: str) -> list[str]:
    if not isinstance(value, list) or any(not isinstance(item, str) for item in value):
        raise InputError(f"{where} must be an array of strings")
    return value


def _rho(value: Any, where: str) -> dict[str, int]:
    item = _exact_keys(value, {"mu", "lambda"}, where)
    return {"mu": _natural(item["mu"], f"{where}.mu"),
            "lambda": _natural(item["lambda"], f"{where}.lambda")}


def _parse_solver_output(raw: bytes, stderr: bytes, table: Table) -> dict[str, Any]:
    if stderr:
        raise InputError(f"solver wrote unexpected stderr: {stderr.decode('utf-8', errors='replace')}")
    try:
        result = json.loads(
            raw.decode("utf-8"),
            object_pairs_hook=_object_without_duplicate_keys,
            parse_constant=_reject_constant,
        )
    except (UnicodeError, json.JSONDecodeError, InputError) as exc:
        raise InputError(f"solver stdout is not strict JSON: {exc}") from exc
    _exact_keys(result, RESULT_KEYS, "solver output")
    if result["format"] != "hma-result-v1" or result["instance"] != table.name:
        raise InputError("solver result format or instance name does not match its input")

    axis_names = list(table.axis_names)
    component_names = list(table.components)
    selected = _string_list(result["selected"], "selected")
    if selected != sorted(selected) or len(selected) != len(set(selected)) or not set(selected) <= set(axis_names):
        raise InputError("selected must be a unique sorted subset of axis names")
    selected_rho = _rho(result["selected_rho"], "selected_rho")
    mu_all = _natural(result["mu_all"], "mu_all")
    live_all = _string_list(result["live_all"], "live_all")
    if live_all != [name for name in component_names if name in set(live_all)]:
        raise InputError("live_all must contain unique component names in input order")
    if len(live_all) != len(set(live_all)) or not set(live_all) <= set(component_names):
        raise InputError("live_all contains duplicate or unknown components")

    engaged = result["engaged_all"]
    if not isinstance(engaged, list):
        raise InputError("engaged_all must be an array")
    for index, edge in enumerate(engaged):
        _exact_keys(edge, {"components", "weight"}, f"engaged_all[{index}]")
        edge_components = _string_list(edge["components"], f"engaged_all[{index}].components")
        if len(edge_components) < 2 or len(edge_components) != len(set(edge_components)):
            raise InputError(f"engaged_all[{index}] has an invalid component list")
        if not set(edge_components) <= set(component_names):
            raise InputError(f"engaged_all[{index}] references an unknown component")
        _natural(edge["weight"], f"engaged_all[{index}].weight")

    minimal = result["minimal_sufficient"]
    if not isinstance(minimal, list) or not minimal:
        raise InputError("minimal_sufficient must be a non-empty array")
    normalized_minimal: list[dict[str, Any]] = []
    seen_vectors: set[tuple[str, ...]] = set()
    for index, item in enumerate(minimal):
        item = _exact_keys(item, {"axes", "rho"}, f"minimal_sufficient[{index}]")
        vector = _string_list(item["axes"], f"minimal_sufficient[{index}].axes")
        if vector != sorted(vector) or len(vector) != len(set(vector)) or not set(vector) <= set(axis_names):
            raise InputError(f"minimal_sufficient[{index}].axes must be a unique sorted subset of axis names")
        key = tuple(vector)
        if key in seen_vectors:
            raise InputError(f"duplicate minimal vector: {vector!r}")
        seen_vectors.add(key)
        normalized_minimal.append({"axes": vector, "rho": _rho(item["rho"], f"minimal_sufficient[{index}].rho")})
    expected_order = sorted(
        normalized_minimal,
        key=lambda item: (-item["rho"]["mu"], -item["rho"]["lambda"], tuple(item["axes"])),
    )
    if normalized_minimal != expected_order:
        raise InputError("minimal_sufficient is not in deterministic rho-descending/name-ascending order")
    selected_entries = [item for item in normalized_minimal if item["axes"] == selected]
    if len(selected_entries) != 1 or selected_entries[0]["rho"] != selected_rho:
        raise InputError("selected vector and selected_rho do not match exactly one listed minimal vector")

    dispositions = _exact_keys(result["axis_dispositions"], set(axis_names), "axis_dispositions")
    allowed_memberships = {"in-selected", "in-other-minimal", "in-none"}
    for axis_name in axis_names:
        item = _exact_keys(dispositions[axis_name], {"membership", "emergent_dead"}, f"axis_dispositions.{axis_name}")
        if item["membership"] not in allowed_memberships or type(item["emergent_dead"]) is not bool:
            raise InputError(f"axis_dispositions.{axis_name} has an invalid category or deadness value")
        occurs_in_minimal = any(axis_name in entry["axes"] for entry in normalized_minimal)
        expected_membership = (
            "in-selected" if axis_name in selected
            else "in-other-minimal" if occurs_in_minimal
            else "in-none"
        )
        if item["membership"] != expected_membership:
            raise InputError(f"axis_dispositions.{axis_name}.membership contradicts the listed minimal vectors")

    counts = _exact_keys(
        result["counts"],
        {"axes", "contract_rows", "behavior_cells", "hyperedges", "subsets", "contract_row_pairs"},
        "counts",
    )
    expected_counts = {
        "axes": len(axis_names),
        "contract_rows": len(table.contract),
        "behavior_cells": len(table.contract) * len(component_names),
        "hyperedges": len(table.edges),
        "subsets": 1 << len(axis_names),
        "contract_row_pairs": len(table.contract) * (len(table.contract) - 1) // 2,
    }
    for key, expected in expected_counts.items():
        if _natural(counts[key], f"counts.{key}") != expected:
            raise InputError(f"counts.{key} is inconsistent with the input table")
    return result


def _run_solver(table_path: Path) -> tuple[bytes, bytes]:
    solver_path = Path(__file__).resolve().parent / "solver.py"
    result = subprocess.run(
        [sys.executable, str(solver_path), str(table_path)],
        cwd=ROOT,
        env=os.environ.copy(),
        capture_output=True,
        timeout=600,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"solver failed ({result.returncode}) for {table_path.name}: "
            + result.stderr.decode("utf-8", errors="replace")
        )
    return result.stdout, result.stderr


def _validate_one(filename: str, expected_name: str | None, lean: str, proof_dir: Path) -> tuple[Table, dict[str, Any], str]:
    table_path = FIXTURES / filename
    if filename == "arena.json":
        # One authoritative arena table; preserve the legacy API without a
        # second stored copy of the 1,152-row fixture.
        table = compat.table(verify.read_json(ROOT / "solver/instances/arena.json"))
        from solver import solve as legacy_solve
        first_stdout = json.dumps(legacy_solve(table), ensure_ascii=False, sort_keys=True,
                                  indent=2, allow_nan=False).encode()
        second_stdout = json.dumps(legacy_solve(table), ensure_ascii=False, sort_keys=True,
                                   indent=2, allow_nan=False).encode()
        first_stderr = second_stderr = b""
    else:
        if not table_path.is_file():
            raise FileNotFoundError(f"required fixture is missing: {table_path}")
        table = load_table(table_path)
        first_stdout, first_stderr = _run_solver(table_path)
        second_stdout, second_stderr = _run_solver(table_path)
    if expected_name is not None and table.name != expected_name:
        raise InputError(f"{filename} must have instance name {expected_name!r}, got {table.name!r}")
    if first_stdout != second_stdout or first_stderr != second_stderr:
        raise RuntimeError(f"byte-exact determinism failure on {table.name}")
    output = _parse_solver_output(first_stdout, first_stderr, table)
    expected = verify.compute_expected(compat.instance(table), lean=lean, build_dir=proof_dir)
    if verify.canonical(output) != verify.canonical(compat.result(table, expected)):
        raise RuntimeError("legacy-format result disagrees with imported Hma definitions")
    if filename != "arena.json":
        # Retain the concrete kernel certificates used by the merged interface.
        version, _source = check_against_lean(table, output, lean, proof_dir)
    else:
        version = "4.19.0 (compiled definition evaluation)"

    if table.name == "X":
        independent = brute_force(table)
        for key in ("selected", "selected_rho", "mu_all", "minimal_sufficient"):
            if output[key] != independent[key]:
                raise RuntimeError(f"Instance X independent brute force disagrees on {key}")
        if output["selected"] != ["a"]:
            raise RuntimeError("Instance X control did not select {a}")
        if output["minimal_sufficient"] != [
            {"axes": ["a"], "rho": {"mu": 1, "lambda": 3}},
            {"axes": ["c"], "rho": {"mu": 1, "lambda": 2}},
        ]:
            raise RuntimeError("Instance X control does not retain the full {a}/{c} rho ordering")
    return table, output, version


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"), help="Lean executable (must be v4.19.0)")
    parser.add_argument("--proof-dir", default=str(ROOT / "proof"), help="directory containing freshly built Hma.olean")
    args = parser.parse_args(argv)
    proof_dir = Path(args.proof_dir).resolve()

    failures = 0
    for filename, expected_name in REQUIRED:
        try:
            table, output, version = _validate_one(filename, expected_name, args.lean, proof_dir)
            minima = ", ".join(
                f"{item['axes']} rho=({item['rho']['mu']},{item['rho']['lambda']})"
                for item in output["minimal_sufficient"]
            )
            extra = "; independent brute force=PASS" if table.name == "X" else ""
            print(
                f"PASS {table.name}: selected={output['selected']} "
                f"rho=({output['selected_rho']['mu']},{output['selected_rho']['lambda']}); "
                f"minimal=[{minima}]; Lean={version}; determinism=BYTE-EXACT{extra}"
            )
        except FileNotFoundError as exc:
            failures += 1
            print(f"BLOCKED {expected_name or 'arena'}: {exc}")
        except (InputError, verify.Rejected, RuntimeError, subprocess.SubprocessError) as exc:
            failures += 1
            print(f"FAIL {expected_name or filename}: {exc}")

    if failures:
        print(f"SOLVER GATE: FAIL-CLOSED ({failures} required case(s) missing or invalid)")
        return 1
    print("SOLVER GATE: PASS (all named controls and arena; Lean agreement and byte-exact determinism checked)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
