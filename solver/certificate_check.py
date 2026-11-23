#!/usr/bin/env python3
"""Kernel certificates for carried incremental witnesses and complete outcomes.

Each prefix supplies a literal active-row list and sparse histogram. Lean checks
only the incident-pair update against the previous materialized histogram and
transports its previously established invariant. It does not recompute the
full row-pair definition at every prefix. The complete supplied outcome is then
checked against the executable renderer whose correctness follows from that
invariant. Ordinary kernel reduction checks the finite equalities.

These are concrete certificates for the decoded inputs, not a proof of the
Python decoder, serializer, or every execution of the Python materializer.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

import incremental
import solve
import verify

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def need(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def encoded(value: Any) -> bytes:
    return verify.canonical(value).encode("utf-8")


def digest(value: Any) -> str:
    return hashlib.sha256(encoded(value)).hexdigest()


def nat(value: Any) -> int:
    need(type(value) is int and value >= 0, "certificate: expected natural number")
    return value


def boolean(value: Any) -> str:
    need(type(value) is bool, "certificate: expected boolean")
    return "true" if value else "false"


def lst(parts) -> str:
    return "[" + ",".join(parts) + "]"


def number_list(values) -> str:
    return lst(str(nat(value)) for value in values)


def fin(value: int) -> str:
    return "⟨" + str(nat(value)) + ",by decide⟩"


def fin_list(values) -> str:
    return lst(fin(value) for value in values)


def sublist_order(size: int) -> list[int]:
    if size == 0:
        return [0]
    return [sum(((mask >> i) & 1) << (size - 1 - i) for i in range(size))
            for mask in range(1 << size)]


def rendered_literal(result: Any, data: dict, rows: int) -> str:
    """Validate all JSON framing, then embed its semantic fields without repair.

    The Lean renderer enumerates Hma.sublists order; the JSON contract uses
    numeric mask order. This adapter first checks the entire original order and
    cross-field consistency before applying that fixed permutation.
    """
    verify.obj(result, {"schema", "name", "axes", "components", "chosen", "full",
                        "minimal", "dispositions", "counts", "subsets"}, "output")
    axes, comps = data["axes"], data["components"]
    n, m = len(axes), len(comps)
    need(type(result["schema"]) is int and result["schema"] == 1, "output schema")
    need(result["name"] == data["name"] and result["axes"] == axes and
         result["components"] == comps, "output identity or column order")
    expected_counts = {"axes": n, "components": m, "contract_rows": rows,
                       "hyperedges": len(data["edges"]), "subsets": 1 << n,
                       "row_pairs": rows * (rows - 1) // 2}
    need(encoded(result["counts"]) == encoded(expected_counts), "output search counts")
    ai, bi = {name: i for i, name in enumerate(axes)}, {name: i for i, name in enumerate(comps)}
    weights = {tuple(edge): weight for edge, weight in data["edges"]}

    def ids(names: Any, index: dict) -> list[int]:
        need(type(names) is list and all(type(name) is str and name in index for name in names),
             "output contains unknown names")
        values = [index[name] for name in names]
        need(values == sorted(set(values)), "noncanonical named set")
        return values

    def snapshot(live: Any, edges: Any, measure: Any) -> str:
        live_ids = ids(live, bi)
        need(type(edges) is list, "output edge list")
        edge_ids = []
        for edge in edges:
            verify.obj(edge, {"components", "weight"}, "output edge")
            key = tuple(ids(edge["components"], bi))
            need(key in weights and type(edge["weight"]) is int and edge["weight"] == weights[key],
                 "output edge weight or identity")
            edge_ids.append(key)
        need(edge_ids == sorted(set(edge_ids)), "output edge ordering")
        need(type(measure) is list and len(measure) == 2, "output rho")
        mu, lam = (nat(value) for value in measure)
        return ("{live := " + fin_list(live_ids) + ",edges := " +
                lst(fin_list(edge) for edge in edge_ids) + ",measure := (" +
                str(mu) + "," + str(lam) + ")}")

    need(type(result["subsets"]) is list and len(result["subsets"]) == 1 << n,
         "output subset coverage")
    classified = []
    actual_minima = []
    highest = []
    for mask, row in enumerate(result["subsets"]):
        verify.obj(row, {"axes", "rho", "live", "engaged", "sufficient", "minimal", "highest"},
                   "output subset")
        selected = ids(row["axes"], ai)
        need(selected == [i for i in range(n) if mask & (1 << i)], "output subset ordering")
        flags = [boolean(row[key]) for key in ("sufficient", "minimal", "highest")]
        value = snapshot(row["live"], row["engaged"], row["rho"])
        classified.append("{axes := " + fin_list(selected) + ",value := " + value +
                          ",sufficient := " + flags[0] + ",minimal := " + flags[1] +
                          ",highest := " + flags[2] + "}")
        if row["minimal"]:
            actual_minima.append({"axes": row["axes"], "rho": row["rho"]})
        if row["highest"]:
            highest.append(selected)
    need(encoded(result["minimal"]) == encoded(sorted(actual_minima, key=lambda r: r["axes"])),
         "full minimal list disagrees with supplied flags")
    verify.obj(result["chosen"], {"axes", "rho"}, "output chosen")
    chosen = ids(result["chosen"]["axes"], ai)
    chosen_mask = sum(1 << i for i in chosen)
    need(encoded(result["chosen"]["rho"]) == encoded(result["subsets"][chosen_mask]["rho"]),
         "chosen rho disagrees with supplied table")
    verify.obj(result["full"], {"mu", "live", "engaged"}, "output full")
    full_row = result["subsets"][-1]
    need(encoded(result["full"]) == encoded({"mu": full_row["rho"][0],
         "live": full_row["live"], "engaged": full_row["engaged"]}), "full output cross fields")
    full = snapshot(result["full"]["live"], result["full"]["engaged"], full_row["rho"])
    need(type(result["dispositions"]) is list and len(result["dispositions"]) == n,
         "output disposition coverage")
    dispositions = []
    for i, value in enumerate(result["dispositions"]):
        verify.obj(value, {"axis", "membership", "emergent_dead"}, "output disposition")
        need(value["axis"] == axes[i] and value["membership"] in {"chosen", "alternative", "none"},
             "output disposition identity or class")
        dispositions.append("{axis := " + fin(i) + ",membership := ." + value["membership"] +
                            ",emergentDead := " + boolean(value["emergent_dead"]) + "}")
    order = sublist_order(n)
    minimum_lists = [ids(result["subsets"][mask]["axes"], ai) for mask in order
                     if result["subsets"][mask]["minimal"]]
    highest_lists = [ids(result["subsets"][mask]["axes"], ai) for mask in order
                    if result["subsets"][mask]["highest"]]
    return ("{full := " + full + ",subsets := " + lst(classified[mask] for mask in order) +
            ",minimal := " + lst(fin_list(value) for value in minimum_lists) +
            ",highest := " + lst(fin_list(value) for value in highest_lists) +
            ",chosen := some " + fin_list(chosen) + ",dispositions := " + lst(dispositions) + "}")


def histogram_literal(hist: dict[tuple[int, int], int], axes: int) -> str:
    entries = []
    for (mask, component), count in sorted(hist.items()):
        need(type(mask) is int and 0 <= mask < 1 << axes and nat(count) > 0,
             "invalid sparse histogram entry")
        entries.append("((" + fin_list(i for i in range(axes) if mask & (1 << i)) +
                       "," + fin(component) + ")," + str(count) + ")")
    return lst(entries)


def template(data: dict) -> str:
    source = verify.lean_source(data).split("def numbers", 1)[0]
    start, end = source.index("def behavior"), source.index("def input")
    parameter = "configuration" if data["rows"] else "_configuration"
    lookup = "def behavior (" + parameter + " : List Nat) : Array Nat :=\n  "
    lookup += "".join("if configuration = " + number_list(axes) + " then #" + number_list(values) + " else\n  "
                      for axes, values in data["rows"])
    lookup += "#[]\n\n"
    source = (source[:start] + lookup + source[end:]).replace(
        "behavior.getD (List.ofFn x) #[]", "behavior (List.ofFn x)")
    return ("import CertificateMaterialization\nimport CertifiedTable\n" + source +
            "\nopen HmaExecutable HmaCertified HmaIncremental HmaCertificate\n" +
            "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" +
            "abbrev WitnessState := HmaExecutable.State Axis Nat Component\n" +
            "def preference := HmaCertified.finLexPrefer (n := " + str(len(data["axes"])) + ")\n")


def generate(instance: dict, operations: list[tuple[str, dict]], *, mutant: str | None = None) -> tuple[str, dict]:
    """Emit closed proofs for literal snapshots, never recursively defined caches."""
    full = solve.normalize(instance)
    data = verify.decode(full)
    parts = [template(data)]
    row_ids = {}
    for i, (axes, _) in enumerate(data["rows"]):
        row_ids[tuple(axes)] = i
        parts.append(f"def row{i} : Axis → Nat := fun a => ((#{number_list(axes)})[a.val]?).getD 0\n")
    initial = copy.deepcopy(full)
    initial["contract"] = []
    state = incremental.Incremental(initial)
    retained: list[int] = []
    proofs = []
    summaries = []

    def row_id(row):
        return row_ids[tuple(data["codes"][verify.label(value)] for value in row["axes"])]

    for prefix in range(len(operations) + 1):
        op, row = ("initial", None) if prefix == 0 else operations[prefix - 1]
        previous_rows = retained[:]
        if op == "append":
            rid = row_id(row)
            state.append_rows([row])
            retained.insert(0, rid)
        elif op == "remove":
            rid = row_id(row)
            state.remove_rows([row["axes"]])
            retained.remove(rid)
        elif op != "initial":
            raise RuntimeError("unsupported certificate operation")
        histogram = dict(state._exact)
        output = state.observe()
        if prefix == len(operations) and mutant == "latent-support":
            need(bool(histogram), "latent support mutant needs nonempty state")
            key = next(iter(sorted(histogram)))
            histogram[key] += 1
        if prefix == len(operations) and mutant == "missing-delta":
            need(bool(histogram), "delta mutant needs nonempty state")
            del histogram[next(iter(sorted(histogram)))]
        if prefix == len(operations) and mutant == "wrong-dead":
            output["dispositions"][0]["emergent_dead"] = not output["dispositions"][0]["emergent_dead"]
        if prefix == len(operations) and mutant == "wrong-chosen":
            candidates = [value for value in output["subsets"] if value["axes"] != output["chosen"]["axes"]]
            selected = candidates[-1]
            output["chosen"] = {"axes": selected["axes"], "rho": selected["rho"]}
        if prefix == len(operations) and mutant == "wrong-minimal":
            output["subsets"][0]["minimal"] = not output["subsets"][0]["minimal"]
            output["minimal"] = sorted(({"axes": value["axes"], "rho": value["rho"]}
                                        for value in output["subsets"] if value["minimal"]), key=lambda v: v["axes"])
        rows_literal = lst(f"row{i}" for i in retained)
        parts.append(f"def entries{prefix} : List (Key Axis Component × Nat) := " +
                     histogram_literal(histogram, len(data["axes"])) + "\n" +
                     f"theorem distinct{prefix} : entries{prefix}.Pairwise (fun p q => (p.1 == q.1) = false) := by decide\n" +
                     f"def state{prefix} : WitnessState :=\n  ⟨{rows_literal}, Std.HashMap.ofList entries{prefix}⟩\n")
        seq = prefix
        if prefix == len(operations) and mutant == "stale-sequence":
            seq -= 1
        if prefix:
            parts.append(f"theorem sequence{prefix} : ({seq} : Nat) = {prefix} := by decide\n")
            if op == "append":
                parts.append(f"def computed{prefix} := HmaExecutable.append input state{prefix - 1} row{rid}\n"
                             f"theorem computedValid{prefix} : Valid input computed{prefix} :=\n"
                             f"  append_valid input state{prefix - 1} valid{prefix - 1} row{rid}\n")
                parts.append(f"theorem fresh{prefix} : row{rid} ∉ state{prefix - 1}.rows := by\n"
                             f"  intro h\n  have hh := List.mem_map_of_mem (f := fun x : Axis → Nat => List.ofFn x) h\n"
                             "  have impossible : ¬ List.ofFn row" + str(rid) + " ∈ (state" + str(prefix - 1) +
                             ".rows.map (fun x : Axis → Nat => List.ofFn x)) := by decide\n  exact impossible hh\n")
            else:
                parts.append(f"def computed{prefix} : WitnessState :=\n  ⟨{rows_literal}, " +
                             f"removeKeys state{prefix - 1}.hist (rowKeys input row{rid} {rows_literal})⟩\n" +
                             f"theorem removed{prefix} : HmaExecutable.remove input state{prefix - 1} row{rid} = some computed{prefix} := by rfl\n" +
                             f"theorem computedValid{prefix} : Valid input computed{prefix} :=\n" +
                             f"  remove_valid input state{prefix - 1} computed{prefix} valid{prefix - 1} row{rid} removed{prefix}\n")
        else:
            parts.append("def computed0 : WitnessState := HmaExecutable.empty\n"
                         "theorem computedValid0 : Valid input computed0 := empty_valid input (by decide)\n")
        parts.append(f"theorem carryRows{prefix} : computed{prefix}.rows = state{prefix}.rows := by rfl\n")
        if prefix:
            opposite = previous_rows if op == "append" else retained
            keys = []
            xs, ys = data["rows"][rid]
            for other in opposite:
                xo, yo = data["rows"][other]
                diff = [i for i, (x, y) in enumerate(zip(xs, xo)) if x != y]
                for component, (x, y) in enumerate(zip(ys, yo)):
                    if x != y:
                        keys.append("(" + fin_list(diff) + "," + fin(component) + ")")
            removed = op == "remove"
            contributing = f"state{prefix - 1}.rows" if not removed else rows_literal
            parts.append(f"def deltaKeys{prefix} : List (Key Axis Component) := " + lst(keys) + "\n" +
                         f"theorem incident{prefix} : rowKeys input row{rid} {contributing} = deltaKeys{prefix} := by decide\n" +
                         f"theorem delta{prefix} : acceptsDelta entries{prefix - 1} entries{prefix} deltaKeys{prefix} {str(removed).lower()} = true := by decide\n" +
                         f"theorem carryHistogram{prefix} : ∀ key, read computed{prefix}.hist key = read state{prefix}.hist key := by\n" +
                         f"  intro key\n  change read ({'removeKeys' if removed else 'addKeys'} (Std.HashMap.ofList entries{prefix - 1}) (rowKeys input row{rid} {contributing})) key = read (Std.HashMap.ofList entries{prefix}) key\n" +
                         f"  rw [incident{prefix}]\n" +
                         f"  exact {'checked_remove' if removed else 'checked_add'} entries{prefix - 1} entries{prefix} deltaKeys{prefix} distinct{prefix - 1} distinct{prefix} delta{prefix} key\n")
        else:
            parts.append("theorem carryHistogram0 : ∀ key, read computed0.hist key = read state0.hist key := by\n" +
                         "  intro key\n  change read (∅ : Histogram (Key Axis Component)) key = read (Std.HashMap.ofList entries0) key\n" +
                         "  rw [read_empty, read_ofList entries0 distinct0]\n  rfl\n")
        parts.append(f"theorem valid{prefix} : Valid input state{prefix} :=\n"
                     f"  valid_transport_read input computed{prefix} state{prefix} computedValid{prefix} carryRows{prefix}\n"
                     f"    (sparse_ofList entries{prefix} distinct{prefix} (by decide)) carryHistogram{prefix}\n"
                     f"def current{prefix} := withContract input state{prefix}.rows\n"
                     f"def supplied{prefix} : Rendered Axis Component :=\n  " +
                     rendered_literal(output, data, len(retained)) + "\n"
                     f"theorem rendered{prefix} : render current{prefix} (liveList input state{prefix}) preference = supplied{prefix} := by\n"
                     f"  rw [liveEntries_eq input state{prefix} entries{prefix} rfl distinct{prefix}]\n"
                     "  decide\n"
                     f"theorem outcome{prefix} : RenderCorrect current{prefix} supplied{prefix} := by\n"
                     f"  rw [← rendered{prefix}]\n"
                     f"  exact render_correct current{prefix} (liveList input state{prefix}) (liveList_exact input state{prefix} valid{prefix}) preference\n")
        proofs.extend([f"valid{prefix}", f"outcome{prefix}"])
        pairs = 0 if prefix == 0 else len(previous_rows) if op == "append" else len(retained)
        need(state.diagnostics()["last"]["pair_evaluations"] == pairs, "delta pair accounting changed")
        summaries.append({"prefix": prefix, "operation": op, "active_rows": len(retained),
                          "pair_delta": pairs, "histogram_cells": len(histogram),
                          "output_sha256": digest(output), "proof": f"outcome{prefix}",
                          "histogram_sha256": digest([[mask, component, count]
                              for (mask, component), count in sorted(histogram.items())])})
    parts.extend("#print axioms " + proof + "\n" for proof in proofs)
    source = "\n".join(parts)
    return source, {"prefixes": summaries, "proofs": proofs,
                    "source_sha256": hashlib.sha256(source.encode()).hexdigest()}


def run_lean(source: str, directory: Path, name: str, *, build: Path, lean: str,
             expect_success: bool = True, timeout: int = 600) -> tuple[dict, str]:
    path = directory / (name + ".lean")
    path.write_text(source, encoding="utf-8")
    process = subprocess.run([lean, "-DwarningAsError=true", "--root=" + str(directory), "-o", str(directory / (name + ".olean")), str(path)],
                             env=dict(os.environ, LEAN_PATH=str(build)), capture_output=True, text=True,
                             timeout=timeout, check=False)
    transcript = process.stdout + process.stderr
    if not expect_success:
        need(process.returncode != 0, name + ": malformed certificate was accepted")
        need("error:" in transcript and ("decide" in transcript or "type mismatch" in transcript),
             name + ": negative control did not reach a failed proof check:\n" + transcript)
        return {}, transcript
    need(process.returncode == 0 and not process.stderr,
         name + ": certificate kernel check failed:\n" + transcript)
    audit = {}
    for line in process.stdout.splitlines():
        match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
        need(match is not None, name + ": unexpected proof diagnostics: " + line)
        used = sorted(part.strip() for part in match[2].split(",") if part.strip())
        need(set(used) <= ALLOWED, name + ": nonstandard proof dependency")
        audit[match[1]] = used
    return audit, transcript


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
    return {"schema": 1, "name": f"exponential-{groups}", "axes": axes, "components": components,
            "contract": rows, "hyperedges": [{"components": components[2 * i:2 * i + 2], "weight": 1}
                                             for i in range(groups)]}


def cases() -> dict[str, tuple[dict, list[tuple[str, dict]]]]:
    result = {}
    for name in ("X", "D", "E-empty", "E-singleton", "tie", "typed-weighted"):
        data = solve.load(HERE / "instances" / (name + ".json"))
        rows = data["contract"]
        operations = [("append", row) for row in rows]
        if rows:
            operations += [("remove", rows[0]), ("append", rows[0])]
        result[name] = (data, operations)
    data = solve.normalize(exponential(3))
    result["exponential-3"] = (data, [("append", row) for row in data["contract"]] +
                                [("remove", data["contract"][0]), ("append", data["contract"][0])])
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true")
    parser.add_argument("--emit-dir", type=Path, help="retain reproducible generated proof sources")
    parser.add_argument("--case", help="develop one named case; never writes the standing receipt")
    parser.add_argument("--source-case", help="emit one generated source; does not validate or record")
    args = parser.parse_args()
    temporary_build = None
    try:
        if args.source_case:
            catalog = cases()
            need(args.source_case in catalog, "unknown source case")
            source, _ = generate(*catalog[args.source_case])
            sys.stdout.buffer.write(source.encode("utf-8"))
            return 0
        lean = os.environ.get("LEAN", "lean")
        if os.environ.get("HMA_BUILD_DIR"):
            build = Path(os.environ["HMA_BUILD_DIR"]).resolve()
        else:
            # A standalone certificate/emit invocation gets its own cold build;
            # the standing gate supplies an already cold-audited import path.
            import certified
            temporary_build = tempfile.TemporaryDirectory(prefix="hma-certificate-build-")
            build = Path(temporary_build.name) / "proof"
            certified.cold_build(build, lean)
            module = "CertificateMaterialization"
            copied = build / (module + ".lean")
            copied.write_bytes((ROOT / "proof" / copied.name).read_bytes())
            compiled = subprocess.run([lean, "-DwarningAsError=true", "-o", module + ".olean", copied.name],
                cwd=build, env=dict(os.environ, LEAN_PATH=str(build)), text=True, capture_output=True, timeout=120)
            need(compiled.returncode == 0 and not compiled.stderr,
                 "certificate dependency failed to compile:\n" + compiled.stdout + compiled.stderr)
        for module in ("ExecutableWitness", "CertifiedTable", "CertificateMaterialization"):
            need((build / (module + ".olean")).is_file(), "missing compiled " + module)
        report = {"schema": 1, "mode": "kernel-carried-state-certificates", "cases": {}, "rejections": []}
        with tempfile.TemporaryDirectory(prefix="hma-certificates-") as temporary:
            work = Path(temporary)
            for name, (data, operations) in cases().items():
                if args.case and args.case != name:
                    continue
                source, record = generate(data, operations)
                executions = []
                for seed in (1, 2):
                    process = subprocess.run([sys.executable, str(Path(__file__).resolve()), "--source-case", name],
                        env=dict(os.environ, PYTHONHASHSEED=str(seed)), capture_output=True, timeout=60)
                    need(process.returncode == 0 and not process.stderr,
                         "certificate generation process failed: " + process.stderr.decode(errors="replace"))
                    executions.append(process.stdout)
                need(source.encode() == executions[0] == executions[1],
                     "certificate source bytes differ across two processes")
                record["two_process_source_bytes"] = "EXACT"
                audit, _ = run_lean(source, work, "Certificate", build=build, lean=lean)
                need(set(audit) == set(record["proofs"]), "certificate proof inventory mismatch")
                record["axioms"] = audit
                report["cases"][name] = record
                if args.emit_dir:
                    args.emit_dir.mkdir(parents=True, exist_ok=True)
                    (args.emit_dir / (name + ".lean")).write_text(source, encoding="utf-8")
                print(f"KERNEL CERTIFICATE {name}: PASS; prefixes={len(record['prefixes'])}; "
                      f"named proofs={len(audit)}; materialized carry=CHECKED; delta-only pairs=CHECKED; "
                      "full outcome=PROVED; source bytes=EXACT", flush=True)
            if args.case:
                need(bool(report["cases"]), "unknown certificate case")
                return 0
            fixture = solve.load(HERE / "instances/X.json")
            # Keep this proof challenge small while retaining a genuinely
            # redundant positive support whose current Boolean view is unchanged.
            operations = [("append", row) for row in fixture["contract"][:3]]
            good, _ = generate(fixture, operations)
            run_lean(good, work, "Control", build=build, lean=lean)
            for mutant in ("latent-support", "missing-delta", "wrong-dead", "wrong-chosen", "wrong-minimal", "stale-sequence"):
                bad, _ = generate(fixture, operations, mutant=mutant)
                run_lean(bad, work, "Rejected", build=build, lean=lean, expect_success=False)
                report["rejections"].append(mutant)
                print("KERNEL REJECTION " + mutant + ": PASS", flush=True)
        record_path = HERE / "results/certificates.json"
        if args.record:
            record_path.write_bytes(encoded(report))
        need(record_path.is_file() and record_path.read_bytes() == encoded(report),
             "kernel certificate receipt missing or stale")
        print(f"CERTIFICATE GATE PASS: {len(report['cases'])} campaigns; "
              f"{sum(len(case['prefixes']) for case in report['cases'].values())} certified prefixes; "
              f"{len(report['rejections'])} rejected corrupt certificates", flush=True)
        return 0
    except (RuntimeError, ValueError, OSError, subprocess.SubprocessError) as error:
        print("CERTIFICATE REJECTED: " + str(error), file=sys.stderr, flush=True)
        return 1
    finally:
        if temporary_build is not None:
            temporary_build.cleanup()


if __name__ == "__main__":
    raise SystemExit(main())
