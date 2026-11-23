"""Audit the actual Lean environment, including declarations absent from text.

The generated auditor is temporary tooling, outside the checked-in Lean corpus.
It inspects only constants originating in the freshly compiled repository
modules; Lean's trusted standard library is not relabelled as project code.
"""
from __future__ import annotations

from collections.abc import Iterable, Mapping
import json
from pathlib import Path
import re
import subprocess
import tempfile
from typing import Any


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def source(modules: list[str]) -> str:
    imports = "\n".join("import " + module for module in modules)
    wanted = "[" + ",".join("`" + module for module in modules) + "]"
    return f'''import Lean
{imports}

open Lean Elab Command

run_elab do
  let environment ← getEnv
  let wanted : List Name := {wanted}
  for module in wanted do
    unless (environment.getModuleIdx? module).isSome do
      throwError "Audited module was not imported"
  let mut records : Array Json := #[]
  for (name, info) in environment.constants do
    if let some index := environment.getModuleIdxFor? name then
      let origin := environment.header.moduleNames[index.toNat]!
      if wanted.contains origin then
        if info.isAxiom || info.isTheorem then
          let principles ← collectAxioms name
          records := records.push (Json.mkObj [
            ("name", toJson name.toString),
            ("module", toJson origin.toString),
            ("kind", toJson (if info.isAxiom then "axiom" else "theorem")),
            ("unsafe", toJson info.isUnsafe),
            ("partial", toJson info.isPartial),
            ("principles", toJson (principles.map Name.toString))])
  liftM <| IO.println (Json.arr records).compress
'''


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        require(key not in result, "Duplicate environment-audit JSON key")
        result[key] = value
    return result


def audit(lean: str, build: str | Path, modules: Iterable[str],
          census: Iterable[str], env: Mapping[str, str]) -> dict[str, Any]:
    """Reject logical axioms and audit every actual repository theorem constant.

    Returns the full theorem->principles map, the names of generated helpers,
    and counts. The explicit source census must occur in the actual environment;
    structure projections, equation lemmas, and elaborator helpers are also
    audited even though they have no explicit theorem declaration in source.
    """
    names = sorted(modules)
    require(bool(names) and len(set(names)) == len(names), "Invalid audited module list")
    require(all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*", name)
                for name in names), "Invalid audited module name")
    environment = dict(env, LEAN_PATH=str(Path(build).resolve()))
    with tempfile.TemporaryDirectory(prefix="hma-environment-audit-") as temporary:
        path = Path(temporary) / "EnvironmentAudit.lean"
        path.write_text(source(names), encoding="utf-8")
        result = subprocess.run([lean, "-DwarningAsError=true", str(path)],
                                cwd=temporary, env=environment, text=True,
                                capture_output=True, timeout=120)
    require(result.returncode == 0,
            "Environment audit did not compile:\n" + result.stdout + result.stderr)
    require(not result.stderr, "Unexpected environment-audit diagnostics: " + result.stderr)
    try:
        records = json.loads(result.stdout, object_pairs_hook=unique_object)
    except ValueError as error:
        raise RuntimeError("Malformed environment-audit JSON") from error
    require(type(records) is list, "Environment audit did not return a declaration list")
    principles: dict[str, list[str]] = {}
    seen: set[str] = set()
    placeholders: list[str] = []
    for record in records:
        require(type(record) is dict and set(record) ==
                {"name", "module", "kind", "unsafe", "partial", "principles"},
                "Malformed environment-audit declaration")
        name = record["name"]
        require(type(name) is str and bool(name) and name not in seen,
                "Missing or duplicate environment declaration name")
        seen.add(name)
        require(record["module"] in names and record["kind"] in {"axiom", "theorem"},
                "Unexpected environment declaration origin/kind")
        require(type(record["unsafe"]) is bool and type(record["partial"]) is bool,
                "Malformed environment declaration safety flags")
        used = record["principles"]
        require(type(used) is list and all(type(value) is str for value in used) and
                len(set(used)) == len(used), "Malformed environment dependency list")
        if record["kind"] == "axiom":
            require(record["unsafe"], "Custom logical axiom in repository environment: " + name)
            # Lean itself emits unsafe axiomInfo placeholders for compiled
            # closure/specialization metadata. These are not logical axioms.
            # They remain forbidden as dependencies of any theorem below.
            require(not record["partial"] and used == [name],
                    "Unexpected compiler-placeholder metadata: " + name)
            placeholders.append(name)
        else:
            require(not record["unsafe"] and not record["partial"],
                    "Unchecked theorem constant: " + name)
            require(set(used) <= ALLOWED,
                    f"Nonstandard principle in actual theorem {name}: {used}")
            principles[name] = sorted(used)
    declared = set(census)
    require(declared <= set(principles),
            "Source theorem census missing from actual environment: " +
            ", ".join(sorted(declared - set(principles))))
    return {
        "theorems": dict(sorted(principles.items())),
        "actual_theorems": len(principles),
        "declared_theorems": len(declared),
        "generated_helpers": sorted(set(principles) - declared),
        "safe_axioms": 0,
        "compiler_placeholders": sorted(placeholders),
    }


def attack_selftest(lean: str, env: Mapping[str, str]) -> None:
    """An unused metaprogram-generated logical axiom must fail the audit.

    The hostile module is temporary and deliberately bypasses the text scan,
    isolating the environment audit's obligation. Successful compilation alone
    never counts as successful rejection.
    """
    attack = '''import Lean
open Lean Elab Command
run_elab do
  addDecl <| .axiomDecl {
    name := `Injected
    levelParams := []
    type := mkConst ``False
    isUnsafe := false
  }
'''
    with tempfile.TemporaryDirectory(prefix="hma-environment-attack-") as temporary:
        build = Path(temporary)
        path = build / "Attack.lean"
        path.write_text(attack, encoding="utf-8")
        environment = dict(env, LEAN_PATH=temporary)
        result = subprocess.run([lean, "-DwarningAsError=true", "-o",
                                 str(path.with_suffix(".olean")), str(path)],
                                cwd=temporary, env=environment, text=True,
                                capture_output=True, timeout=120)
        require(result.returncode == 0 and not result.stdout and not result.stderr,
                "Environment attack control did not compile: " + result.stdout + result.stderr)
        try:
            audit(lean, build, ["Attack"], [], environment)
        except RuntimeError as error:
            require(str(error) == "Custom logical axiom in repository environment: Injected",
                    "Environment attack failed for the wrong reason: " + str(error))
        else:
            raise RuntimeError("Environment audit accepted an unused custom logical axiom")
