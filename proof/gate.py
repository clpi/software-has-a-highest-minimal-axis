#!/usr/bin/env python3
"""Cold compilation, complete theorem audit, and executable validation gate."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

import environment

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ESCAPES = re.compile(r"\b(sorry|sorryAx|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|partial|run_elab|run_meta|run_tac|elab|macro|syntax|initialize|builtin_initialize)\b|debug\.skipKernelTC")


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def code_only(source: str) -> str:
    """Blank comments/strings for the restricted, fail-closed declaration census."""
    result = list(source)
    i, depth = 0, 0
    string = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                result[i:i + 2] = "  "
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                result[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if source[i] != "\n":
                    result[i] = " "
                i += 1
        elif string:
            char = source[i]
            if char != "\n":
                result[i] = " "
            if char == "\\" and i + 1 < len(source):
                result[i + 1] = " "
                i += 2
            else:
                if char == '"':
                    string = False
                i += 1
        elif source.startswith("/-", i):
            result[i:i + 2] = "  "
            depth = 1
            i += 2
        elif source.startswith("--", i):
            while i < len(source) and source[i] != "\n":
                result[i] = " "
                i += 1
        elif source[i] == '"':
            result[i] = " "
            string = True
            i += 1
        else:
            i += 1
    require(not depth and not string, "Unterminated comment/string in Lean census")
    return "".join(result)


def declarations(source: str, path: Path) -> list[str]:
    names: list[str] = []
    scope: list[tuple[str, str]] = []
    for line in code_only(source).splitlines():
        namespace = re.fullmatch(r"\s*namespace\s+([\w.']+)\s*", line)
        section = re.fullmatch(r"\s*section(?:\s+([\w.']+))?\s*", line)
        ending = re.fullmatch(r"\s*end(?:\s+([\w.']+))?\s*", line)
        declaration = re.match(r"\s*(?:@\[[^\]]*\]\s*)?(theorem|lemma)\s+([\w.']+)\b", line)
        if namespace:
            scope.append(("namespace", namespace[1]))
        elif section:
            scope.append(("section", section[1] or ""))
        elif ending:
            require(bool(scope), f"Unbalanced scope in {path}")
            _, name = scope.pop()
            require(not ending[1] or ending[1] == name, f"Unrecognized scope ending in {path}")
        elif declaration:
            names.append(".".join([name for kind, name in scope if kind == "namespace"] + [declaration[2]]))
        elif re.search(r"\b(theorem|lemma)\b", line):
            raise RuntimeError(f"Unrecognized theorem declaration in {path}: {line.strip()}")
    require(not scope, f"Unclosed scope in {path}")
    return names


def digest_inputs() -> str:
    entries = []
    for directory in (ROOT / "proof", ROOT / "solver", ROOT / ".github"):
        if not directory.exists():
            continue
        for path in directory.rglob("*"):
            if not path.is_file() or "__pycache__" in path.parts or "results" in path.parts:
                continue
            if path.suffix not in {".lean", ".py", ".sh", ".json", ".cjs", ".yml"} and path.name != "lean-toolchain":
                continue
            entries.append((path.relative_to(ROOT).as_posix(), hashlib.sha256(path.read_bytes()).hexdigest()))
    payload = "".join(f"{path}\0{sha}\n" for path, sha in sorted(entries)).encode()
    return hashlib.sha256(payload).hexdigest()


def main() -> int:
    if len(sys.argv) != 1:
        print("Usage: proof/check.sh (no options; proof and solver gates both required)", file=sys.stderr)
        return 2
    log = (ROOT / "proof/CHECK.log").open("w", encoding="utf-8")

    def emit(message: str) -> None:
        print(message, flush=True)
        log.write(message + "\n")
        log.flush()

    try:
        executable = os.environ.get("LEAN", "lean")
        lean = shutil.which(executable)
        require(lean is not None, f"Lean executable unavailable: {executable}")
        version = subprocess.run([lean, "--version"], text=True, capture_output=True, check=True).stdout.strip()
        require("version 4.19.0," in version, f"Wrong Lean version: {version}")
        require((ROOT / "proof/lean-toolchain").read_text().strip() == "leanprover/lean4:v4.19.0", "Unexpected toolchain pin")
        emit(version)
        emit("Gate input sha256: " + digest_inputs())
        baseline = json.loads((ROOT / "proof/baseline.json").read_text())
        require(baseline["commit"] == "63d9d3fdce1f81c81cd5cda2bd9850b0c1494646", "Unexpected baseline pin")
        require(len(baseline["theorems"]) == 58, "Baseline must contain exactly 58 theorems")
        require(set(baseline["source_sha256"]) == {"proof/Hma.lean", "proof/Controls.lean"}, "Incomplete original-source baseline")
        for path, digest in baseline["source_sha256"].items():
            require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, f"Baseline proof source changed: {path}")
        sources = sorted(path for path in ROOT.rglob("*.lean") if ".git" not in path.relative_to(ROOT).parts)
        require(bool(sources), "No Lean source files")
        census: dict[str, Path] = {}
        modules: dict[str, Path] = {}
        for path in sources:
            source = path.read_text()
            require(not ESCAPES.search(source), f"Prohibited proof escape in {path.relative_to(ROOT)}")
            for name in declarations(source, path.relative_to(ROOT)):
                require(name not in census, f"Duplicate theorem census name: {name}")
                census[name] = path
            relative = path.relative_to(ROOT / "proof") if path.is_relative_to(ROOT / "proof") else path.relative_to(ROOT)
            module = ".".join(relative.with_suffix("").parts)
            require(all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", part) for part in relative.with_suffix("").parts), f"Unsupported Lean module path: {relative}")
            require(module not in modules, f"Duplicate Lean module name: {module}")
            modules[module] = path
        require(set(baseline["theorems"]) <= set(census), "An original theorem is missing")
        emit(f"Source coverage: {len(sources)} Lean files; {len(census)} theorem/lemma declarations; escape scan PASS")

        with tempfile.TemporaryDirectory(prefix="hma-cold-") as temporary:
            build = Path(temporary)
            env = dict(os.environ, LEAN_PATH=str(build), LEAN=lean, HMA_BUILD_DIR=str(build), PYTHONDONTWRITEBYTECODE="1")
            for module, source in modules.items():
                destination = build.joinpath(*module.split(".")).with_suffix(".lean")
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, destination)
            pending = sorted(modules)
            failures: dict[str, str] = {}
            while pending:
                next_pending = []
                for module in pending:
                    path = build.joinpath(*module.split(".")).with_suffix(".lean")
                    result = subprocess.run([lean, "-DwarningAsError=true", "-o", str(path.with_suffix(".olean")), str(path)], cwd=build, env=env, text=True, capture_output=True)
                    output = result.stdout + result.stderr
                    if result.returncode:
                        next_pending.append(module)
                        failures[module] = output
                    else:
                        require(not re.search(r"\b(error|warning):|sorryAx", output), f"Checker diagnostics in {module}: {output}")
                require(len(next_pending) < len(pending), "Lean compilation failed:\n" + "\n".join(failures[module] for module in next_pending))
                pending = next_pending
            emit("Cold compilation: PASS (every Lean source; warnings as errors; isolated import path)")
            audit = build / "GateAudit.lean"
            audit.write_text("\n".join([*("import " + module for module in sorted(modules)), "", *("#print axioms " + name for name in sorted(census))]) + "\n")
            result = subprocess.run([lean, "-DwarningAsError=true", str(audit)], cwd=build, env=env, text=True, capture_output=True)
            require(result.returncode == 0, "Axiom audit did not compile:\n" + result.stdout + result.stderr)
            principles: dict[str, list[str]] = {}
            for line in result.stdout.splitlines():
                match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
                if match:
                    name = match[1]
                    used = sorted(filter(None, (value.strip() for value in match[2].split(","))))
                else:
                    match = re.fullmatch(r"'([^']+)' does not depend on any axioms", line)
                    require(match is not None, "Unexpected axiom audit output: " + line)
                    name, used = match[1], []
                require(name not in principles, f"Duplicate axiom audit line: {name}")
                require(set(used) <= ALLOWED, f"Nonstandard principle for {name}: {used}")
                principles[name] = used
                emit(line)
            require(set(principles) == set(census), "Theorem census and axiom printouts disagree")
            for name, used in baseline["theorems"].items():
                require(principles[name] == used, f"Axiom state changed for {name}")
            emit("Original proof baseline: PASS (58/58; Hma.lean and Controls.lean byte-identical; per-theorem axioms unchanged)")
            emit(f"Axiom subset check: PASS ({len(principles)}/{len(census)}; subset of {{propext, Classical.choice, Quot.sound}})")
            actual = environment.audit(lean, build, modules, census, env)
            for name, used in principles.items():
                require(actual["theorems"][name] == used, f"Environment and printout audit disagree: {name}")
            emit(f"Environment audit: PASS ({actual['actual_theorems']} theorem constants including {len(actual['generated_helpers'])} generated helpers; zero custom logical axioms)")
            emit(f"Compiler metadata: {len(actual['compiler_placeholders'])} generated unsafe placeholders; none in theorem dependencies")
            environment.attack_selftest(lean, env)
            emit("GATE ATTACK CONTROL: PASS (unused metaprogram-generated logical axiom rejected)")
            command = [sys.executable, str(ROOT / "solver/check.py")]
            with subprocess.Popen(command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=1) as process:
                require(process.stdout is not None, "Missing validation output stream")
                for line in process.stdout:
                    emit(line.rstrip("\n"))
                require(process.wait() == 0, "Solver validation gate failed")
        emit("GATE PASS: proof baseline, Lean-definition agreement, complete outputs, and byte-exact determinism")
        return 0
    except (RuntimeError, OSError, ValueError, subprocess.SubprocessError) as error:
        emit("REJECTED: " + str(error))
        return 1
    finally:
        log.close()


if __name__ == "__main__":
    raise SystemExit(main())
