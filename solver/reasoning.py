#!/usr/bin/env python3
"""Compile one fixed proof-carrying reasoning process and feed runtime requests.

The finite model, admissible actions, objective dimensions, parameters, and
horizon are explicit runtime inputs. Compilation never consumes a campaign.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

import online
import verify

ROOT = Path(__file__).resolve().parents[1]
LANES = {"hma": "OnlineHma", "pareto": "OnlinePareto",
         "controller": "OnlineController", "policy": "OnlinePolicy"}


def modules_for(entries: list[str]) -> list[str]:
    ordered: list[str] = []
    active: set[str] = set()

    def visit(module: str) -> None:
        if module in ordered:
            return
        path = ROOT / "proof" / (module + ".lean")
        if not path.exists():
            return
        verify.need(module not in active, "cyclic module dependency")
        active.add(module)
        for dependency in re.findall(r"^import\s+([\w.]+)\s*$", path.read_text(), re.MULTILINE):
            visit(dependency)
        active.remove(module)
        ordered.append(module)

    for entry in entries:
        visit(entry)
    return ordered


def command(args: list[str], *, env: dict, cwd: Path | None = None, timeout: int = 240) -> subprocess.CompletedProcess:
    result = subprocess.run(args, env=env, cwd=cwd, capture_output=True, timeout=timeout)
    verify.need(result.returncode == 0, "reasoning build failed: " + " ".join(args) + "\n" +
                result.stdout.decode(errors="replace") + result.stderr.decode(errors="replace"))
    return result


def cold_build(build: Path, lean: str, lanes: list[str] | None = None) -> None:
    build.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(build.resolve()))
    for module in modules_for([LANES[k] for k in lanes or LANES]):
        source = build / (module + ".lean")
        shutil.copyfile(ROOT / "proof" / source.name, source)
        command([lean, "-DwarningAsError=true", "-o", str(source.with_suffix(".olean")), str(source)],
                env=env, cwd=build)


def build_binary(build: Path, lean: str, temporary: Path, lanes: list[str] | None = None) -> Path:
    """No input tables or events are available to the fixed program build."""
    lanes = lanes or list(LANES)
    temporary.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=str(build.resolve()))
    prefix = command([lean, "--print-prefix"], env=env).stdout.decode().strip()
    leanc = str(Path(prefix) / "bin/leanc")
    objects: list[str] = []
    for module in modules_for([LANES[k] for k in lanes]):
        verify.need((build / (module + ".olean")).is_file(), "missing cold-built module: " + module)
        source = build / (module + ".lean")
        verify.need(source.is_file() and source.read_bytes() == (ROOT / "proof" / source.name).read_bytes(),
                    "cold-built source is absent or differs from current input: " + module)
        cfile = temporary / (module + ".c")
        obj = temporary / (module + ".o")
        command([lean, "-DwarningAsError=true", "--root=" + str(build),
                 "-c", str(cfile), str(source)], env=env)
        command([leanc, "-O2", "-c", "-o", str(obj), str(cfile)], env=env)
        objects.append(str(obj))
    runner = temporary / "ReasoningMain.lean"
    imports = "\n".join("import " + LANES[k] for k in lanes)
    cases = "\n".join(f'  | ["{k}"] => {LANES[k]}.run' for k in lanes)
    runner.write_text(imports + "\n\ndef main (args : List String) : IO Unit :=\n  match args with\n" +
                      cases + '\n  | _ => throw (IO.userError "expected a reasoning lane")\n')
    cfile, binary = temporary / "ReasoningMain.c", temporary / "hma-reasoning"
    command([lean, "-DwarningAsError=true", "--root=" + str(temporary), "-c", str(cfile), str(runner)], env=env)
    command([leanc, "-O2", "-o", str(binary), str(cfile), *objects], env=env)
    return binary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("lane", choices=LANES)
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--lean-dir", type=Path)
    parser.add_argument("--binary", type=Path)
    parser.add_argument("--build-only", type=Path)
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    try:
        with tempfile.TemporaryDirectory(prefix="hma-reasoning-") as tmp:
            temporary = Path(tmp)
            binary = args.binary
            if binary is None:
                verify.need(lean is not None, "Lean 4.19.0 executable unavailable")
                build = args.lean_dir or temporary / "proof"
                if args.lean_dir is None:
                    cold_build(build, lean)
                destination = args.build_only or temporary / "native"
                binary = build_binary(build, lean, destination)
            if args.build_only:
                print(binary)
                return 0
            native = online.Native(binary, args=[args.lane])
            try:
                for line in sys.stdin.buffer:
                    try:
                        request = online.load_line(line)
                        native.exchange(request)
                        sys.stdout.buffer.write(native.last_line)
                        sys.stdout.buffer.flush()
                    except (ValueError, TypeError, verify.Rejected) as error:
                        sys.stdout.write(verify.canonical({"ok": False, "error": str(error)}))
                        sys.stdout.flush()
            finally:
                native.close()
        return 0
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print("REJECTED: " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
