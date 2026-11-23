#!/usr/bin/env python3
"""Persistent compiled-once Lean HMA session over numbered JSON-lines events.

No future input or historical event journal is retained. The fixed executable
holds the materialized witness state and its Lean validity proof between reads.
The external JSON decoder and encoding remain checked execution boundaries.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import selectors
import subprocess
import sys
import tempfile
from typing import Any

import certified
import verify

ROOT = Path(__file__).resolve().parents[1]
EXTRA_MODULES = ("Exponential", "OnlineHma")


def load_line(line: str | bytes) -> Any:
    return json.loads(line, object_pairs_hook=verify.unique_object,
                      parse_float=verify.no_float, parse_constant=verify.no_float)


def cold_build(build: Path, lean: str) -> None:
    certified.cold_build(build, lean)
    environment = dict(os.environ, LEAN_PATH=str(build.resolve()))
    for module in EXTRA_MODULES:
        path = build / (module + ".lean")
        path.write_bytes((ROOT / "proof" / path.name).read_bytes())
        result = subprocess.run([lean, "-DwarningAsError=true", "-o", module + ".olean", path.name],
                                cwd=build, env=environment, capture_output=True, timeout=120)
        verify.need(result.returncode == 0 and not result.stderr,
                    "online dependency failed: " + module + "\n" + result.stdout.decode() + result.stderr.decode())


def build_binary(build: Path, lean: str, temporary: Path) -> Path:
    """Compile the same fixed program once, before any request is supplied."""
    compiler = certified.Executor(build, lean, temporary)
    for module in EXTRA_MODULES:
        verify.need((build / (module + ".olean")).is_file(), "missing online dependency: " + module)
        cfile, obj = temporary / (module + ".c"), temporary / (module + ".o")
        compiler.command([lean, "-DwarningAsError=true", "--root=" + str(ROOT / "proof"),
                          "-c", str(cfile), str(ROOT / "proof" / (module + ".lean"))])
        compiler.command([compiler.leanc, "-O2", "-c", "-o", str(obj), str(cfile)])
        compiler.objects.append(str(obj))
    runner = temporary / "OnlineMain.lean"
    runner.write_text("import OnlineHma\ndef main : IO Unit := OnlineHma.run\n", encoding="utf-8")
    cfile, binary = temporary / "OnlineMain.c", temporary / "hma-online"
    compiler.command([lean, "-DwarningAsError=true", "-c", str(cfile), str(runner)])
    compiler.command([compiler.leanc, "-O2", "-o", str(binary), str(cfile), *compiler.objects])
    return binary


def encode(source: dict) -> dict:
    data = certified.normalized(source)
    indices = {name: i for i, name in enumerate(data["components"])}
    return {"axes": len(data["axes"]), "components": len(data["components"]),
            "scope": verify.canonical({"axes": data["axes"], "components": data["components"]}),
            "domains": [[verify.label(value) for value in axis["values"]] for axis in data["axes"]],
            "rows": [[[verify.label(v) for v in r["axes"]],
                      [verify.label(v) for v in r["behavior"]]] for r in data["contract"]],
            "edges": [[[indices[c] for c in e["components"]], e["weight"]] for e in data["hyperedges"]]}


class Native:
    def __init__(self, binary: Path, timeout: float = 180, args: list[str] | None = None):
        self.process = subprocess.Popen([str(binary), *(args or [])], stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.timeout = timeout
        self.last_line = b""
        self.output_digest = hashlib.sha256()
        self.response_count = 0
        self.broken = False

    def exchange(self, request: dict) -> dict:
        verify.need(not self.broken, "native session no longer usable")
        try:
            self.process.stdin.write(verify.canonical(request).encode())
            self.process.stdin.flush()
            with selectors.DefaultSelector() as selector:
                selector.register(self.process.stdout, selectors.EVENT_READ)
                verify.need(bool(selector.select(self.timeout)), "online Lean response timed out")
            line = self.process.stdout.readline()
            verify.need(bool(line), "online Lean process terminated")
            self.last_line = line
            self.output_digest.update(line)
            self.response_count += 1
            message = load_line(line)
            verify.need(type(message) is dict and type(message.get("ok")) is bool,
                        "malformed online response")
            if message["ok"]:
                verify.obj(message, {"ok", "observation"}, "online success")
            else:
                verify.obj(message, {"ok", "error"}, "online refusal")
                verify.need(type(message["error"]) is str, "malformed online error")
            return message
        except (OSError, ValueError) as error:
            self.broken = True
            self.process.kill()
            raise verify.Rejected(str(error)) from error

    def close(self) -> None:
        if self.process.poll() is None:
            self.process.stdin.close()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait()
        errors = self.process.stderr.read()
        verify.need(not errors and self.process.returncode == 0,
                    "online Lean process failed: " + errors.decode(errors="replace"))

    def __enter__(self):
        return self

    def __exit__(self, typ, value, trace):
        if typ is not None:
            if self.process.poll() is None:
                self.process.kill()
                self.process.wait()
        else:
            self.close()


def decode_record(source: dict, observation: dict, next_seq: int, epoch: int) -> dict:
    verify.obj(observation, {"next_seq", "epoch", "pair_additions", "pair_removals", "rows", "cells",
                            "support", "result", "minimal_rows"}, "online observation")
    verify.need(type(observation["next_seq"]) is int and observation["next_seq"] == next_seq and
                type(observation["epoch"]) is int and observation["epoch"] == epoch,
                "online response clock mismatch")
    encoded = encode(source)
    data = verify.decode(source)
    data["rows"] = encoded["rows"]
    raw = {k: v for k, v in observation.items() if k != "minimal_rows"}
    raw["prefix"] = next_seq - 1
    result = certified.decode_record(next_seq - 1, data, raw)
    expected_rows = [{"axes": row["axes"], "rho": row["rho"]}
                     for row in observation["result"]["subsets"] if row["minimal"]]
    verify.need(verify.canonical(observation["minimal_rows"]) == verify.canonical(expected_rows),
                "online minimal rows do not match certified result")
    result["minimal_rows"] = [{"id": sum(1 << a for a in p["axes"]),
        "axes": [data["axes"][a] for a in p["axes"]], "rho": p["rho"]} for p in expected_rows]
    return result


class Session:
    """Transactional current-input adapter; no future or prior events retained."""
    def __init__(self, native: Native):
        self.native = native
        self.current: dict | None = None
        self.next_seq = 1
        self.epoch = 0

    def apply(self, request: Any) -> dict:
        verify.need(type(request) is dict and type(request.get("op")) is str, "operation expected")
        op = request["op"]
        if op == "start":
            verify.obj(request, {"op", "instance"}, "start")
            verify.need(self.current is None, "session already started")
            candidate = certified.normalized(request["instance"])
            command = {"op": "start", "input": encode(candidate)}
            next_seq, epoch = 1, 0
        else:
            verify.need(self.current is not None, "session not started")
            verify.need(type(request.get("seq")) is int and request["seq"] == self.next_seq and
                        type(request.get("epoch")) is int and request["epoch"] == self.epoch,
                        "stale sequence or epoch")
            if op in {"checkpoint", "inspect"}:
                verify.obj(request, {"op", "seq", "epoch"}, op)
                candidate = copy.deepcopy(self.current)
                command = copy.deepcopy(request)
                next_seq, epoch = self.next_seq, self.epoch
            else:
                local_event = copy.deepcopy(request)
                local_event["seq"], local_event["epoch"] = 1, 0
                candidate = certified.inputs({"schema": 1, "initial": self.current,
                                              "events": [local_event]})[-1]
                command = {"op": "rebase" if op == "rebase" else "advance",
                           "seq": self.next_seq, "epoch": self.epoch, "input": encode(candidate)}
                next_seq, epoch = self.next_seq + 1, self.epoch + (op == "rebase")
        reply = self.native.exchange(command)
        verify.need(reply["ok"], "Lean transition rejected: " + reply.get("error", ""))
        try:
            result = decode_record(candidate, reply["observation"], next_seq, epoch)
        except (ValueError, KeyError, TypeError):
            self.native.broken = True
            self.native.process.kill()
            raise
        self.current, self.next_seq, self.epoch = candidate, next_seq, epoch
        return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("LEAN", "lean"))
    parser.add_argument("--lean-dir", default=os.environ.get("HMA_BUILD_DIR"))
    parser.add_argument("--binary", type=Path, help="use an already compiled fixed online executable")
    parser.add_argument("--lane", help="optional shared executable dispatch argument")
    args = parser.parse_args()
    try:
        with tempfile.TemporaryDirectory(prefix="hma-online-") as temp:
            temporary = Path(temp)
            if args.binary:
                binary = args.binary
            else:
                build = Path(args.lean_dir) if args.lean_dir else temporary / "proof"
                if not args.lean_dir:
                    cold_build(build, args.lean)
                binary = build_binary(build, args.lean, temporary)
            with Native(binary, args=[args.lane] if args.lane else []) as native:
                session = Session(native)
                for line in sys.stdin:
                    try:
                        result = session.apply(load_line(line))
                        print(verify.canonical({"ok": True, "observation": result}), end="", flush=True)
                    except (verify.Rejected, ValueError, KeyError, TypeError) as error:
                        print(verify.canonical({"ok": False, "error": str(error)}), end="", flush=True)
                        if native.broken:
                            return 1
    except (verify.Rejected, OSError, ValueError, subprocess.SubprocessError) as error:
        print("ONLINE GATE REJECTED: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
