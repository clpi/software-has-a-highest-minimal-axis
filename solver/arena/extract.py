#!/usr/bin/env python3
"""Re-extract the frozen model from a separately obtained pinned HTML source."""

import hashlib
import json
from pathlib import Path
import sys


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    if len(sys.argv) != 2:
        raise ValueError("usage: extract.py PINNED_INDEX_HTML")
    provenance = json.loads(Path(__file__).with_name("provenance.json").read_text())
    original = Path(sys.argv[1]).read_bytes()
    if digest(original) != provenance["source_sha256"]:
        raise ValueError("input is not the pinned arena HTML")
    source = original.decode("utf-8")
    extracts = []
    for span in provenance["extracts"]:
        start = source.index(span["start"])
        end = source.index(span["end"], start) if span["end"] is not None else source.index("\n", start) + 1
        part = source[start:end]
        if digest(part.encode("utf-8")) != span["sha256"]:
            raise ValueError("source span hash mismatch: " + span["start"])
        extracts.append(part)
        if span["start"] == "var SCEN={":
            extracts.append("  }\n};\n")
    extracts.append("module.exports = { hmaBuildInstance };\n")
    result = "\n".join(extracts).encode("utf-8")
    if digest(result) != provenance["model_sha256"]:
        raise ValueError("extraction does not reproduce the frozen module")
    sys.stdout.buffer.write(result)


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print("ARENA EXTRACTION FAIL: " + str(error), file=sys.stderr)
        raise SystemExit(1)
