#!/usr/bin/env python3
"""Reproduce the pinned arena table without network or the historical UI solver."""

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    here = Path(__file__).resolve().parent
    provenance = json.loads((here / "provenance.json").read_text())
    fixture = (here.parent / "instances" / "arena.json").read_bytes()
    model = (here / "arena-model.cjs").read_bytes()
    if digest(model) != provenance["model_sha256"]:
        raise ValueError("Arena model differs from the pinned extraction")
    if digest(fixture) != provenance["fixture_sha256"]:
        raise ValueError("Arena fixture differs from its provenance receipt")
    with tempfile.TemporaryDirectory(prefix="hma-arena-") as temporary:
        dictionary = Path(temporary) / "dictionary.json"
        compact = subprocess.run(
            ["node", str(here / "generate-arena.cjs"), "--dictionary", str(dictionary)],
            check=True, stdout=subprocess.PIPE,
        ).stdout
        if compact != fixture:
            raise ValueError("Arena regeneration disagrees with the fixture bytes")
        raw = subprocess.run(
            ["node", str(here / "generate-arena.cjs"), "--raw"],
            check=True, stdout=subprocess.PIPE,
        ).stdout
        if len(raw) != provenance["raw_table_bytes"] or digest(raw) != provenance["raw_table_sha256"]:
            raise ValueError("Original arena observations disagree with their pinned receipt")
        raw_table = json.loads(raw)
        table = json.loads(compact)
        inverse = json.loads(dictionary.read_text())
        decoded = json.loads(compact)
        for row in decoded["contract"]:
            row["behavior"] = [
                inverse[component][value]
                for component, value in zip(decoded["components"], row["behavior"], strict=True)
            ]
        if decoded != raw_table:
            raise ValueError("Interned arena values do not decode to the original observations")
        if len(table["contract"]) != provenance["rows"]:
            raise ValueError("Arena row count disagrees with provenance")
        for component, count in provenance["component_values"].items():
            if len(inverse[component]) != count or len(set(inverse[component])) != count:
                raise ValueError("Arena observation dictionary is not an injective encoding")
    print(
        "ARENA SOURCE PASS: 1152 rows; compact bytes match; original observation SHA256 "
        + provenance["raw_table_sha256"]
        + "; lossless interning checked"
    )


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, IndexError, subprocess.CalledProcessError) as error:
        print("ARENA SOURCE FAIL: " + str(error), file=sys.stderr)
        raise SystemExit(1)
