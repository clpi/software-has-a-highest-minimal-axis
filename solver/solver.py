#!/usr/bin/env python3
"""Compatible hma-table-v1 entry point for the shared finite HMA engine."""
from __future__ import annotations
import argparse
import json
import sys
from typing import Any
import compat
from model import InputError, Table, load_table
import solve as engine


def solve(table: Table) -> dict[str, Any]:
    return compat.result(table, engine.solve(compat.instance(table)))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("table", help="path to an hma-table-v1 JSON file")
    args = parser.parse_args(argv)
    try:
        result = solve(load_table(args.table))
        print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False))
    except (InputError, engine.InvalidInstance, RuntimeError, UnicodeError) as exc:
        print(f"hma-solver: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
