#!/bin/sh
# One cold gate for the proof and the executable agreement checks.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
exec "${PYTHON:-python3}" "$ROOT/proof/gate.py" "$@"
