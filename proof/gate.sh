#!/bin/sh
# The full gate: the founding proof gate, then the solver
# agreement gate. Fails closed: if any stage fails, the
# gate fails.
#
# Stage 1 runs proof/check.sh unchanged (escape scan,
# cold compile with warnings as errors, axiom audit
# inside {propext, Classical.choice, Quot.sound}); it
# also builds the compiled modules the expectations
# program runs against.
#
# Stage 2 builds the expectations program
# (proof/Expect.lean) as a native executable and runs it
# twice; the two runs must be byte-identical. The program
# evaluates the proved definitions of the core on
# Instances X, D, both forms of E, and the arena instance
# at seeds 11 and 23, and prints the canonical
# expectation lines. The native build is because the
# interpreter evaluates the arena pair scans for minutes
# where the native build takes seconds, with the same
# output either way.
#
# Stage 3 runs the solver twice on each instance (the
# two runs must be byte-identical), renders each run in
# the canonical lines with solver/canon.py, and diffs
# the result against the expectations. Any disagreement
# fails the gate.
set -eu
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
export LEAN_PATH=".:${LEAN_PATH:-}"

LEAN="$LEAN" sh check.sh

TMPD="$(mktemp -d)"
trap 'rm -rf "$TMPD"' EXIT HUP INT TERM

LEANBIN="$(dirname "$(command -v "$LEAN")")"
TCROOT="$(cd "$LEANBIN/.." && pwd)"
mkdir -p "$TMPD/build"
for m in Hma Controls Arena Expect; do
  "$LEAN" --c="$TMPD/build/$m.c" "$m.lean"
done
LEAN_CC="${LEAN_CC:-cc}" "$LEANBIN/leanc" -O2 \
  -o "$TMPD/build/expect" \
  "$TMPD/build/Hma.c" "$TMPD/build/Controls.c" \
  "$TMPD/build/Arena.c" "$TMPD/build/Expect.c" \
  -L"$TCROOT/lib" -L"$TCROOT/lib/lean" \
  -Wl,-rpath,"$TCROOT/lib/lean" -Wl,-rpath,"$TCROOT/lib"

"$TMPD/build/expect" > "$TMPD/expected.txt"
"$TMPD/build/expect" > "$TMPD/expected2.txt"
cmp "$TMPD/expected.txt" "$TMPD/expected2.txt"

SOLVER_DIR="../solver"
: > "$TMPD/got.txt"
for inst in instance_x.json instance_d.json \
    instance_e_empty.json instance_e_singleton.json \
    instance_arena_seed11.json instance_arena_seed23.json; do
  python3 "$SOLVER_DIR/solver.py" "$SOLVER_DIR/instances/$inst" \
    > "$TMPD/run1.json"
  python3 "$SOLVER_DIR/solver.py" "$SOLVER_DIR/instances/$inst" \
    > "$TMPD/run2.json"
  cmp "$TMPD/run1.json" "$TMPD/run2.json"
  python3 "$SOLVER_DIR/canon.py" "$TMPD/run1.json" \
    "$SOLVER_DIR/instances/$inst" >> "$TMPD/got.txt"
done

if ! diff -u "$TMPD/expected.txt" "$TMPD/got.txt"; then
  echo "Rejected: solver output disagrees with the proved definitions" >&2
  exit 1
fi
echo "Solver agreement check passed: the solver agrees with the proved definitions on Instances X, D, E (both forms), and the arena instance at seeds 11 and 23, and its output is byte-identical across two runs on every instance."
