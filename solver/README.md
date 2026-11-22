# Finite HMA table solver

This directory contains a Python 3.10+ standard-library implementation of the deterministic finite-subset solver specified in `../SPEC.md`. It enumerates every subset of the declared axes, evaluates liveness from pairs of explicit contract rows, computes engaged hyperedges and their weights, finds every minimal sufficient subset, and selects the rho-maximal one with the lexicographically smallest sorted axis-name list as the tie-break.

The implementation is checked against the repository's Lean definitions for every validation fixture. That is a concrete implementation check, not a new general theorem about Python programs.

## Input

An input file is a strict JSON object with exactly these root fields:

- `format`: `hma-table-v1`
- `name`: a non-empty instance name
- `axes`: axis objects `{ "name": string, "values": [...] }`, with unique names and finite, duplicate-free domains
- `components`: a list of unique component names
- `contract`: explicit rows `{ "configuration": {axis: value, ...}, "behavior": {component: value, ...} }`; every row gives one complete axis vector and all component values
- `edges`: hyperedge objects `{ "components": [component, ...], "weight": natural number }`; weights for edges of size at least two must be positive

The contract may be empty or contain a single row. Values are interpreted by equality within each coordinate; the solver does not ascribe additional meaning to JSON values. Duplicate keys, unknown/missing fields, duplicate rows, and out-of-domain configuration values are rejected.

## Output

The JSON result contains the selected axis vector and rho, `mu_all`, `live_all`, `engaged_all`, the complete ordered minimal-sufficient list with rho values, each axis's membership and emergent-dead disposition, and enumeration counts. Output key ordering and formatting are fixed. The gate runs the solver twice per fixture and compares stdout and stderr byte-for-byte.

## Run

From the repository root, run one table directly with:

```sh
python3 -B solver/solver.py solver/fixtures/x.json
```

For the full Lean validation gate, use the pinned Lean 4.19.0 executable in `LEAN`:

```sh
LEAN=/path/to/lean sh proof/check.sh
```

The gate compiles all in-tree Lean files with warnings as errors; scans for forbidden escape tokens; checks the 42 `Hma.lean` plus 16 `Controls.lean` theorem declarations; checks the existing axiom subset; then runs `solver/validate.py`. The validator generates a temporary Lean module for each fixture, instantiates `Hma.Inst`, checks the solver output against the actual definitions, and compiles the resulting certificates against the freshly built `Hma.olean`. Instance X also has a separate direct brute-force comparison.

The arena case is required. Until the exact arena table is present at `solver/fixtures/arena.json`, the gate intentionally exits nonzero after reporting the available case results; it does not substitute synthetic arena data.
