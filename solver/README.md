# Deterministic highest-minimal solver

`solve.py` implements the explicit finite-table contract in `SPEC.md` section 7.
It searches every axis subset, returns one highest minimal vector, reports the
entire minimal list with its refinement vectors, and gives each axis both its
minimal-set membership disposition and its independent emergent-dead status.

**Claim:** this is an implementation checked against the proved definitions.
The Python solver, its decoder, and the complete toolchain are not newly proved
correct for every possible input. The executable agreement checks are reported
separately from the Lean theorems.

## Run

The solver itself needs only Python 3.10 or newer and its standard library:

```sh
python3 solver/solve.py solver/instances/X.json > /tmp/X-result.json
python3 solver/solve.py solver/instances/arena.json > /tmp/arena-result.json
```

The required gate also needs the pinned Lean 4.19.0 distribution with its
ordinary `leanc` compiler support, and Node.js for arena regeneration:

```sh
LEAN=lean sh proof/check.sh
```

The gate uses an isolated temporary Lean import/build directory. Existing
`.olean` files in the checkout are not evidence and are not reused. There is no
option to skip the solver checks and still obtain a passing gate. `LEAN` and
`PYTHON` can select installed executables; missing dependencies fail the run.

For an additional instance, compile the checker modules into a disposable
directory, then run `verify.py` on that instance and its actual solver output:

```sh
build="$(mktemp -d)"
export LEAN_PATH="$build"
(
  cd proof
  lean -DwarningAsError=true -o "$build/Hma.olean" Hma.lean
  lean -DwarningAsError=true -o "$build/FiniteCheck.olean" FiniteCheck.lean
  lean -DwarningAsError=true -o "$build/Controls.olean" Controls.lean
)
python3 solver/verify.py solver/instances/X.json /tmp/X-result.json --lean-dir "$build" --control X
```

The full repository gate always builds those modules afresh. `--control X`,
`D`, `E-empty`, or `E-singleton` additionally requires exact correspondence
with the original `Ctl` instance. The temporary build can be discarded after
the check.

## Incremental use and the existing interface

`incremental.py` accepts a strict JSON campaign with `schema: 1`, an `initial`
instance (or checkpoint), and `events`. Each event supplies the next contiguous
`seq`, current schema `epoch`, an `op`, and its operation's payload. For example,
starting from an empty contract with the corresponding domains:

```json
{"seq":1,"epoch":0,"op":"append","rows":[{"axes":[false],"behavior":[false,false]}]}
```

The operations are `append` / `replace` with `rows`, `remove` with `axes`
(configuration vectors), `edges` with `hyperedges`, and `rebase` with `instance`.
Event vectors use **sorted current axis/component names**, as exposed by
`Incremental.instance()`. A rebase advances the epoch and fully reconstructs
witness state. Stale sequence numbers or epochs reject before mutation.

Run `python3 solver/incremental.py campaign.json` to emit complete observations
at every prefix, work receipts, and a compact checkpoint. The Python API provides
`Incremental`, `apply`, `observe`, `checkpoint`, `restore`, and `replay`.
[INCREMENTAL-MODEL.md](INCREMENTAL-MODEL.md) describes the formal guarantees and
checked implementation boundary. The full gate always runs incremental checks.

The `hma-table-v1` / `hma-result-v1` entry point merged on main remains supported:

```sh
python3 solver/solver.py solver/fixtures/x.json
```

`model.py` retains its named-column parser. `compat.py` maps legacy JSON values
to injective canonical string labels, then maps the shared engine's result back
to the existing field names and ordering. There is one computation engine.
`validate.py` retains the X/D/E concrete Lean certificates and checks the arena
through the imported definitions. The authoritative arena fixture lives once
at `instances/arena.json`; the earlier missing-arena blocker is resolved.

## Table format

Inputs have exactly these fields:

```json
{
  "schema": 1,
  "name": "example",
  "axes": [{"name": "a", "values": [false, true]}],
  "components": ["p", "q"],
  "contract": [
    {"axes": [false], "behavior": [false, false]},
    {"axes": [true], "behavior": [true, true]}
  ],
  "hyperedges": [{"components": ["p", "q"], "weight": 1}]
}
```

Each contract row gives a full configuration in the declared axis order and
its full behavior vector in the declared component order. This is exactly
`F` restricted to `C`, not a sampled approximation to an omitted table.

Names are nonempty Unicode strings. Finite value labels are JSON null,
booleans, integers, or strings. Their identities remain distinct: `false`,
`0`, `"0"`, and `null` denote four values. Other finite objects can be named by
distinct strings. Floating-point numbers are rejected; use exact integer or
string labels. No arithmetic on labels is part of liveness.

The decoder rejects duplicate JSON keys, duplicate names, duplicate domain
values, duplicate configurations, incomplete vectors, out-of-range values,
unknown edge members, repeated edge members, and repeated edge sets. Rejecting
duplicate configurations ensures the table defines a function. Set-like
declarations are canonicalized; duplicates are not allowed to inflate Lean's
list counts. These are the set-valued instances specified in `SPEC.md`, not
every list-valued object expressible through the more permissive `Hma.Inst`
structure.

Hyperedge weights are natural numbers and must be positive for edges of size
at least two. Empty and singleton hyperedges are accepted but never engaged.
An omitted hyperedge list is invalid; an explicitly empty list is valid. Zero
axes, zero components, empty contracts, singleton contracts, and empty axis
ranges with empty contracts are supported.

Canonicalization sorts axis and component names and correctly permutes their
table columns. It also sorts domain labels, contract rows, edge members, and
edges. Name order is Unicode code-point lexicographic order, independent of
locale; no Unicode normalization silently identifies different names.

## Search and output

For each unordered pair of contract rows, the solver computes the axes and
components on which they differ. A pair contributes a liveness witness to
exactly the subsets containing its differing axes. A finite subset closure
combines those witnesses for all `2^|A|` subsets. The resulting live sets
determine engaged hyperedges, `mu`, `lambda`, and `rho`.

Sufficiency uses `mu(S) = mu(A)`. Minimality is inclusion minimality. The solver
uses the monotonicity-supported one-axis-deletion optimization: a sufficient
proper subset exists exactly when a sufficient one-axis deletion exists. The
independent Lean checker uses the complete proper-subset definition.

The selected vector maximizes `(mu, lambda)` among all minimal sufficient sets.
Ties break by the lexicographically smallest sorted axis-name list. A shorter
list is not preferred unless it is a prefix in that lexicographic comparison.

The output fields are:

| Field | Meaning |
| --- | --- |
| `schema`, `name` | Format version and instance name |
| `axes`, `components` | Canonical name lists |
| `chosen` | Selected sorted axis list and its `[mu, lambda]` |
| `full` | `mu(A)`, `Live(A)`, and all engaged hyperedges with weights |
| `minimal` | Every inclusion-minimal sufficient set and its refinement vector, in name-list order |
| `dispositions` | Each axis's `chosen`, `alternative`, or `none` membership plus an independent `emergent_dead` Boolean |
| `counts` | Axis/component/contract/edge counts, total subsets, and unordered row pairs scanned |
| `subsets` | Every subset in numeric-mask order over sorted axes, with live set, engaged edges, rho, sufficient/minimal/highest flags |

Deadness is intentionally separate from membership. In X, `c` is emergent-dead
and belongs to the alternative minimal set `{c}`. In the arena, even the chosen
axis `count` is emergent-dead. Neither is an error: deadness asks whether the
axis is redundant with all the other axes present.

Output bytes are UTF-8 JSON with sorted object keys, compact separators, and
one terminal newline. No timestamps, random identifiers, process metadata,
locale formatting, or timing measurements enter the result. The gate compares
two separate processes with different `PYTHONHASHSEED` values byte for byte.
It also changes all declaration orders and checks that the bytes stay equal.

Search cost is exponential in axis count and polynomial in the contract size:
the pair scan is `O(|C|^2 (|A| + |B|))`, followed by subset closure and finite
edge/minimality scans. All counts are printed in the result. There is no
heuristic search truncation or maximum axis count hidden in the solver.
Resource exhaustion can still prevent completion. The validation harness uses
explicit subprocess timeouts and rejects a timed-out check.

## Why agreement is with the proved definitions

`verify.py` does not import `solve.py`. It independently validates and decodes
the original table, using a different injective finite-label encoding. It
embeds that table as a real `Hma.Inst`, with finite axis/component types and
proofs of axis completeness, absence of duplicate axes, and positive
interacting weights. Only numeric identifiers are inserted into generated
Lean source; input labels cannot become Lean commands. Outside the contract,
the behavior function has an arbitrary total default, which none of these
definitions observes.

The checker imports the unchanged `Hma.lean` and computes its `livelist` for
every subset. `FiniteCheck.lean` shares that computed live list when calculating
the other measures. Its five kernel-checked lemmas are:

| Lemma | Exact connection |
| --- | --- |
| `HmaCheck.snapshotLive` | Cached live list equals `Hma.livelist` |
| `HmaCheck.snapshotEdges` | Cached edge list equals `Hma.engagedlist` |
| `HmaCheck.snapshotMeasure` | Cached measure equals `Hma.rho` |
| `HmaCheck.tableMinimalIff` | The finite complete-table minimality predicate is equivalent to `Hma.minimal` |
| `HmaCheck.tableHighestIff` | The finite complete-table highest predicate is equivalent to `Hma.highest` |

The last two use the original `Hma.subsetrep` theorem. Thus quantification over
the full sublist table covers every Boolean axis-set function used by the
original statements. The checker separately evaluates `Hma.dead` for each
axis. Python only maps checked identifiers back to names, applies the specified
name-order tie break, and assembles the required output schema.

Tables above 32 rows, or with at least eight axes and more than four rows,
use an ordinary executable produced by the pinned Lean compiler and `leanc` from the same
`Hma`, checker bridge, and generated instance source. There is no hand-written
C semantic implementation or proof tactic that trusts native evaluation.
Other tables use Lean's interpreter. Both paths are runtime checks. The decoder deterministically interleaves rows
from different behavior groups to expose existential witnesses earlier; all
contract rows are retained, and the declared contract is a set. The generated
behavior lookup preserves exact table equality.

Every output field is compared using type-sensitive canonical JSON. Missing
minimal sets, extra sets, wrong refinement values, wrong selected vectors,
incorrect deadness or membership, omitted subset rows, incorrect counts,
unexpected fields, and booleans substituted for numeric values all fail.
Mutation controls exercise these rejection paths against fresh Lean-derived
expectations. The X/D/E checks also compare their complete input rows with
the original `Ctl.instx`, `Ctl.instd`, `Ctl.inste1`, and `Ctl.inste2` tables.

The original 58 theorem sources are byte-identical to
`63d9d3fdce1f81c81cd5cda2bd9850b0c1494646`. `proof/baseline.json` records their
source hashes and each theorem's original axiom set. The gate requires exact
preservation, cold-compiles every Lean file with warnings as errors, and
audits all original and new theorem dependencies against
`{propext, Classical.choice, Quot.sound}`.

The additional environment audit enumerates declarations from the actual
loaded repository modules, including generated theorem helpers. It rejects
unused custom logical axioms as well as nonstandard dependencies of any
theorem. A negative control injects an unused logical axiom through a temporary
metaprogram and requires the environment auditor to reject it. The checked-in
proof corpus also rejects declaration-generating metaprogram commands. Lean's
ordinary compiler-generated unsafe closure placeholders are reported as
metadata; none may occur in theorem dependencies.

## Validation cases

The required gate checks the following complete subset spaces and the recorded
result JSON in `results/`:

| Instance | Rows | Subsets | Selected vector | rho | Full minimal list |
| --- | ---: | ---: | --- | --- | --- |
| X | 8 | 8 | `{a}` | `(1,3)` | `{a}:(1,3)`, `{c}:(1,2)` |
| D | 2 | 8 | `{a,b,c}` | `(1,2)` | `{a,b,c}:(1,2)` |
| E-empty | 0 | 8 | `{}` | `(0,0)` | `{}` |
| E-singleton | 1 | 8 | `{}` | `(0,0)` | `{}` |
| arena | 1,152 | 256 | `{count}` | `(4,5)` | `{count}`, `{material}`, `{motion}`, `{place}`, all `(4,5)` |
| tie | 8 | 8 | `{a,b}` | `(1,2)` | `{a,b}`, `{c}`, both `(1,2)` |
| typed-weighted | 8 | 4 | `{a,b}` | `(5,3)` | `{a,b}:(5,3)` |
| empty-universe | 1 | 1 | `{}` | `(0,0)` | `{}` |

`tie` distinguishes inclusion minimality and lexical tie breaking from minimum
cardinality. `typed-weighted` distinguishes typed finite labels and weighted
emergence from Boolean-only or unit-weight implementations. `empty-universe`
checks that the empty function/configuration still denotes a valid case.

The arena fixture comes from the actual published arena model at seed 11,
period 8, not from an arena-specific branch in the solver. Its source pin and
reconstruction are documented in [arena/README.md](arena/README.md). The gate
regenerates its full original observations, checks their recorded hash,
checks that interning is lossless, and reproduces the compact table byte for
byte before passing it to the same solver/checker used for X/D/E.

## Not landed / cannot say

- All section 7 computation and output obligations are implemented for the
  explicit finite table format described above. There is no deferred X, D,
  empty/singleton E, or arena check in the gate.
- The solver is **checked executable code**, not a theorem of correctness for
  every possible input. The checker bridges and incremental/hypergraph/counting
  proofs establish model facts, not correctness of the Python algorithm, JSON
  decoders, serializer, Lean compiler/runtime, C compiler, or operating system.
- The finite-instance agreement run is a runtime check. It is not presented
  as a new kernel proof certificate for the entire arena result. The existing
  58 theorems, the checker bridges, and the incremental/hypergraph/counting
  results are kernel-checked proofs.
- The coordinator file named in the ticket was unavailable. The arena was
  recovered reproducibly from the published source pin; byte identity with
  the unseen coordinator artifact is not claimed.
- The arena evidence covers its complete 1,152-row qualification at seed 11,
  period 8. It does not certify all seeds, all periods, every possible arena,
  physical-world fidelity, or the planner's universal optimality.
- No extractor from arbitrary software to a faithful instance is supplied.
  The general solver consumes an explicit contract/behavior/hypergraph table.
- Section 5's induced transformation remains the existing mathematical map
  on lawful variations. The CLI does not provide a separate variation
  enumeration/composition API. Section 7 does not require that additional API.
- Highest means maximal specified `rho` among inclusion-minimal sufficient
  sets. It does not mean a globally best software architecture, minimum-size
  axis set, Pareto optimality over unmodeled measures, or preservation of
  isolated component liveness beyond the existing theorem's scope.
- These are proposed repository changes until the pull request is merged.
  A green recorded local gate and a green hosted CI run are separate receipts;
  neither substitutes for the other.

- Incremental checkpoints preserve current inputs and replay boundaries. They
  do not authenticate fabricated historical observations or work counters and
  do not recover a discarded prefix without an earlier checkpoint/events or
  equivalent reconstruction source.
- Mixed row insertion/withdrawal has a fixed-semantics model proof. Runtime
  behavior replacement, edge edits and schema rebases are checked against
  newly constructed Lean instances; the Python transition code is not proved.
- The ordered sequence adapter rejects duplicate delivery. It does not implement
  the family's separate admission protocol for distributed idempotent merges.
- Pair/support counters are exact for measured operations, not total CPU cost.
  Schema rebases and checkpoint restoration rebuild; full output rendering is
  exponential in the axis count. Restoration work is reported separately.
