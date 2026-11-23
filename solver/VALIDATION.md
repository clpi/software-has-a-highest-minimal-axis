# Validation and exact claim boundary

The deliverable is a deterministic finite-table solver and an incremental
materializer **checked against the proved HMA definitions**. The additional
Lean backend has proofs of its actual materialized witness transitions,
complete renderer, admission checks and replay protocol. Concrete incremental
kernel certificates validate supplied cache and output materializations.
These are not a universal correctness theorem for the Python implementation.

The original baseline is `63d9d3fdce1f81c81cd5cda2bd9850b0c1494646`.
The original `Hma.lean` and `Controls.lean` bytes and all 58 individual axiom
sets remain unchanged. The gate records the full current source/declaration
census, including 45 declarations imported unchanged from the existing
hypergraph model. The gate audits the entire loaded proof
environment, including generated theorem helpers, and rejects custom logical
axioms and proof escapes.

## Reproduce

```sh
LEAN=/path/to/lean-4.19.0/bin/lean sh proof/check.sh
```

Python 3.10+, Node.js, and the pinned Lean distribution's ordinary C compiler
support are required. The same cold gate runs in GitHub Actions.
[proof/CHECK.log](../proof/CHECK.log) is the complete recorded receipt.
It records the input digest, theorem dependencies, proof preservation,
source regeneration, each finite-instance outcome, and every gate result.

## Standing instances

The complete results are stored under [results/](results/). Each batch output
is checked against all imported Lean subset definitions, original X/D/E
instance identity where applicable, declaration-order permutations, and two
separate solver processes with different hash seeds and exact byte comparison.

| Instance | Contract rows | Subsets | Selected | Rho | Complete minimal list |
| --- | ---: | ---: | --- | --- | --- |
| X | 8 | 8 | `{a}` | `(1,3)` | `{a}:(1,3)`, `{c}:(1,2)` |
| D | 2 | 8 | `{a,b,c}` | `(1,2)` | `{a,b,c}` |
| E-empty | 0 | 8 | `{}` | `(0,0)` | `{}` |
| E-singleton | 1 | 8 | `{}` | `(0,0)` | `{}` |
| arena | 1,152 | 256 | `{count}` | `(4,5)` | `{count}`, `{material}`, `{motion}`, `{place}`, all `(4,5)` |

The arena's earlier missing-table blocker is resolved by the reproducible
published model extraction documented in [arena/README.md](arena/README.md).
The existing `hma-table-v1` entry point from merged PR #2 is preserved through
`compat.py`; it uses the shared solver, retains the X/D/E concrete Lean
certificates, and checks the single authoritative arena table. No separate
copy of the arena fixture is required for that interface.

## Incremental execution

[results/incremental.json](results/incremental.json) records **14 campaigns,
108 transaction prefixes, and 91 distinct current inputs evaluated in Lean**.
Repeated identical inputs reuse only their freshly computed in-process Lean
result. Every prefix's full result, each checkpoint's actual current input,
all receipt fields, and work accounting are checked. Every checkpoint is
restored and its entire remaining suffix is checked. The original campaign
and **every checkpoint suffix** each run in two separate processes, with full
canonical transcript bytes compared.

| Campaign | Checked prefixes | Final selected/rho | Cumulative pair evaluations |
| --- | ---: | --- | ---: |
| X | 17 | `{a}` / `(1,3)` | 70 |
| D | 5 | `{a,b,c}` / `(1,2)` | 3 |
| E-empty | 1 | `{}` / `(0,0)` | 0 |
| E-singleton | 4 | `{}` / `(0,0)` | 0 |
| arena | 6 | `{count}` / `(4,5)` | 665,278 |
| tie | 11 | `{a,b}` / `(1,2)` | 42 |
| typed-weighted | 11 | `{a,b}` / `(5,3)` | 42 |
| empty-universe | 4 | `{}` / `(0,0)` | 0 |
| schema-rebase | 4 | `{a}` / `(1,3)` | 92 |
| mixed-36 | 37 | Recorded per prefix | 33 |
| exponential-1 through exponential-4 | 2 each | Rho `(k,2k)`, `2^k` minima | 3, 10, 21, 36 |

The arena advances through 0, 1, 32, 1,152, 1,151, and 1,152 active rows.
Growing to 1,152 rows evaluates exactly 662,976 distinct unordered pairs
cumulatively. Removing and restoring one row evaluates 1,151 pairs each,
giving 665,278 across the whole campaign. Those last two updates traverse
zero support cones because other row pairs preserve every occupied exact
support. This is checked operation accounting, not a wall-time benchmark.

At the final arena state the materializer stores 1,152 active rows, 1,230
occupied exact support cells, 256 subset slots, and 1,280 subset-support cells.
It retains zero event records and zero individual pair records. Checkpoints
omit all derived support caches and reconstruct them from active input.

Refusal/challenge controls cover 11 malformed or stale transactions with
atomic refusal, six malformed checkpoints, caller mutation isolation,
pre-checkpoint sequence rejection, 255 exact superset cones, an answer-only
checkpoint counterexample, immediate live-cache corruption, and a corrupt
redundant support that becomes observable only after withdrawal. The batch
gate separately challenges 20 corrupt outputs and 21 malformed inputs.

## What is proved

The executed Lean backend and certificate chain are described in
[CERTIFIED-EXECUTION.md](CERTIFIED-EXECUTION.md). The central new obligations are
`HmaExecutable.append_valid`, `remove_valid`, `compatible_valid`,
`liveList_exact`, `checkpoint_replay`, and `stored_cells_bound`;
`HmaCertified.render_correct` and the lexicographic choice theorem;
and `HmaReplay.finish_sound`, `solve_chosen`, `certified_hypergraph`,
accepted-clock equations and exact pair-work accounting. These concern the
same pure functions that the compiled backend executes. The finite delta
certificate checker proves its acceptance criterion sound before using it to
recertify supplied concrete materializations.

The materialized backend's separate receipt is
[results/certified.json](results/certified.json): 14 campaigns and 108 prefixes,
with full output, exact-mask multiplicity, occupied-subset support, live bits,
retained input, clock and work comparisons. Its two native process runs are
compared as raw bytes. [results/certificates.json](results/certificates.json)
records 7 smaller campaigns, 53 concrete prefixes, 106 named validity/outcome
proofs, and 6 corrupt proof candidates rejected by the kernel. Arena agreement
is executable evidence, not a new closed theorem for its complete result.

- `HmaGraph.live_exact` and `interaction_exact` connect the pair/interaction
  rules to the original HMA definitions through the existing upstream
  all-premise `Qualification.Derives` relation.
- `HmaGraph.incremental_live_exact` and `incremental_interaction_exact` reuse
  `HypergraphIncremental.incremental_exact`, for arbitrary old/new graphs on
  common carriers. They do not reimplement a separate closure semantics.
- `HmaIncremental.mixed_every_prefix_exact` proves supporting-pair cache
  correctness through arbitrary modeled insertion/withdrawal prefixes at
  fixed instance semantics. `checkpoint_mixed_replay` and
  `checkpoint_numbered_replay` prove continuation equivalence from retained
  rows, cache validity and sequence/epoch boundaries.
- `HmaGraph.Reconstructs` and its preservation theorems require current
  semantic input, not historical derivation metadata. Preserving only the
  present answer is insufficient for future replay.
- `IncrementalCounts.lean` proves `2^n` subsets, `2^(n-d)` supersets of a
  size-`d` difference set, and cumulative unordered pair count
  `2P(m)=m(m-1)`, with exactly `m` new pairs on one-row append.
- `HmaExponential.exponential_minimal_family` constructs an actual HMA
  instance for every natural `k` with `2k` axes, `2k+1` distinct contract rows,
  and exactly `2^k` distinct sets whose membership is equivalent to both
  `Hma.minimal` and `Hma.highest`.

## Online parametric reasoning

The fixed native executable receives each request after compilation and carries
current certified state across requests. It exposes the HMA, Pareto, scalar
controller and budget-constrained policy lanes described in
[PARAMETRIC-REASONING.md](PARAMETRIC-REASONING.md). The mandatory gate runs all
four against one freshly built executable and compares their reports with new
execution; a stale report fails rather than being overwritten.

| Check | Recorded coverage | Required agreement |
| --- | --- | --- |
| Online HMA | 14 campaigns, 108 prefixes | Current input, full original-definition output, witnesses, clocks, work, checkpoint suffixes and raw bytes |
| Pareto | 90 prefixes: 42 generic and 48 HMA | Full catalogue/frontier, all-parameter linear regions, equal-cost identities, resurrection, exact comparison reuse and raw bytes |
| Scalar controller | 75 accepted prefixes, 10 refusals | Every cached Bellman layer, values/actions against complete adaptive-tree enumeration, dependency work, cumulative vector and raw bytes |
| Policy controller | 7 campaigns, 30 prefixes, 14 refusals | Every adaptive policy/profile, budget-feasible catalogue/frontier, global nondominance, weighted optimum, dependencies, cumulative bounds and raw bytes |
| Autonomous qualification | 5 parameter regimes, 15 decisions | Selected actions drive real online HMA updates; fresh original-definition agreement and measured work precede outcome admission |
| Concrete reasoning certificates | 6 accepted and 6 rejected claims | Lean kernel accepts exact claims and rejects nearby false claims for the expected logical reason |

The autonomous initial problem contains 729 syntactic policies and all 29
admissible schedules for qualifying eight X rows in at most three nonempty
batches. Its unrestricted frontier has five policy identities and three cost
vectors: `(28,1,64)`, `(28,2,32)`, and `(28,3,22)`. Coordinates mean incident pair
evaluations, nonempty submissions and the declared square-of-batch-size tariff.
That tariff is not a CPU measurement. Every run completes all eight rows with
28 pair evaluations. All 15 corrupted pair-count observations are refused
before policy admission. Four distinct current inputs are checked freshly
against the original Lean definitions. Entire paired process transcripts are
compared byte for byte across two fresh executions.

The policy lane first chooses globally over all admissible policies and commits
the resulting cost vector. Its subsequent emitted frontier is complete among
budget-feasible policies. The selected policy remains globally nondominated
among all structurally admissible policies and minimizes the current weighted
objective among every budget-feasible continuation. Parameter changes preserve
the cumulative component commitment. Unsupported or infeasible model revisions
reject atomically; a rebase explicitly starts a new commitment.

This extension adds universal proofs for the executed finite Pareto and
controller functions. It does not recast the Python solver as a new theorem.
The actual scalar outcome transition is connected to the abstract cumulative
minimax theorem by `ControllerRefinement.lean`. `OnlinePolicy.lean` proves
selected-record/action existence and acceptance of every supported outcome
for each carried positive-horizon state. The autonomous Python orchestration
and concrete transcript are checked integration, not a new closed theorem for
the entire external loop.

## Not landed / cannot say

All SPEC section 7 computation/output obligations are implemented for the
explicit finite table representation, including the standing and arena checks.
The boundaries below remain explicit:

- The Python solver, incremental transition code, input adapters, serialization
  and execution toolchain are checked implementations. No theorem quantifies
  over every execution of those programs.
- The earlier abstract mixed-row model fixes its behavior function. The new
  executable Lean layer proves transfer across behavior changes on retained
  rows, carries proofs through replacement and edge/weight edits, and admits
  heterogeneous schema rebase by reconstruction. Actual Python operations
  remain checked executions. There is no universal theorem that every
  schema-compatible reconciliation request is accepted; every accepted Lean
  result is certified, and the batch `solve` is total for its stated premises.
- The ordered sequence adapter rejects duplicate deliveries. It does not
  implement the separate distributed admission protocol with idempotent
  delivery, permanent identity tombstones, arbitrary merge order, durable
  storage transactions, or crash recovery.
- Retaining unlimited provenance is not a requirement. A compact checkpoint
  preserves current-state reconstruction and future permitted replay. It
  does not reconstruct a discarded historical prefix without an earlier
  checkpoint/events or an equivalent generator. Checkpoint parsing does not
  authenticate fabricated input observations or historical work counters.
- Pair/support counters omit full-table validation, copying, sorting,
  serialization and other work. Restoration work is reported separately from
  semantic-event cumulative counters. No universal speedup or polynomial cost
  is promised; the explicit subset table and full minimal list can be
  exponentially large, as the new theorem demonstrates.
- Arena evidence covers the pinned model, seed 11, period 8, and its full
  1,152-row contract. It does not establish physical-world fidelity, all seeds
  or periods, or universal planner optimality. The coordinator artifact named
  in the original ticket was unavailable; identity with that unseen artifact
  is not claimed.
- There is no arbitrary-software-to-instance extractor, nor a separate
  SPEC section 5 variation/composition API. The existing section 5 mathematical
  result remains unchanged; that API is outside section 7's solver contract.

The final change remains a pull request until merged. A recorded gate and a
hosted CI run are distinct receipts tied to their exact tested inputs/commits.
