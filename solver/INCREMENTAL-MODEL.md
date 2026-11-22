# Incremental HMA: reconstruction, witnesses, and checked outcomes

The retained invariant is enough information to reconstruct the current input,
replay a permitted future suffix, and validate its outcomes. Preserving every
historical receipt, derivation path, or intermediate cache is not a requirement.
The materializer stores no event log and no individual pair-witness records.

There are two different kinds of evidence in this directory. The Lean modules
prove statements about the mathematical models. The gate checks executions of
the Python materializer against the original Lean definitions. These checks do
not constitute a universal correctness theorem for the Python implementation,
its decoder, serialization, compiler, or runtime.

## One hypergraph semantics

[`proof/HmaGraph.lean`](../proof/HmaGraph.lean) imports the existing family
hypergraph model rather than defining another closure relation. The upstream
modules are copied without modification from
[`clpi/software-optimality@0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0`](https://github.com/clpi/software-optimality/tree/0bbc1f3b8aa38afe17e02ccbd7ddd0e7722b3cb0).
[`proof/upstream.json`](../proof/upstream.json) records the exact source files
and their SHA256 digests.

For an instance `I` and allowed-axis set `S`, graph roots identify current
contract rows and selected axes. For two rows `x,y`, define their difference
set as

\[
D(x,y)=\{a\in I.axes\mid x(a)\ne y(a)\}.
\]

A pair rule has **all** of these premises: the two row atoms and the axis atom
for every member of `D(x,y)`. Its conclusion is a live-component atom when
the two behavior values differ. An interaction rule requires all live-component
atoms of that interaction. It also checks declared component membership,
interaction membership, and cardinality at least two. Binary incidence is not
used as an inference rule.

| Formal statement | Exact consequence |
| --- | --- |
| `HmaGraph.differences_selected` | Requiring every changed axis is equivalent to `Hma.agreeoff`. |
| `HmaGraph.live_exact` | Deriving a live-component atom is equivalent to the original `Hma.live`. |
| `HmaGraph.interaction_exact` | Deriving an interaction atom is equivalent to the original `Hma.engaged`. |
| `HmaGraph.supportCount_hypergraph_exact` | Positive row-pair support and live-atom derivability agree. |
| `HmaGraph.occupiedCount_hypergraph_exact` | Positive occupied-difference-mask support and live-atom derivability agree. |
| `HmaGraph.incremental_live_exact` / `incremental_interaction_exact` | The upstream incremental closure produces exactly the new instance's liveness and engagement. |
| `HmaGraph.incremental_projection_exact` | Any downstream observation of closure sees equal incremental and full inputs. |

The incremental bridge uses the upstream
`HypergraphIncremental.incremental_exact`. That model invalidates changed rule
heads and their downstream dependents, preserves unaffected derivations, and
rebuilds affected derivations from supported premises. Its correctness covers
arbitrary old/new graphs, including retractions and cycles. This does not mean
the Python materializer implements the upstream generic graph evaluator; it
implements the specialized row-pair representation whose meanings are connected
above.

## What the implementation retains

[`incremental.py`](incremental.py) retains the current typed input table and two
derived counting layers:

1. `exact[(D,b)]` counts unordered current row pairs whose exact difference mask
   is `D` and whose values for component `b` differ.
2. `support[S][b]` counts distinct occupied exact masks `D` contained in `S`.
   The component is live precisely when this count is positive.

The second count is a count of occupied masks, not a count of row pairs. This
distinction permits efficient updates: increasing a positive exact count does
not change any live conclusion. Only a transition between zero and positive
changes that mask's superset cone. Retaining multiplicities is necessary for
withdrawals: removing one witness must not remove another witness's support.

Cumulative evidence does not require a monotone selected answer. Under fixed
instance semantics, `HmaIncremental.live_add_row` proves that an existing live
witness survives a row append. Sufficiency still compares a subset's emergence
against the current full-axis emergence, so the sufficient/minimal families
must be reconsidered as that target changes. Withdrawals and behavior or weight
edits are revision-sensitive as well. Append-only describes the supplied event
sequence, not an obligation to keep every old conclusion active.

An update partitions rows into unchanged, removed and added groups. The
materializer revisits removed-to-unchanged and removed-to-removed pairs, and the
corresponding new pairs. It skips unchanged-to-unchanged pairs. Behavior
replacement is a single transaction whose net support deltas are accumulated
before the closure changes.

Input validation and support-underflow checks precede mutation. The gate tests
that rejected transactions leave the current input, outputs and diagnostic
state unchanged. This is an executed refusal check, not an operating-system
crash-recovery or durable-transaction theorem.

## Checkpoints and replay

A checkpoint contains the complete current instance, the next sequence number,
the schema epoch, and declared cumulative work counters. It omits events,
individual pair records, exact-mask counts, subset-support counts and live
bitsets. Restoration rebuilds those derived caches from the current input.

`HmaGraph.Reconstructs` specifies what must survive reconstruction. Axes,
components, contract membership, behavior on current contract rows, interaction
declarations and weights determine current HMA observations. Contract delivery
order and repeated identical deliveries do not affect that relation. The
`reconstructed_*` theorems preserve the live list, emergence measure, refinement
vector, minimality, highestness and dead-axis classifications.

The separate row-update model in
[`proof/Incremental.lean`](../proof/Incremental.lean) proves cache preservation
after every accepted insertion/withdrawal prefix at fixed instance semantics.
`supportCount_remove_middle` and `removeRow_valid` handle removal from any
position in the retained row list; `mixed_every_prefix_exact` establishes the
resulting liveness invariant for every accepted mixed prefix.
`replayRows_append` proves that splitting an append replay into batches gives
the same model state. `checkpoint_mixed_replay` proves that reconstructing a
valid model cache from its retained rows preserves every future insertion and
withdrawal suffix. `checkpoint_numbered_replay` also retains the sequence
boundary; `wrong_sequence_rejected` proves rejection of a mismatched number.
These premises preserve the actual rows and clock; equality of current answers
is not substituted for reconstruction.

That distinction is testable. An empty contract and a singleton contract can
have identical current liveness. Adding the same second observation can then
produce different liveness. Keeping only the chosen answer, the minimal list,
or even every current live bit would lose information needed by that future
update. The gate includes this counterexample and a corrupted-support case
whose present answer is correct but whose answer after withdrawal is wrong.

The Python gate exercises append, withdrawal, behavior replacement, interaction
and weight edits, and explicit schema rebases. It restores every tested
checkpoint and checks the subsequent suffix outcomes. Fixed-instance model
proofs cover insertion and withdrawal. Changes to behavior, interaction weights
or schema, as executed by the Python implementation, are checked against fresh
Lean outcomes. The original hypergraph bridge proves equivalence of its
abstract old/new graph projections; it is not a universal proof of the Python
transaction code.

The sequence protocol accepts only the next contiguous event in the current
schema epoch. Older or duplicate transactions fail closed after restoration.
Removing a configuration and later adding it with a fresh transaction is
permitted. This is an ordered journal adapter, not the upstream `Admission`
module's identity-based, idempotent delivery protocol with permanent tombstones.

Schema rebases rebuild the cache completely and advance the epoch. Old
positional masks are never reused across an axis-universe change. The generic
graph theorems compare graphs on common carrier types; the Python schema
conversion and rebuilding path is checked by execution.

Discarding history also bounds the replay claim. A checkpoint can replay its
retained suffix; it does not reconstruct discarded historical prefixes. To
revisit those prefixes, retain an earlier checkpoint plus the relevant events
or an equivalent reproducible generator. Likewise, a syntactically valid
checkpoint is not evidence that its historical assertions are authentic.
Independently validated checkpoint and outcome bytes define the replay boundary.

## Combinatorial, exponential, and cumulative costs

[`proof/IncrementalCounts.lean`](../proof/IncrementalCounts.lean) distinguishes
three counts:

| Quantity | Formal count |
| --- | --- |
| Explicit subset space for `n` axes | `2^n`, by `sublists_length`; no duplicates when the axis list has none, by `sublists_nodup`. |
| Supersets of a required difference mask of size `d` | `2^(n-d)`, by `cone_length`; uniqueness and coverage are established separately. |
| Unordered pairs after accumulating `m` rows | `m(m-1)/2`, expressed without division by `cumulativePairs_twice` and related to actual pair enumeration by `pairs_length`. |

Adding one row to `m` existing rows introduces exactly `m` new pairs
(`pair_delta_exact`). Thus a pure sequence of single-row appends evaluates each
pair once cumulatively; it does not repeat all old pairs at every prefix. An
exact support's cone may still contain exponentially many subsets. Incremental
processing reduces repeated work; it does not make explicit exponential output
polynomial.

[`proof/Exponential.lean`](../proof/Exponential.lean) establishes an actual HMA
family for every natural `k`. `HmaExponential.exponential_minimal_family` proves
that its instance has `2k` axes and `2k+1` distinct contract rows, together with
a list of exactly `2^k` distinct sets whose membership is equivalent to
`Hma.minimal` and to `Hma.highest`. Each minimal set selects exactly one axis
from each independent pair. `live_iff_hits` and `sufficient_iff_covers` connect
that characterization to the original liveness and emergence definitions.

This is a formal exponential-output example with only linearly many contract
rows. The gate additionally checks the executable paired-axis fixtures with
one through four groups: `2^(2k)` subsets and `2^k` minimal vectors. The
mathematical family theorem is universal in `k`; the Python fixture adapter and
its actual executions are checked on the stated finite cases.

Reported cumulative counters cover initialization and accepted semantic-event
pair/support operations. Restoration work is reported separately. Counters do
not account for every table scan, copy, normalization, sort, parse or
serialization, and are not wall-clock performance claims. The implementation
still validates the current table and renders every requested subset and
minimal vector. The full output contract can dominate an otherwise small
incremental update.

## Empirical outcome validation

[`incremental_check.py`](incremental_check.py) reconstructs each tested current
input independently of the materializer's state. The independent decoder in
[`verify.py`](verify.py) constructs a real `Hma.Inst` and evaluates the imported
Lean definitions. The gate compares complete outputs, including all subsets,
the full minimal list, selected vector, measures and axis dispositions. It
independently assembles the complete transcript, checks current input bytes in
each checkpoint, and runs both the original campaign and every checkpoint
suffix in two fresh processes for exact byte comparison. It fails when
agreement, replay, deterministic bytes, refusal controls or declared work
accounting fail.

Python pair enumeration is used separately to check operation counts. It does
not supply the gate's semantic outcome oracle. Recorded results are receipts
for the exact tested code and inputs. They establish neither physical fidelity
of supplied observations nor correctness for untested environments or arbitrary
future inputs. Arena regeneration and the original X/D/E controls retain their
own explicitly documented validation boundaries.
