# Executable witness maintenance and incremental certification

The Python solver remains an **implementation checked against the proved
definitions**. This addition also supplies a Lean implementation whose actual
materialized transitions and complete result renderer have correctness proofs.
It closes the previous gap between the abstract function-valued cache and the
executed counting representation. It does not turn the Python decoder, Python
materializer, JSON serialization, Lean compiler, or operating system into
kernel-verified programs.

## The actual carried invariant

[`ExecutableWitness.lean`](../proof/ExecutableWitness.lean) uses `Std.HashMap`
with keys `(difference-list, component)` and natural-number multiplicities.
The state contains current configuration rows and this finite map. It contains
no prior state, event journal, individual pair records, or chain of delayed
counting functions.

For every key `(D,b)`, `Valid I state` establishes

\[
\operatorname{read}(state.hist,(D,b))=
\#\{\{x,y\}\subseteq state.rows:
  D(x,y)=D\ \land\ I.beh(x,b)\ne I.beh(y,b)\},
\]

for declared components, and zero for undeclared components. Every stored cell
is positive. The component list must contain no duplicates, matching the JSON
set contract. The proofs use the standard library's hash-map lookup/update
lemmas; hash buckets are not assumed to have informal dictionary semantics.

`append` computes only the new row's incident pairs and updates their cells.
`remove` locates the active row and subtracts exactly its incident support.
`append_valid` and `remove_valid` prove the resulting concrete map valid.
`replay_valid` and `every_prefix_exact` extend this to accepted mixed prefixes.
`liveList_exact` identifies the executable map query with **the original
`Hma.livelist`**, through the already proved exact-difference witness reading.

`stored_cells_bound` proves that the number of materialized cells is at most
`length(sublists axes) * length(comps)`, hence `2^n * m`. The bound depends on
the current finite universe, not elapsed event history. Current rows remain
necessary input unless an equivalent reconstruction mechanism is supplied.

## Behavior changes and schema changes

[`CertifiedReplay.lean`](../proof/CertifiedReplay.lean) carries a subtype pairing
each actual map with its `Valid` proof. Its executed `reconcile` function:

1. Removes withdrawn rows and rows whose observed behavior changes, using the
   old behavior function.
2. Checks equal axis/component lists and equality of behavior on every retained
   row/component. `compatible_valid` transfers the existing materialized map
   to the new instance under those finite premises.
3. Adds new/replaced rows using the new behavior function.

There is no recomputation of retained-to-retained row pairs. Edge and weight
changes need no pair update; the result renderer reads the new declarations.
`Session.advance` checks the next sequence number and epoch. A rejected pure
transition returns no successor and cannot mutate its input value.

`rebase` permits a different axis, value, component, and behavior carrier type.
It rebuilds the new instance and advances the epoch. It carries the sequence
boundary across the change and does not reuse positional masks from another
axis universe. This is an explicit reconstruction boundary.

Before exposing an observation, `finish` checks `RowsMatch`: the active rows
and requested instance contract have the same membership. It then returns an
`Output I` whose fields include the actual rendered value and
`HmaCertified.RenderCorrect I value`. The result cannot be certified merely
because a cache is internally consistent with a different input.

## Complete output, including the tie-break

[`CertifiedTable.lean`](../proof/CertifiedTable.lean) implements the finite
subset enumeration and complete output. `render_correct` and the accompanying
ordering and uniqueness theorems prove these facts about the actual returned
structure:

| Returned field | Proved meaning |
| --- | --- |
| Full-axis snapshot | Original live list, engaged edges and `rho` |
| Every subset and its flags | Original `sufficient`, `minimal`, `highest` |
| Complete minimal/highest lists | Membership iff the original predicate, with coverage and no duplicate axis keys |
| Chosen vector | Exists and satisfies original `Hma.highest` |
| Tie-break using `finLexPrefer` | No lexicographically smaller highest candidate |
| Axis dispositions | Membership in the chosen/minimal families, separately from original `Hma.dead` |

The adapter assigns `Fin` indices in sorted axis-name order, so numeric
lexicographic order implements SPEC's sorted-name tie-break. That assignment
is an explicitly checked encoding boundary. All selections and dispositions
are computed in Lean; the adapter only translates the verified fields back to
their external names and checks that every translation agrees.

`HmaReplay.certified_hypergraph` connects the executed live-list query directly
to `HypergraphIncremental.derives (HmaGraph.graph I S) (.live b)`. The graph uses
the pinned existing all-premise closure. All differing-axis premises and both
row premises are required; ordinary pairwise reachability is not substituted
for hypergraph derivability.

## Incremental kernel certificates

[`certificate_check.py`](certificate_check.py) generates named certificates
for concrete carried states and complete supplied outcomes. The previous
certified state is materialized as literal current rows and support entries.
A subsequent certificate checks the incident-row contribution against that
previous materialization. It does not unfold the entire historical update
chain or redo all previous row-pair searches.

The kernel reduces finite serialized entries, key equality, support arithmetic
and the supplied result checks. Proved `Std.HashMap` lookup lemmas connect those
finite checks to the actual executable map. The gate does not use native proof
evaluation or pretend that executing the compiled hash table is itself a
kernel proof of a particular output. Invalid multiplicities and output claims
must fail compilation of the corresponding claimed certificate.

[`certified.py`](certified.py) is the separately executed Lean backend. Its
generated program carries the proved states through an entire campaign in one
process and uses `finish` at each prefix. It does not invoke the original full
pair-search checker anew at every update. The gate compares every positive
support cell and every output field with the Python materializer. A hidden
positive-count error is therefore rejected immediately, even if current live
bits and selected output still happen to agree. `occupancy_exact` also connects
the reference's occupied-difference counts to the original `occupiedCount`;
every Python subset-support count and live bit is checked against that output.
The independently replayed current input is compared with both Python copies
of retained row data, so a hidden row-map error is rejected at the same prefix.

## Reconstruction, cumulative work, and exponential size

`checkpoint_replay` proves future mixed-event equivalence after rebuilding a
valid concrete map from retained current rows. Equality is extensional: active
rows and all support counts agree, regardless of hash-bucket layout. Past
provenance is not a premise. A different mechanism that reconstructs the same
current semantic input can discharge the same requirement.

For pure append growth, each unordered pair is introduced exactly once, giving
`m(m-1)/2` pairs cumulatively. Removing and restoring a row can legitimately
evaluate its incident pairs again. Counters distinguish these cumulative
evaluations from current storage. They do not count all validation, lookup,
copying, rendering, compilation or serialization work.

The independent exponential construction remains an actual HMA family:
`2k` axes, `2k+1` distinct rows and exactly `2^k` highest minimal vectors.
The explicit subset renderer emits `2^n` subsets. Incremental maintenance does
not erase these output costs or establish a universal wall-time speedup.

## Running and reviewing

Run the complete gate with `LEAN=lean sh proof/check.sh`. It cold-compiles and
audits all modules, preserves the original 58 proofs and exact axiom states,
runs the original definition checker, executes the proved backend, checks
kernel certificates, and runs the incremental engine merged on main.

The executable backend can also run a single instance or an ordered campaign.
It cold-builds its dependency closure automatically; `--lean-dir` optionally
uses a separately cold-built module directory:

```sh
LEAN=lean python3 solver/certified.py solver/instances/arena.json
LEAN=lean python3 solver/certified.py campaign.json --campaign
LEAN=lean python3 solver/certificate_check.py --emit-dir /tmp/hma-certificate-sources
```

The compiled program runs twice in independent processes and its complete
output must agree byte for byte. The campaign gate covers X/D/E, the arena,
mixed behavior/edge updates, schema changes and the exponential controls.
Selected checkpoints are rebuilt inside the Lean execution and their suffix
receipts must agree. The existing Python gate still reconstructs every tested
checkpoint and checks every future suffix independently against HMA.

The source/campaign execution digests and per-prefix results are recorded in
[`results/certified.json`](results/certified.json); concrete certificate results
are recorded in [`results/certificates.json`](results/certificates.json).
The certificate gate covers 7 campaigns, 53 prefixes, and 106 named
validity/outcome proofs. It generates no closed kernel theorem for the full
arena result: arena evidence is execution of the proved backend plus the
independent original-definition checker. The complete cold receipt is
[`proof/CHECK.log`](../proof/CHECK.log). The final gate also rejects any change
to its input files during validation.

## Remaining boundaries

The universal theorems concern the actual Lean pure functions and their stated
finite-input premises. Python execution and byte encoding remain checked
implementations. The older `certified.py` command compiles a supplied finite
campaign ahead of execution, including its input tables. Its state-storage
theorem does not bound that whole generated binary or Python staging process
by current-state size. The additional fixed executable in
[PARAMETRIC-REASONING.md](PARAMETRIC-REASONING.md) accepts online requests after
compilation and carries the same certified current state without receiving
future campaign inputs. Arena output is
evidence for the pinned executable model and
specified instance, not physical-world or all-seed validity. Reconstruction
does not authenticate invented measurements or recover discarded historical
prefixes. The ordered adapter does not implement distributed merge, permanent
identity tombstones, durable storage or crash recovery. A separate variation
composition API is still outside SPEC section 7's solver output contract.
There is no general theorem that every schema-compatible reconciliation is
accepted; every accepted Lean output is certified, and `solve` is total for
its stated finite-input premises. General delivery fencing is established by
the Session proofs and runtime checks. The certificate gate's stale-sequence
attack separately checks rejection of a false closed sequence assertion.
