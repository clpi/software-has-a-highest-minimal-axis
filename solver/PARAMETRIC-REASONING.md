# Online parametric Pareto reasoning

The finite decision universe, its qualifications, the cost coordinates, the
supported outcomes and the decision horizon are explicit inputs. The executable
Lean functions compute exact frontiers and optimal policies within those inputs.
They carry proofs that their current caches produce those results. Python handles
the external protocol and independent checks; it remains a checked implementation.

The original SPEC highest-minimal output keeps its original meaning. The resource
Pareto view adds a separate choice over every minimal sufficient vector. It does
not rename a resource-preferred alternative as the original highest vector.

## Four executable lanes

One fixed executable supports four persistent JSON-lines lanes. It is compiled
before receiving the input model or any events. New inputs are read one request
at a time, with no generated source for the future campaign.

| Lane | Current problem | Actual carried state |
| --- | --- | --- |
| `hma` | SPEC finite-table computation | Current typed input, materialized pair-witness map, sequence/epoch |
| `pareto` | Complete qualified catalogue or HMA minimal-vector resource view | Current profiles, pair-comparison cells, exact frontier regions |
| `controller` | Finite-horizon worst-case scalar cost | Current finite model, parameters, state, all Bellman layers, accumulated cost vector |
| `policy` | Complete budget-feasible adaptive-policy Pareto frontier | Current finite model, policy profiles and dependencies, comparison cells, remaining component budgets |

Run a lane using the public driver:

```sh
LEAN=lean python3 solver/reasoning.py controller < requests.jsonl
LEAN=lean python3 solver/reasoning.py policy < requests.jsonl
```

The driver builds one fixed binary for all lanes. To reuse that exact binary:

```sh
LEAN=lean python3 solver/reasoning.py hma --build-only /tmp/hma-reasoning
python3 solver/reasoning.py controller --binary /tmp/hma-reasoning/hma-reasoning < requests.jsonl
```

For original named HMA instances and append/remove/replace/edge events, the
`solver/online.py` adapter supplies strict typed encoding to the native `hma`
lane. The lower-level native lanes use explicit finite identifiers. JSON labels
for HMA values preserve distinctions such as `false`, `0`, `"0"`, and `null`.

After startup, mutating requests use the next sequence number and current epoch. A
rejection leaves the preceding state available for the next valid request.
`inspect` preserves the delivery clock. The `hma`, `controller`, and `policy`
lanes also expose an in-process `checkpoint` reconstruction that preserves it.
A schema `rebase` advances the epoch. Current-state reconstruction includes the parameters and any remaining
cost commitment; a selected answer alone is insufficient.

For example, the `pareto` lane accepts these two JSON lines:

```jsonl
{"op":"start","dimensions":2,"catalogue":[{"id":1,"profile":[0,3]},{"id":2,"profile":[2,2]},{"id":3,"profile":[3,0]}],"weights":[1,0]}
{"op":"weights","seq":1,"epoch":0,"weights":[0,1]}
```

The selected identity changes from 1 to 3. Both outputs retain all three Pareto
identities and their parameter regions. The second request performs zero new
dominance evaluations. Use the returned `next_seq` and `epoch` for the next
request. The executable gate campaigns in `pareto_check.py`,
`controller_check.py`, and `policy_check.py` provide complete model and update
examples for their respective protocols.

## Exact Pareto frontiers and all-parameter regions

`ParametricPareto.lean` reuses `FiniteFrontier.strictPareto` from the pinned
software-optimality import. Every coordinate is minimized. A point dominates
another only when it is no worse on every declared coordinate and strictly
better on at least one. Distinct identities with equal costs remain distinct
frontier points.

The state contains the complete current qualified catalogue and materialized
ordered-pair comparison cells. Keeping dominated points matters: a withdrawn
dominator can expose a previously dominated point. Reconciliation reuses a cell
only when the objective schema and both complete point identities/profiles still
agree. A changed profile cannot borrow a comparison for its former value.

The computed frontier is proved equal to the original finite frontier relation.
The proof also supplies a no-worse frontier representative of every catalogue
point. It does not assume a caller-supplied claim that the chosen catalogue has
already been optimized.

Generic Pareto profiles and HMA resource costs are integers, including negative
values. Preference weights are nonnegative integers. The controller and policy
lanes use nonnegative integer stage and terminal costs; their input decoders
reject negative costs.

For arbitrary nonnegative integer parameters `w`, selection minimizes

\[
  \sum_i w_i c_i(p)
\]

over the entire qualified catalogue. Ties use the sum of the full cost profile,
then the stable numeric identity. The secondary comparison ensures that zero
weights do not select a dominated point. A positive common scaling of all
weights preserves the selected identity. Exact rational weight ratios can
therefore be represented by a common integer denominator; arbitrary floating
point arithmetic is not part of this interface.

The executable also materializes a region for each Pareto point `p`. Its rows
are coefficient vectors `c(q) - c(p)` for every catalogue point `q`. The region
theorem proves, for every parameter vector, that

\[
  \forall q,\quad w\cdot(c(q)-c(p))\ge 0
\]

holds exactly when `p` is a global minimum of the primary weighted objective.
Parameter-only changes reuse the current regions, frontier and comparison
state. Active regions can overlap at ties. They describe primary optimality;
the deterministic secondary comparison still selects one result.

The complete Pareto frontier is broader than the set of points selected by
positive linear weights. A kernel control preserves `(2,2)` on the frontier
between `(0,3)` and `(3,0)` and proves that its primary-optimality region contains
only the all-zero nonnegative weights. No unsupported point is silently dropped
from the frontier.

### HMA connection

`HmaPareto.lean` derives candidates directly from the proof-carrying complete
renderer. Candidate membership is equivalent to the original `Hma.minimal`
predicate over the complete canonical subset space. The cost profile is

```text
[axis count, negative live-component count, sum of declared axis resource costs]
```

The live-component coordinate is proved equal to the original `Hma.lam`.
Resource costs are explicit declarations, not inferred wall-clock measurements.
The selected resource vector is proved minimal sufficient, Pareto-nondominated,
and globally weighted-optimal among all minimal sufficient vectors. It preserves
the original engaged hyperedges by the sufficiency theorem.

For X, the original highest-minimal result remains `{a}`. With a resource cost
of 10 for `a` and 0 for `c`, the resource frontier contains both vectors:
`{a}` retains more live components, while `{c}` has lower declared resource cost.
Different parameters choose different members without changing the SPEC result.
`OnlinePareto.lean` obtains these candidates from `HmaReplay.finish` directly;
it does not reconstruct the semantics from a second JSON interpretation.

## Globally optimal scalar control with incremental recertification

`OptimalController.lean` defines an adaptive policy as a finite tree. At each
step the policy chooses an admitted action; a supported observation chooses its
continuation. The model declares finite nonempty action and outcome lists,
successor states, stage costs and terminal costs.

The actual Bellman functions implement

\[
V_0(s)=T(s),\qquad
V_{h+1}(s)=\min_{a\in A(s)}\max_{o\in O(s,a)}
  \bigl(C(s,a,o)+V_h(N(s,a,o))\bigr).
\]

Theorems establish admitted selection, attainment of the value, and comparison
with **every admissible adaptive policy tree** of that horizon. An optimality
premise is not supplied by the caller. The observation/replay theorems establish
the remaining-horizon count and the cumulative spent-plus-continuation bound
for a fixed model and parameters.

`ControllerRefinement.lean` connects the actual
`OnlineController.acceptOutcome` function to that proved transition, including
its refusal behavior, state, horizon, accumulated cost vector and counters.
Its cumulative bound therefore applies to accepted finite prefixes of the
executed pure transition function, not just to an abstract controller model.

`IncrementalControl.lean` materializes the values for every finite state and
every remaining horizon. After model or parameter changes it compares local
action/outcome lists, successors and scalar costs. A layer cell needs a new
Bellman backup if its local model changed or one of its successor values changed
in the lower layer. Equal lower values stop propagation even if their internal
optimal choices changed. Current action selection reads the current model.

The cache update is proved exact against the uncached Bellman function, which
transfers global policy optimality to the actual cached values and selections.
An unchanged model and parameter set perform zero new Bellman backups or changed
terminal-cell writes. A four-state, three-step kernel control changes 9 of 16
stored values/cells under its dependency rule, and a fresh full-tree oracle
checks the same result. The materialized value-cell count is exactly
`(horizon + 1) * numberOfStates`, independent of event history.

The work receipt counts changed terminal cells plus recomputed Bellman cells.
It does not count every terminal evaluation, dependency comparison, list lookup,
allocation, parser operation, or serialized output byte. Reordering declared
actions or outcomes can conservatively trigger extra work. This is not a proof
of the smallest possible machine-time update.

## Complete adaptive-policy search and committed Pareto optimality

The scalar objective above is

\[
\max_{\text{trace}}\sum_i w_i\,\operatorname{cost}_i(\text{trace}).
\]

The `policy` lane instead keeps each coordinate's worst complete-trace cost,
then applies preferences to that vector:

\[
c_i(\pi)=\max_{\text{supported trace of }\pi}
  \operatorname{cost}_i(\text{trace}),\qquad
\sum_i w_i c_i(\pi).
\]

These objectives can disagree. The kernel controls and executable checks include
an example where scalar minimax chooses one action and the vector frontier
strictly excludes it. The APIs name their objective explicitly.

`ParetoPolicy.lean` enumerates every finite adaptive tree over the declared
action/outcome carriers, then checks structural admissibility. Its completeness
theorem quantifies over all adaptive policies, including history-dependent
policies whose two histories reach the same model state. Policy identity is the
index in the complete syntactic enumeration, so withdrawing an action does not
renumber unrelated policies.

Every materialized policy record contains its exact profile, admission flag and
dependency footprint. The footprint distinguishes terminal costs from branch
sources. A reusable branch requires agreement on action/outcome lists,
successors and every declared cost coordinate. New outcomes therefore invalidate
the old support. Footprint reuse is proved to preserve admission, profile and
dependencies, and the refreshed cache is proved equal to a fresh exhaustive
cache. The Pareto comparison cache then updates only affected profile pairs.

Parameter-only changes need no policy-profile or dominance reevaluation. A
changed cost under a currently zero scalar weight still changes the stored raw
model and the vector profile where relevant; restoring positive weights observes
the new cost rather than an obsolete one.

### Preserving the committed vector while reasoning continuously

Unrestricted reoptimization of coordinatewise worst-case vectors is generally
time-inconsistent. A control demonstrates an initially optimal `[10,10]` policy
whose unrestricted later reoptimization could accumulate `[0,20]`.

The online policy lane fixes this by committing the selected initial profile
as a componentwise bound. Each accepted observation adds its actual modeled
component costs to the accumulated vector and subtracts them from the remaining
budget. Subsequent policies must fit that remaining budget.

Initial selection searches the unrestricted admissible policy universe before
creating the commitment. The emitted catalogue and frontier then cover every
budget-feasible policy; they can omit unrestricted Pareto alternatives whose
profiles exceed that commitment. The generic `ParetoPolicy` functions also
compute the unrestricted frontier. To choose a different component commitment,
the online protocol requires an explicit rebase.

The carried arithmetic invariant is

\[
\operatorname{spent}_i+\operatorname{budget}_i
=\operatorname{initialBound}_i.
\]

The selected policy satisfies

\[
\operatorname{spent}_i+c_i(\pi_{\text{remaining}})
\le\operatorname{initialBound}_i.
\]

A supported outcome from the actual selected record is proved to have an
accepted feasible continuation. The complete remaining catalogue contains that
continuation; feasibility is derived rather than assumed. Reoptimization is
weighted-optimal among every budget-feasible adaptive policy. Pareto
nondominance still holds against all structurally admissible policies, because
any componentwise dominator would also fit the downward-closed budget box.
The actual session totality theorem also proves that every carried state with
a positive remaining horizon has a selected cached record and root action;
successful selection is not an assumed lookup premise.

Parameter changes preserve the commitment. Model revisions must retain a
feasible continuation or reject atomically. An explicit rebase starts a new
commitment epoch. Changing preferences does not make past choices retrospectively
optimal under the new weights. Accumulated cost vectors belong to their current
schema/commitment epoch; a rebase does not add numbers whose coordinate meanings
have changed.

At a changed observed state and reduced horizon, the policy lane constructs the
new remaining-policy problem. That reconstruction is counted explicitly; it is
not reported as a zero-cost suffix update. The scalar controller can instead
retain its already computed lower Bellman layers across supported observations.

## Empirical autonomous qualification

`autonomous_check.py` runs an actual decision-and-observation loop. Its finite
task is to qualify all eight X rows in at most three nonempty batches. Every
batch size from 0 through 8 is represented in the action carrier; admissibility
rejects impossible batches and requires completion in the final slot. The
complete three-step policy universe has 729 trees and 29 admitted schedules.

The cost coordinates are actual incident-pair work, submission count, and an
explicit declared batch charge `batchSize^2`. The last coordinate is a tariff
used to exercise parametric tradeoffs, not an empirical CPU-time estimate.

The loop asks the policy engine for the next action, appends exactly that batch
to the persistent HMA engine, checks its complete result against the original
Lean definitions, verifies the observed pair work against the model, and only
then admits the outcome to the policy engine. It repeats without a precompiled
campaign. Unsupported or altered measurements are refused by the harness.

The unrestricted initial problem has three nondominated cost vectors, with all
equal-cost identities retained by its complete frontier:

```text
[28, 1, 64]
[28, 2, 32]
[28, 3, 22]
```

The independent checker enumerates the entire bounded schedule universe and
checks initial global optimality, every later budget-feasible optimum, global
Pareto nondominance and the cumulative bound. Reparameterization cannot silently
abandon a prior component commitment. Every completed run qualifies all eight
rows and introduces all 28 unordered pairs once.

This empirically validates the executed finite model and these observations.
It does not authenticate arbitrary supplied measurements or establish that
every external system follows the declared transition/cost model.

## Counting, evidence and limits

With `r` retained unchanged profile identities and `k` freshly appended points,
the comparison update evaluates `2*r*k + k*k` new ordered comparisons. The
append-only count telescopes to the final catalogue size squared minus the
initial size squared. Removing candidates requires no new dominance evaluations;
the retained comparison cells still reveal any resurrected frontier points.
Profile changes or objective-schema changes have their own exact counts.
Reconciliation still materializes the current square comparison matrix, and
region output can contain `frontierSize * catalogueSize * dimensions`
coefficients. Zero new dominance evaluations does not mean zero reconstruction
or output work.

For complete policy enumeration, `P(0)=1` and

\[
P(h+1)=a\,P(h)^o,
\]

where `a` and `o` are the declared action and outcome carrier sizes. This can
grow doubly exponentially in the horizon. The complete policy Pareto lane pays
that explicit cost; no sampled or heuristically truncated policy universe is
presented as complete. Its retained state is current-problem state, not an
unbounded record of previous events. Storage counts do not bound the complete
runtime heap, policy-tree sharing, compiler output, or serialization memory.

`proof/check.sh` cold-compiles and audits every Lean source, preserves the
original 58 source bytes and exact axiom sets, and runs the existing HMA gates
plus every online lane and the autonomous qualification loop. Native transcripts
are compared byte for byte across fresh processes. Recorded reports are checked
against new execution; ordinary gate runs cannot rewrite them into agreement.
`ReasoningControls.lean` contains concrete kernel proofs, and
`reasoning_certificate_check.py` separately rejects false nearby result claims.

The detailed receipts are `results/online.json`, `pareto.json`, `controller.json`,
`policy.json`, `autonomous.json`, and `reasoning-certificates.json`. The full
gate receipt remains `proof/CHECK.log`.

The universal claims concern the actual Lean functions and explicit premises.
External parsing/encoding, the compiler, runtime, operating system and measured
model fidelity remain checked boundaries. Optimality is relative to the named
finite qualified universe, coordinates, outcome model, horizon and current
component commitments. There is no claim of universal optimal intelligence,
optimality over undeclared actions, optimality for an unbounded unknown future,
or a globally fastest implementation. The protocol is an ordered local process;
distributed consensus, durable storage and crash recovery remain outside it.
