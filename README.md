# software-has-a-highest-minimal-axis

A qualified parametric system — named axes, a contract of
allowed configurations, a behavior function on finite
components, and a hypergraph joining the components —
always has a highest minimal axis vector: a smallest axis
set whose variation inside the contract already produces
the full emergent live interacting structure, and among
those smallest sets one whose refinement vector
(mu, lambda), emergence first and live count second, is
maximal. The induced transformation from variations of
that minimal vector to behavior variations loses no
engaged hyperedge.

## Contents

- SPEC.md — the object, defined at agent proof
  resolution: the universe, variation and liveness, the
  emergence measure and the refinement vector,
  sufficiency, minimality and highest minimality, the
  induced transformation, the named Instances X, D, and
  E, the solver contract, and the theorem list.
- proof/ — the Lean core: 58 theorems (the finite list
  machinery, monotonicity L1, structure forcing L2,
  existence T1, minimality T2, maximality and rho
  uniqueness T3, functoriality T4, the degenerate
  characterization T5 with its empty and singleton
  contract corollary, the corrected dead axis facts, and
  sixteen standing controls on Instances X, D, and E).
  The family gate: proof/check.sh, cold, Lean 4.19.0,
  warnings as errors, escape scan, dependency audit
  inside {propext, Classical.choice, Quot.sound}. Gate
  verdict at founding: PASS (proof/CHECK.log).

## Headline results

- Monotonicity (L1): under a subset of axes, the live
  set, mu, and lambda all grow.
- Structure forcing (L2): a sufficient axis set engages
  exactly the hyperedges the full axis set engages; the
  positivity of the hyperedge weights is load bearing,
  through a strict sum step.
- Existence (T1): every instance has a highest minimal
  axis set, by descent on axis count to a minimal
  sufficient set and ascent on the refinement coordinate.
- Minimality (T2): every proper subset of a highest
  minimal set has mu strictly below the full mu.
- Maximality and uniqueness (T3): a highest minimal set
  stands over every minimal sufficient set in the
  lexicographic refinement order, and any two highest
  minimal sets share the same rho.
- Functoriality (T4): variations compose, the induced
  transformation respects identity and composition, and
  it preserves the engaged structure exactly.
- Degenerate characterization (T5): no proper subset of
  the full axis set is sufficient if and only if every
  highest minimal set is the full axis set. Instance D
  is the whole set case; under an empty or singleton
  contract the unique highest minimal vector is the
  empty set (Instance E).
- Highest is not vacuous (Instance X): {a} and {c} are
  both minimal sufficient, rho({a}) = (1, 3) against
  rho({c}) = (1, 2), so {a} is the unique highest
  minimal vector and {c} is minimal but not highest.
- The dead axis correction: axis c of Instance X is
  emergent-dead and {c} is minimal sufficient, so a dead
  axis can belong to a minimal sufficient set. The true
  claim, proved in the core, is that removing a dead
  axis is already sufficient, so a dead axis makes the
  full axis set non-minimal.

## Gate

Run cold from the proof directory, with the pinned
Lean 4.19.0 on the path:

    cd proof
    LEAN=lean sh check.sh

The gate rejects every proof escape token in every Lean
file, compiles with warnings as errors, and audits the
printed foundational principles of all 58 theorems
against the allowed set {propext, Classical.choice,
Quot.sound}. Founding verdict: PASS; the run is recorded
in proof/CHECK.log.
