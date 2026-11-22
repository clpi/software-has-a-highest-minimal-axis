# software-has-a-highest-minimal-axis

A qualified parametric system — named axes, a contract of
allowed configurations, a behavior function on finite
components, and a hypergraph joining the components —
always has a highest minimal axis vector: an inclusion-minimal axis
set whose variation inside the contract already produces
the full emergent live interacting structure, and among
those minimal sets one whose refinement vector
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
  verdict at founding: PASS. The original 58 theorem sources and their
  per-theorem axiom sets are retained by the current gate.
- solver/ — a deterministic executable implementation of SPEC.md section 7,
  an independent decoder and Lean-definition checker, X/D/E fixtures, and the
  recovered 1,152-row arena instance. The solver returns the chosen vector,
  every minimal vector, per-axis dispositions, and every subset's measurements.
  It is an **implementation checked against the proved definitions**, not a
  new theorem establishing correctness of the Python program for all inputs.
- proof/FiniteCheck.lean — five additional bridge lemmas equating executable
  finite-table views with the existing `Hma` definitions. These support the
  checker; they do not prove the external solver or decoder correct.
- [solver/README.md](solver/README.md) — input/output contract, commands,
  checking mechanism, results, and the not-landed / cannot-say list.
- [solver/arena/README.md](solver/arena/README.md) — exact source pin,
  reproducible arena extraction, and lossless table encoding.

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

Run from the repository root with Lean 4.19.0, Python 3.10 or newer,
and Node.js on the path:

    LEAN=lean sh proof/check.sh

The gate cold-compiles every Lean file in the repository with warnings as
errors, audits the original 58 theorems and the five checker bridges, checks
the arena's source/table correspondence, compares every solver result with
Lean's definitions, and compares two independent solver runs byte for byte.
Wrong outputs, incomplete results, stale recorded outputs, malformed input,
missing tools, or checker failures reject the run. GitHub Actions runs the same
gate. The current receipt is [proof/CHECK.log](proof/CHECK.log); complete
per-instance outputs are in [solver/results](solver/results).

For example:

```sh
python3 solver/solve.py solver/instances/X.json
python3 solver/solve.py solver/instances/arena.json
```

The arena selects `{count}`, with `rho = (4,5)`. Its full minimal list is
`{count}`, `{material}`, `{motion}`, `{place}`, all with the same `rho`.
The name-order tie break chooses `{count}`. Inclusion minimality does not mean
minimum cardinality: the `tie` control deliberately chooses `{a,b}` over `{c}`.
