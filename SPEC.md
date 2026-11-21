# Highest Minimal Axis — Specification

Program: HIGHEST MINIMAL AXIS. Directive (Chris, main chat, 2026-11-20 ~20:40 PST):
"solve the highest minimal axis/vector -> highest emergent live interacting /
interdepending allowed vector / functor/transformation and prove it and develop".

This spec is the contract for the proof (Deliverable 2) and the solver
(Deliverable 3). Every definition below is checkable and computable. Where the
program brief left a reading open, this spec picks one and names the choice.

## 0. Choices made where the brief left the reading open

- REFINEMENT READING (chosen): lexicographic refinement. The headline measure
  is the emergence measure mu (section 3). Sufficiency is stated against the
  full axis set (mu(S) = mu(A)), exactly as the brief's primary definition
  requires. Because every hyperedge weight is positive, equality of mu forces
  equality of the engaged structure (Lemma L2), so among minimal sufficient
  sets the headline measure cannot distinguish. The refinement coordinate is
  lambda(S) = the number of live components under S. The refinement vector is
  rho(S) = (mu(S), lambda(S)) under lexicographic order. Highest means maximal
  rho among minimal sufficient sets; on sufficient sets mu is constant, so
  highest is lambda-maximality there. This is non-vacuous: two minimal
  sufficient sets can engage the same hypergraph while differing in which
  isolated components they keep live (Instance X, section 6, exhibits this).
  The threshold reading (sufficiency against a target below mu(A)) was NOT
  chosen: it changes the meaning of sufficient away from "reaches the same
  emergence as varying all axes", which the brief states first.
- LEAN ENCODING (chosen): the proof uses one uniform finite value type V for
  all axes and one uniform finite value type W for all components. Per-axis
  ranges and per-component ranges are carved out by the contract and the
  behavior function, so no theorem loses generality: any per-axis instance is
  represented by embedding its ranges into V and restricting the contract.
- TRANSFORMATION SCOPE (chosen): the induced transformation is stated on
  variations (section 5). Its structure-preservation clause covers the
  emergent structure exactly — engaged hyperedges and the liveness of their
  vertices. Isolated components (in no engaged hyperedge) are not claimed
  preserved; they are precisely what the refinement coordinate lambda trades
  off. Stating preservation any wider would be false, and Instance X is the
  standing counterexample to the wider claim.

## 1. Universe

An instance is a tuple (A, V, C, B, W, F, H, w):

- A: a finite set of axes (names). An axis vector is a point of the product
  of the axis value sets. Finiteness is a consequence of qualification: a
  qualification picks out named axes and named criteria, so the axis set and
  each range are finite by what qualification is, never by an imposed bound.
- V: a finite value type (the Lean encoding's uniform axis value type).
  A configuration is a function x : A -> V. The configuration space is the
  full finite product.
- C: the contract — the allowed set of configurations, C a subset of the
  product. Any subset is a lawful contract, including the empty set and
  singletons; the degenerate readings are theorems (T5), not exclusions.
- B: a finite set of behavior components.
- W: a finite value type (the uniform component value type).
- F: the behavior function, F : (A -> V) -> (B -> W). F(x)(b) is component
  b's value at configuration x.
- H: the hypergraph — a finite family of subsets of B, the hyperedges,
  read on the one hypergraph (the total equivalence terms graph): a
  hyperedge is a set of components the machinery joins.
- w: a weight for each hyperedge, a positive natural number, required
  positive on every hyperedge of size at least 2. Default weight is 1.

## 2. Variation and liveness

- agreeOff(x, x', S): configurations x and x' agree off S when for every
  axis a not in S, x(a) = x'(a). A pair (x, x') with agreeOff(x, x', S) is
  an S-variation when both points lie in C.
- live(b, S): component b is live under S when some S-variation changes it:
  there exist x, x' in C with agreeOff(x, x', S) and F(x)(b) /= F(x')(b).
- Live(S): the set of components live under S.
- Note Live(empty) is always empty: agreement off the empty set is equality.

## 3. The emergence measure

- engaged(S): the hyperedges of size at least 2 entirely inside Live(S):
  { e in H : |e| >= 2 and e subset of Live(S) }. This is the interdependence
  closure of the live set in H: the largest part of H whose components are
  all live under S — the live interacting structure reachable by varying S
  alone within the contract.
- mu(S) = sum over e in engaged(S) of w(e). The emergence measure.
- lambda(S) = |Live(S)|. The refinement coordinate.
- rho(S) = (mu(S), lambda(S)), lexicographic.

Everything is computable from the instance: Live(S) by scanning pairs of C,
engaged and mu by finite sums. A measure that could not be computed from the
hypergraph and the contract would be a spec defect; this one is a finite
scan.

## 4. Sufficient, minimal, highest

- sufficient(S): mu(S) = mu(A).
- minimal(S): sufficient(S) and no proper subset of S is sufficient.
- highestMinimal(S): minimal(S) and rho(S') <= rho(S) for every minimal
  sufficient S'.
- The highest minimal axis vector of an instance is any S with
  highestMinimal(S). All such S share the same rho (T3), so the returned
  vector is unique up to rho-equivalence; a solver fixes one deterministically
  (section 7).
- An axis a is emergent-dead when removing it loses no liveness at all:
  Live(A without a) = Live(A). CORRECTED 2026-11-20 (the solver lane's
  validation refuted the original sentence on Instance X): a dead axis CAN
  belong to a minimal sufficient set — in Instance X, c is dead by this
  definition (Live({a, b}) = Live(A)) yet {c} is minimal sufficient, since
  deadness measures redundancy against all other axes present, while a
  minimal set may still route through that axis alone. The true claim is:
  a dead axis witnesses that A itself is not minimal, because A without a
  has the same Live, hence the same mu, hence is sufficient. Deadness and
  minimal-set membership are separate dispositions and are reported
  separately (section 7).

## 5. The induced transformation

Fix S. A variation over S is a pair (x, x') in C x C with agreeOff(x, x', S).
Variations over a fixed S compose: identity (x, x), and composition
(x, x') then (x', x'') gives (x, x''), lawful because agreement off S is an
equivalence on each fiber. The induced transformation T_S maps a variation
over S to the behavior variation (F(x), F(x')).

For the highest minimal S*, the transformation T = T_{S*} is the induced map
from the minimal axis vector to the full emergent behavior vector: an
S*-variation is exactly an allowed change of the minimal axis vector (the
complementary coordinates are shared between its endpoints), and T returns
the full behavior change it induces.

Functoriality claims (proved, T4):
- identity: T(x, x) is the identity behavior variation at F(x).
- composition: T of a composite variation is the composite of the T images.
- structure preservation: engaged(S*) = engaged(A), and every vertex of
  every engaged hyperedge is live under S*. So the transformation loses no
  emergent interdependence: every interaction the full axis set can produce
  is produced by varying the minimal vector alone.

## 6. Named instances

- Instance X (highest is non-vacuous). Axes {a, b, c}, values Bool, contract
  = all 8 configurations. Components {p, q, r, s}. One hyperedge {p, q},
  weight 1. Behavior: p = a xor c; q = a xor c; r = b; s = a. Then {a} and
  {c} are both minimal sufficient (each makes p and q live, engaging the
  hyperedge). lambda({a}) = 3 (p, q, s live; r is not, since r = b) and
  lambda({c}) = 2 (p, q live; r, s not). So {a} is the unique highest
  minimal vector, {c} is minimal but not highest — the standing refutation
  of "every minimal sufficient set is highest". (Implementers: recompute
  these numbers from the definitions when building the instance; the spec's
  arithmetic is itself checked by the solver's agreement run.)
- Instance D (degenerate, whole set). Axes {a, b, c}, values Bool, contract
  = {000, 111} exactly. Components {p, q}; hyperedge {p, q}, weight 1;
  p = a, q = b. The only pair in the contract differs on every axis, so
  Live(S) is empty for every proper S, mu(S) = 0 < 1 = mu(A), and the whole
  set A is the unique minimal sufficient vector, hence the highest minimal
  vector. The honest degenerate case.
- Instance E (empty and singleton contracts). Any axes and behavior, with
  C empty, or C a singleton. No variation exists, Live(S) is empty for all
  S, mu is identically 0, and the empty axis set is the unique highest
  minimal vector.

## 7. The solver contract

Input: an instance in the table form — named axes with finite value lists,
the contract as an explicit list of configurations (each a full axis
vector), named components, the behavior table (each component's value at
each contract configuration), the hyperedge list with weights. This table
is exactly F restricted to C; the Lean model is the same object with F a
function.

Computation (the spec's definitions, no second informal semantics):
- For each subset S of A and each component b: live(b, S) holds iff some
  pair of contract rows agreeing off S gives b different values.
  Equivalently, with D(x, x') the set of axes where two rows differ:
  live(b, S) iff some pair has D(x, x') subset of S and b differing.
- mu, lambda, rho per section 3. sufficient, minimal, highest per section 4.
- Search: enumerate all subsets (the space is finite by construction),
  collect the minimal sufficient sets, return one of maximal rho; ties
  beyond rho break by the lexicographically smallest sorted axis-name list,
  so the solver is a deterministic function of the instance.
- Output: the returned vector S*, rho(S*), mu(A), Live(A), engaged(A), the
  full list of minimal sufficient sets with their rho values, and for each
  axis its disposition: in S*, in some minimal sufficient set but not S*,
  in none, or emergent-dead (section 4 definition).
- Stated cost: exponential in the number of axes, polynomial in the square
  of the contract size times components and hyperedges. Qualified instances
  are small in axes by what qualification is; the solver prints its counts.

Validation bars (Deliverable 3): (a) on Instance X the solver returns {a}
and an independent brute force over all subsets agrees on the full minimal
sufficient list and the rho ordering; (b) on Instance D the solver returns
the whole set; (c) the arena instance (built from the arena model) runs
through the same solver with no special-casing.

## 8. Theorems required of the proof

- L1 (monotonicity): S subset of T implies Live(S) subset of Live(T),
  mu(S) <= mu(T), lambda(S) <= lambda(T).
- L2 (structure forcing): sufficient(S) implies engaged(S) = engaged(A).
- T1 (existence): for every instance, some S has highestMinimal(S).
- T2 (minimality): highestMinimal(S) implies every proper subset S' of S
  has mu(S') < mu(A).
- T3 (maximality and rho uniqueness): highestMinimal(S) and minimal(S')
  imply rho(S') <= rho(S); and any two highest minimal sets have equal rho.
- T4 (functoriality): the identity and composition laws of section 5, and
  structure preservation: highestMinimal(S*) implies engaged(S*) =
  engaged(A) and every engaged hyperedge is a subset of Live(S*).
- T5 (degenerate characterization): no proper subset of A is sufficient
  if and only if every highest minimal set equals A. Corollaries: Instance
  D's answer is A; under an empty or singleton contract the unique highest
  minimal vector is the empty set (Instance E).
- Standing controls in-tree: Instances X, D, E as decidable checks that the
  definitions compute the claimed answers (including: in Instance X, {c}
  is minimal and not highest; in Instance D, no proper subset is
  sufficient). Controls use kernel decide only — native decide adds an
  axiom outside the standard three and is barred by the axiom audit.
