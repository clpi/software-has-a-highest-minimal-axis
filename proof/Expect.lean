/-
  The expectations program for the solver gate.

  This file is not a proof. It computes, for each named
  instance, the values the solver contract of SPEC.md
  section 7 requires, by evaluating the proved definitions
  of the core module directly: livelist, engagedlist, mu,
  lam, and dead are the definitions of Hma.lean, applied to
  the control instances of Controls.lean (Instances X, D,
  and both forms of E) and to the coded arena instances of
  Arena.lean. The gate script runs this program and
  compares its output, line for line, with the solver's
  output on the same instances; any disagreement fails the
  gate.

  The mechanical route, stated once: every axis set of an
  instance is named by a sublist of the axis list (the core
  proves this as subsetrep), so enumerating sublists of the
  axis list evaluates the definitions over every axis set.
  Sufficiency is mu reaching the full axis set's mu;
  minimality is sufficiency with no proper sublist
  sufficient; both are read off the computed table. The one
  rule applied beyond the definitions is the contract's
  own deterministic selection of section 7: among the
  minimal sufficient sets take maximal rho, and break ties
  beyond rho by the smallest sorted axis name list. The
  emergent-dead flag is the core's dead predicate, decided
  on the definitions.

  A claim is exactly what is checked here: the solver is an
  implementation checked against the proved definitions on
  these instances, not a new theorem.

  Three proved identities keep the evaluation shared and
  fast. The core's mu and engagedlist each recompute the
  live list once per hyperedge member, and a direct
  evaluation of live itself rescans every contract pair
  for every axis set and component. The lemmas below are
  proved from the definitions in this file: the engaged
  list is the edge filter read off one computed live list;
  mu is the weight sum over the engaged list; and the live
  list is read off the instance's pair table, where each
  contract pair is stored once with the set of axes the
  pair differs on and the set of components the pair
  separates, a component being live under an axis set
  exactly when some stored pair whose difference set lies
  inside the axis set separates it. That third identity is
  the difference-set form of liveness the contract's
  section 7 states, here proved against the definition of
  live. The program builds the pair table once per
  instance, reads lam off the live list, which is lam's
  defining body, and decides the emergent-dead flag by the
  definition directly. Everything the gate compares is
  therefore the definitions' own values, with the sharing
  certified by proof rather than by a second reading of
  the definitions.

  The gate builds this program as a native executable:
  under the interpreter the pair scans of the arena
  instances run for minutes, natively for seconds, with
  the same output either way.
-/

import Hma
import Controls
import Arena

open Hma

namespace Expect

/-- The engaged list read off one computed live list:
    the edge filter whose membership test is the engaged
    predicate with its live list already evaluated. Proved
    from the definitions by filter congruence. -/
theorem engagedlisteq {A V B W : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq V] [DecidableEq W] (I : Inst A V B W) (S : A → Bool) :
    engagedlist I S = I.edges.filter
      (fun e => decide (2 ≤ e.length ∧ ∀ b ∈ e, b ∈ livelist I S)) := by
  unfold engagedlist
  apply filtercongr
  intro e he
  rw [decide_eq_decide]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨he, h.1, h.2⟩⟩

/-- The weight sum over a filtered edge list is the map
    and sum form of mu, list by list. -/
theorem mapifsum {A V B W : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq V] [DecidableEq W] (I : Inst A V B W) (S : A → Bool) :
    ∀ l : List (List B),
      (l.map (fun e => if engaged I S e then I.weight e else 0)).sum =
        ((l.filter (fun e => decide (engaged I S e))).map I.weight).sum
  | [] => rfl
  | a :: l => by
    by_cases h : engaged I S a
    · rw [List.map_cons, List.sum_cons, if_pos h, List.filter_cons,
        if_pos (decide_eq_true h), List.map_cons, List.sum_cons,
        mapifsum I S l]
    · have hnc : ¬ (decide (engaged I S a) = true) := by
        rw [decide_eq_false h]
        exact Bool.false_ne_true
      rw [List.map_cons, List.sum_cons, if_neg h, List.filter_cons,
        if_neg hnc, mapifsum I S l, Nat.zero_add]

/-- mu is the weight sum over the engaged list. Proved
    from the definitions. -/
theorem musum {A V B W : Type} [DecidableEq A] [DecidableEq B]
    [DecidableEq V] [DecidableEq W] (I : Inst A V B W) (S : A → Bool) :
    mu I S = ((engagedlist I S).map I.weight).sum := by
  unfold mu engagedlist
  exact mapifsum I S I.edges

/-- Set inclusion between two named axis sets, as a
    boolean. -/
def sub {n : Nat} (l l' : List (Fin n)) : Bool :=
  l.all (fun a => decide (a ∈ l'))

/-- The axes where two configurations differ. -/
def diffset {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (I : Inst (Fin n) V (Fin m) W) (x x' : Fin n → V) : List (Fin n) :=
  I.axes.filter (fun a => decide (x a ≠ x' a))

/-- The pair table of an instance: for each ordered pair
    of contract configurations, the pair of their
    difference set and the components they separate. -/
def pairtable {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (I : Inst (Fin n) V (Fin m) W) :
    List (List (Fin n) × List (Fin m)) :=
  I.contract.flatMap (fun x => I.contract.map (fun x' =>
    (diffset I x x',
      I.comps.filter (fun b => decide (I.beh x b ≠ I.beh x' b)))))

/-- The live list read off a pair table: a component is
    live under an axis set when some stored pair whose
    difference set lies inside the axis set separates it.
    This is the difference-set form of liveness that the
    specification's section 7 states. -/
def livetab {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (I : Inst (Fin n) V (Fin m) W)
    (t : List (List (Fin n) × List (Fin m))) (l : List (Fin n)) :
    List (Fin m) :=
  I.comps.filter (fun b => decide
    (∃ p ∈ t, sub p.1 l = true ∧ b ∈ p.2))

theorem diffmem {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (I : Inst (Fin n) V (Fin m) W) (x x' : Fin n → V) (a : Fin n) :
    a ∈ diffset I x x' ↔ a ∈ I.axes ∧ x a ≠ x' a := by
  unfold diffset
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, of_decide_eq_true h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, decide_eq_true h2⟩

theorem suball {n : Nat} (l l' : List (Fin n)) :
    sub l l' = true ↔ ∀ a ∈ l, a ∈ l' := by
  unfold sub
  rw [List.all_eq_true]
  constructor
  · intro h a ha
    exact of_decide_eq_true (h a ha)
  · intro h a ha
    exact decide_eq_true (h a ha)

theorem agreeoffdiff {n m : Nat} {V W : Type} [DecidableEq V]
    [DecidableEq W] (I : Inst (Fin n) V (Fin m) W) (x x' : Fin n → V)
    (l : List (Fin n)) :
    agreeoff I x x' (fun a => decide (a ∈ l)) ↔
      sub (diffset I x x') l = true := by
  rw [suball]
  constructor
  · intro h a ha
    have ha2 := (diffmem I x x' a).mp ha
    by_cases hal : a ∈ l
    · exact hal
    · exfalso
      have hfalse : (fun a => decide (a ∈ l)) a = false :=
        decide_eq_false hal
      exact ha2.2 (h a ha2.1 hfalse)
  · intro h a ha hafalse
    by_cases hne : x a ≠ x' a
    · have hmem : a ∈ diffset I x x' := (diffmem I x x' a).mpr ⟨ha, hne⟩
      have hal : a ∈ l := h a hmem
      have hafalse2 : decide (a ∈ l) = false := hafalse
      rw [decide_eq_true hal] at hafalse2
      simp at hafalse2
    · exact Classical.byContradiction (fun hn => hne hn)

theorem pairmem {n m : Nat} {V W : Type} [DecidableEq V]
    [DecidableEq W] (I : Inst (Fin n) V (Fin m) W)
    (p : List (Fin n) × List (Fin m)) :
    p ∈ pairtable I ↔ ∃ x ∈ I.contract, ∃ x' ∈ I.contract,
      (diffset I x x',
        I.comps.filter (fun b => decide (I.beh x b ≠ I.beh x' b))) = p := by
  unfold pairtable
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hp⟩
    rw [List.mem_map] at hp
    rcases hp with ⟨x', hx', hpx'⟩
    exact ⟨x, hx, x', hx', hpx'⟩
  · rintro ⟨x, hx, x', hx', hp⟩
    exact ⟨x, hx, by rw [List.mem_map]; exact ⟨x', hx', hp⟩⟩

/-- The pair table computes the live list: the
    difference-set form of liveness, proved against the
    definition of live. -/
theorem tablive {n m : Nat} {V W : Type} [DecidableEq V]
    [DecidableEq W] (I : Inst (Fin n) V (Fin m) W) (l : List (Fin n)) :
    livelist I (fun a => decide (a ∈ l)) = livetab I (pairtable I) l := by
  unfold livelist livetab
  apply filtercongr
  intro b hb
  rw [decide_eq_decide]
  constructor
  · rintro ⟨x, hx, x', hx', hagree, hne⟩
    refine ⟨(diffset I x x',
      I.comps.filter (fun b => decide (I.beh x b ≠ I.beh x' b))), ?_, ?_, ?_⟩
    · exact (pairmem I _).mpr ⟨x, hx, x', hx', rfl⟩
    · exact (agreeoffdiff I x x' l).mp hagree
    · rw [List.mem_filter]
      exact ⟨hb, decide_eq_true hne⟩
  · rintro ⟨p, hp, hsub, hb2⟩
    rcases (pairmem I p).mp hp with ⟨x, hx, x', hx', hp2⟩
    subst hp2
    refine ⟨x, hx, x', hx', ?_, ?_⟩
    · exact (agreeoffdiff I x x' l).mpr hsub
    · have hb3 : b ∈ I.comps.filter
          (fun b => decide (I.beh x b ≠ I.beh x' b)) := hb2
      rw [List.mem_filter] at hb3
      exact of_decide_eq_true hb3.2

/-- Insertion sort on a boolean order, for the small lists
    this program renders. -/
def ins {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: ins le x ys

/-- Insertion sort on a boolean order. -/
def isort {α : Type} (le : α → α → Bool) : List α → List α
  | [] => []
  | x :: xs => ins le x (isort le xs)

/-- Lexicographic strict order on lists of naturals. -/
def lexlt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
    if a < b then true else if b < a then false else lexlt as bs

/-- One computed row of the subset table: an axis set with
    the values the definitions give it. -/
structure Row (n m : Nat) where
  set : List (Fin n)
  live : List (Fin m)
  engaged : List (List (Fin m))
  mu : Nat
  lam : Nat

/-- An instance packaged with the names the solver
    contract uses for it. The order list gives the axis
    indices in axis name order; the rank list gives, per
    axis index, its position in that order. -/
structure View (n m : Nat) (V W : Type) [DecidableEq V] [DecidableEq W] where
  inst : Inst (Fin n) V (Fin m) W
  label : String
  axnames : List String
  axorder : List (Fin n)
  axrank : List Nat
  compnames : List String

/-- The axis set named by a list of axes. -/
def setof {n : Nat} (l : List (Fin n)) : Fin n → Bool :=
  fun a => decide (a ∈ l)

/-- The full subset table of an instance, computed from
    the definitions. Each subset's live list is read off
    the instance's pair table by the proved identity
    above; the engaged list and mu are read off that list
    by the other two identities. -/
def rows {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (v : View n m V W) (t : List (List (Fin n) × List (Fin m))) :
    List (Row n m) :=
  (sublists v.inst.axes).map (fun l =>
    let live := livetab v.inst t l
    let engaged := v.inst.edges.filter
      (fun e => decide (2 ≤ e.length ∧ ∀ b ∈ e, b ∈ live))
    { set := l
      live := live
      engaged := engaged
      mu := (engaged.map v.inst.weight).sum
      lam := live.length })

/-- The name list of an axis set, in axis name order. -/
def namesof {n : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (v : View n m V W) (l : List (Fin n)) : List String :=
  (v.axorder.filter (fun a => decide (a ∈ l))).map
    (fun a => (v.axnames[a.1]?).getD "")

/-- The rank key of an axis set: the ranks of its axes in
    axis name order. Comparing rank keys lexicographically
    is comparing the sorted axis name lists. -/
def rankkey {n : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (v : View n m V W) (l : List (Fin n)) : List Nat :=
  (v.axorder.filter (fun a => decide (a ∈ l))).map
    (fun a => (v.axrank[a.1]?).getD 0)

/-- Presentation order of the minimal list: rho
    descending, then the sorted axis name list ascending,
    through rank keys. -/
def before {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (v : View n m V W) (x y : Row n m) : Bool :=
  if x.mu != y.mu then y.mu ≤ x.mu
  else if x.lam != y.lam then y.lam ≤ x.lam
  else !lexlt (rankkey v y.set) (rankkey v x.set)

/-- Space joined names, or a dash for the empty list. -/
def joined (xs : List String) : String :=
  if xs.isEmpty then "-" else String.intercalate " " xs

/-- One engaged list rendered: members in component order,
    each edge closed by its weight, edges separated by
    semicolons, a dash for none. -/
def engagedtext {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (v : View n m V W) (es : List (List (Fin m))) : String :=
  if es.isEmpty then "-"
  else String.intercalate ";"
    (es.map (fun e =>
      let mem := (isort (fun a b : Fin m => a.1 ≤ b.1) e).map
        (fun b => (v.compnames[b.1]?).getD "")
      String.intercalate "," mem ++ ":" ++ toString (v.inst.weight e)))

/-- The canonical expectation lines for one instance. -/
def render {n m : Nat} {V W : Type} [DecidableEq V] [DecidableEq W]
    (v : View n m V W) : String :=
  let table := rows v (pairtable v.inst)
  let fulllive := livelist v.inst (allaxes (A := Fin n))
  let fullengaged := v.inst.edges.filter
    (fun e => decide (2 ≤ e.length ∧ ∀ b ∈ e, b ∈ fulllive))
  let fullmu := (fullengaged.map v.inst.weight).sum
  let fulllam := fulllive.length
  let minimal := table.filter (fun r =>
    r.mu == fullmu && !(table.any (fun r' =>
      r'.mu == fullmu && sub r'.set r.set &&
        r'.set.length < r.set.length)))
  let ordered := isort (before v) minimal
  let best := ordered.head?
  let bestset := best.map (fun r => r.set) |>.getD []
  let lines := []
  let lines := lines ++ ["instance " ++ v.label]
  let lines := lines ++
    ["returned " ++ joined (best.map (fun r => namesof v r.set) |>.getD [])]
  let lines := lines ++
    ["rho " ++ toString (best.map (fun r => r.mu) |>.getD 0) ++ " " ++
      toString (best.map (fun r => r.lam) |>.getD 0)]
  let lines := lines ++ ["mu-full " ++ toString fullmu]
  let lines := lines ++ ["lambda-full " ++ toString fulllam]
  let lines := lines ++
    ["live-full " ++ joined (fulllive.map
      (fun b => (v.compnames[b.1]?).getD ""))]
  let lines := lines ++ ["engaged-full " ++ engagedtext v fullengaged]
  let lines := lines ++
    ["live-returned " ++ joined
      (best.map (fun r => r.live.map
        (fun b => (v.compnames[b.1]?).getD "")) |>.getD [])]
  let lines := lines ++
    ["engaged-returned " ++
      (best.map (fun r => engagedtext v r.engaged) |>.getD "-")]
  let lines := lines ++ ["minimal-count " ++ toString ordered.length]
  let lines := lines ++ ordered.map (fun r =>
    "minimal " ++ joined (namesof v r.set) ++ " | " ++ toString r.mu ++
      " " ++ toString r.lam ++ " | " ++
      joined (r.live.map (fun b => (v.compnames[b.1]?).getD "")) ++
      " | " ++ engagedtext v r.engaged)
  let lines := lines ++ v.inst.axes.map (fun a =>
    let membership :=
      if a ∈ bestset then "in the return"
      else if minimal.any (fun r => decide (a ∈ r.set)) then
        "in some minimal sufficient set only"
      else "in none"
    "axis " ++ ((v.axnames[a.1]?).getD "") ++ " | " ++ membership ++
      " | dead " ++ toString (decide (dead v.inst a)))
  let rowsn := v.inst.contract.length
  let lines := lines ++
    ["counts " ++ toString table.length ++ " " ++ toString rowsn ++
      " " ++ toString (rowsn * (rowsn - 1) / 2)]
  let lines := lines ++ ["end"]
  String.intercalate "\n" lines ++ "\n"

/-- Instance X, as the controls carry it. -/
def viewx : View 3 4 Bool Bool where
  inst := Ctl.instx
  label := "Instance X"
  axnames := ["a", "b", "c"]
  axorder := [0, 1, 2]
  axrank := [0, 1, 2]
  compnames := ["p", "q", "r", "s"]

/-- Instance D, as the controls carry it. -/
def viewd : View 3 2 Bool Bool where
  inst := Ctl.instd
  label := "Instance D"
  axnames := ["a", "b", "c"]
  axorder := [0, 1, 2]
  axrank := [0, 1, 2]
  compnames := ["p", "q"]

/-- Instance E with the empty contract, as the controls
    carry it. -/
def viewe1 : View 3 2 Bool Bool where
  inst := Ctl.inste1
  label := "Instance E (empty contract)"
  axnames := ["a", "b", "c"]
  axorder := [0, 1, 2]
  axrank := [0, 1, 2]
  compnames := ["p", "q"]

/-- Instance E with the singleton contract, as the controls
    carry it. -/
def viewe2 : View 3 2 Bool Bool where
  inst := Ctl.inste2
  label := "Instance E (singleton contract)"
  axnames := ["a", "b", "c"]
  axorder := [0, 1, 2]
  axrank := [0, 1, 2]
  compnames := ["p", "q"]

/-- The arena instance at seed 11, in the coded encoding
    of Arena.lean. Axis name order: count, material,
    motion, placement, wentropy, wspecials, wsteps. -/
def viewa11 : View 7 5 Nat Nat where
  inst := Arena.inst0
  label := "arena-seed-11"
  axnames := ["count", "placement", "material", "wsteps", "wspecials",
    "wentropy", "motion"]
  axorder := [0, 2, 6, 1, 5, 4, 3]
  axrank := [0, 3, 1, 6, 5, 4, 2]
  compnames := ["layout", "successors", "plan", "selection", "execution"]

/-- The arena instance at seed 23, same names. -/
def viewa23 : View 7 5 Nat Nat where
  inst := Arena.inst1
  label := "arena-seed-23"
  axnames := ["count", "placement", "material", "wsteps", "wspecials",
    "wentropy", "motion"]
  axorder := [0, 2, 6, 1, 5, 4, 3]
  axrank := [0, 3, 1, 6, 5, 4, 2]
  compnames := ["layout", "successors", "plan", "selection", "execution"]

end Expect

/-- The expectations entry point: the canonical lines for
    the six instances of the gate, in gate order. -/
def main : IO Unit := do
  IO.print (Expect.render Expect.viewx)
  IO.print (Expect.render Expect.viewd)
  IO.print (Expect.render Expect.viewe1)
  IO.print (Expect.render Expect.viewe2)
  IO.print (Expect.render Expect.viewa11)
  IO.print (Expect.render Expect.viewa23)
