import FiniteCheck
import Init.Data.List.Lex
import ExecutableWitness
import IncrementalCounts

/- Executable complete observations of a supplied liveness materialization.
   Correctness is conditional on exact liveness; a concrete witness engine
   discharges that premise without repeating row-pair search in this renderer. -/

namespace HmaCertified

open Hma HmaCheck

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]

abbrev Row (A B : Type) := List A × Snapshot B

def snapshotFromLive (I : Inst A V B W) (live : List B) : Snapshot B :=
  let active := activeEdge I.edges live
  { live := live
    edges := I.edges.filter active
    measure := ((I.edges.map (fun e => if active e then I.weight e else 0)).sum,
      live.length) }

def tableFromLive (I : Inst A V B W) (liveFor : (A → Bool) → List B) : List (Row A B) :=
  (sublists I.axes).map (fun l => (l, snapshotFromLive I (liveFor (axisSet l))))

instance tableMinimalDec (I : Inst A V B W) (rows : List (Row A B))
    (fullmu : Nat) (l : List A) (value : Snapshot B) :
    Decidable (tableMinimal I rows fullmu l value) := by
  unfold tableMinimal proper subset
  infer_instance

def minimalFlag (I : Inst A V B W) (rows : List (Row A B))
    (fullmu : Nat) (r : Row A B) : Bool :=
  decide (tableMinimal I rows fullmu r.1 r.2)

def minimalRows (I : Inst A V B W) (rows : List (Row A B))
    (fullmu : Nat) : List (Row A B) :=
  rows.filter (minimalFlag I rows fullmu)

def measureLE (x y : Nat × Nat) : Bool :=
  decide (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2))

def beatsAll (minima : List (Row A B)) (r : Row A B) : Bool :=
  minima.all (fun other => measureLE other.2.measure r.2.measure)

def highestRows (minima : List (Row A B)) : List (Row A B) :=
  minima.filter (beatsAll minima)

def chooseAxes (prefer : List A → List A → Bool) : List (List A) → Option (List A)
  | [] => none
  | x :: xs => match chooseAxes prefer xs with
    | none => some x
    | some y => some (if prefer x y then x else y)

inductive Membership where
  | chosen | alternative | none
  deriving DecidableEq, Repr

structure Classified (A B : Type) where
  axes : List A
  value : Snapshot B
  sufficient : Bool
  minimal : Bool
  highest : Bool
  deriving DecidableEq, Repr

structure Disposition (A : Type) where
  axis : A
  membership : Membership
  emergentDead : Bool
  deriving DecidableEq, Repr

structure Rendered (A B : Type) where
  full : Snapshot B
  subsets : List (Classified A B)
  minimal : List (List A)
  highest : List (List A)
  chosen : Option (List A)
  dispositions : List (Disposition A)
  deriving DecidableEq, Repr

def classify (I : Inst A V B W) (rows : List (Row A B)) (fullmu : Nat)
    (minima : List (Row A B)) (r : Row A B) : Classified A B :=
  { axes := r.1
    value := r.2
    sufficient := decide (r.2.measure.1 = fullmu)
    minimal := minimalFlag I rows fullmu r
    highest := minimalFlag I rows fullmu r && beatsAll minima r }

def chosenContains (chosen : Option (List A)) (a : A) : Bool :=
  match chosen with
  | none => false
  | some l => decide (a ∈ l)

def minimalContains (minima : List (List A)) (a : A) : Bool :=
  minima.any (fun l => decide (a ∈ l))

def membership (chosen : Option (List A)) (minima : List (List A)) (a : A) : Membership :=
  if chosenContains chosen a then .chosen
  else if minimalContains minima a then .alternative else .none

def deadFlag (liveFor : (A → Bool) → List B) (a : A) : Bool :=
  decide (liveFor (rem allaxes a) = liveFor allaxes)

def render (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) : Rendered A B :=
  let full := snapshotFromLive I (liveFor allaxes)
  let rows := tableFromLive I liveFor
  let minima := minimalRows I rows full.measure.1
  let highest := (highestRows minima).map Prod.fst
  let keys := minima.map Prod.fst
  let chosen := chooseAxes prefer highest
  { full := full
    subsets := rows.map (classify I rows full.measure.1 minima)
    minimal := keys
    highest := highest
    chosen := chosen
    dispositions := I.axes.map (fun a =>
      { axis := a, membership := membership chosen keys a, emergentDead := deadFlag liveFor a }) }

abbrev Exact (I : Inst A V B W) (liveFor : (A → Bool) → List B) : Prop :=
  ∀ S, liveFor S = livelist I S

theorem snapshotFromLive_exact (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (S : A → Bool) :
    snapshotFromLive I (liveFor S) = snapshot I S := by
  rw [h S]
  rfl

theorem tableFromLive_exact (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) : tableFromLive I liveFor = table I := by
  unfold tableFromLive table
  apply List.map_congr_left
  intro l _
  rw [snapshotFromLive_exact I liveFor h]

theorem minimalFlag_iff (I : Inst A V B W) (rows : List (Row A B))
    (fullmu : Nat) (r : Row A B) :
    minimalFlag I rows fullmu r = true ↔ tableMinimal I rows fullmu r.1 r.2 := by
  simp only [minimalFlag, decide_eq_true_eq]

theorem mem_minimalRows (I : Inst A V B W) (rows : List (Row A B))
    (fullmu : Nat) (r : Row A B) :
    r ∈ minimalRows I rows fullmu ↔ r ∈ rows ∧ tableMinimal I rows fullmu r.1 r.2 := by
  simp only [minimalRows, List.mem_filter, minimalFlag_iff]

theorem highestFlag_iff (I : Inst A V B W) (rows : List (Row A B))
    (fullmu : Nat) (r : Row A B) :
    (minimalFlag I rows fullmu r && beatsAll (minimalRows I rows fullmu) r) = true ↔
      tableHighest I rows fullmu r.1 r.2 := by
  simp only [Bool.and_eq_true, minimalFlag_iff, beatsAll, List.all_eq_true,
    measureLE, decide_eq_true_eq, mem_minimalRows]
  constructor
  · rintro ⟨hm, hh⟩
    exact ⟨hm, fun other hr hmin => hh other ⟨hr, hmin⟩⟩
  · rintro ⟨hm, hh⟩
    exact ⟨hm, fun other hmem => hh other hmem.1 hmem.2⟩

theorem mem_highestRows (I : Inst A V B W) (rows : List (Row A B))
    (fullmu : Nat) (r : Row A B) :
    r ∈ highestRows (minimalRows I rows fullmu) ↔
      r ∈ rows ∧ tableHighest I rows fullmu r.1 r.2 := by
  simp only [highestRows, List.mem_filter, mem_minimalRows]
  constructor
  · rintro ⟨⟨hr, hm⟩, hh⟩
    exact ⟨hr, (highestFlag_iff I rows fullmu r).mp
      (Bool.and_eq_true_iff.mpr ⟨(minimalFlag_iff I rows fullmu r).mpr hm, hh⟩)⟩
  · rintro ⟨hr, hh⟩
    obtain ⟨hm, hb⟩ := Bool.and_eq_true_iff.mp ((highestFlag_iff I rows fullmu r).mpr hh)
    exact ⟨⟨hr, (minimalFlag_iff I rows fullmu r).mp hm⟩, hb⟩

omit [DecidableEq A] in
theorem chooseAxes_none_iff (prefer : List A → List A → Bool) (xs : List (List A)) :
    chooseAxes prefer xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [chooseAxes]
  | cons x xs =>
    cases hc : chooseAxes prefer xs <;> simp [chooseAxes, hc]

omit [DecidableEq A] in
theorem chooseAxes_mem (prefer : List A → List A → Bool) (xs : List (List A))
    (l : List A) (h : chooseAxes prefer xs = some l) : l ∈ xs := by
  induction xs with
  | nil => simp [chooseAxes] at h
  | cons x xs ih =>
    cases hc : chooseAxes prefer xs with
    | none =>
      have heq : x = l := by simpa [chooseAxes, hc] using h
      subst l
      exact List.mem_cons_self
    | some y =>
      by_cases hp : prefer x y = true
      · have heq : x = l := by simpa [chooseAxes, hc, hp] using h
        subst l
        exact List.mem_cons_self
      · have heq : y = l := by simpa [chooseAxes, hc, hp] using h
        subst l
        exact List.mem_cons_of_mem _ (ih hc)

theorem render_full (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) :
    (render I liveFor prefer).full = snapshot I allaxes :=
  snapshotFromLive_exact I liveFor h allaxes

theorem minimalRows_exact (I : Inst A V B W) (l : List A) :
    l ∈ (minimalRows I (table I) (mu I allaxes)).map Prod.fst ↔
      l ∈ sublists I.axes ∧ Hma.minimal I (axisSet l) := by
  constructor
  · intro h
    obtain ⟨r, hr, hrkey⟩ := List.mem_map.mp h
    obtain ⟨hin, hmin⟩ := (mem_minimalRows I (table I) (mu I allaxes) r).mp hr
    obtain ⟨key, hkey, hr⟩ := List.mem_map.mp hin
    subst r
    simp only at hrkey
    subst l
    exact ⟨hkey, (tableMinimalIff I key).mp hmin⟩
  · rintro ⟨hin, hm⟩
    apply List.mem_map.mpr
    refine ⟨(l, snapshot I (axisSet l)), ?_, rfl⟩
    apply (mem_minimalRows I (table I) (mu I allaxes) _).mpr
    exact ⟨List.mem_map_of_mem hin, (tableMinimalIff I l).mpr hm⟩

theorem highestRows_exact (I : Inst A V B W) (l : List A) :
    l ∈ (highestRows (minimalRows I (table I) (mu I allaxes))).map Prod.fst ↔
      l ∈ sublists I.axes ∧ Hma.highest I (axisSet l) := by
  constructor
  · intro h
    obtain ⟨r, hr, hrkey⟩ := List.mem_map.mp h
    obtain ⟨hin, hhigh⟩ := (mem_highestRows I (table I) (mu I allaxes) r).mp hr
    obtain ⟨key, hkey, hr⟩ := List.mem_map.mp hin
    subst r
    simp only at hrkey
    subst l
    exact ⟨hkey, (tableHighestIff I key).mp hhigh⟩
  · rintro ⟨hin, hh⟩
    apply List.mem_map.mpr
    refine ⟨(l, snapshot I (axisSet l)), ?_, rfl⟩
    apply (mem_highestRows I (table I) (mu I allaxes) _).mpr
    exact ⟨List.mem_map_of_mem hin, (tableHighestIff I l).mpr hh⟩

theorem render_minimal_iff (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (l : List A) :
    l ∈ (render I liveFor prefer).minimal ↔
      l ∈ sublists I.axes ∧ Hma.minimal I (axisSet l) := by
  change l ∈ (minimalRows I (tableFromLive I liveFor)
    (snapshotFromLive I (liveFor allaxes)).measure.1).map Prod.fst ↔ _
  rw [tableFromLive_exact I liveFor h, snapshotFromLive_exact I liveFor h,
    snapshotMeasure]
  exact minimalRows_exact I l

theorem render_highest_iff (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (l : List A) :
    l ∈ (render I liveFor prefer).highest ↔
      l ∈ sublists I.axes ∧ Hma.highest I (axisSet l) := by
  change l ∈ (highestRows (minimalRows I (tableFromLive I liveFor)
    (snapshotFromLive I (liveFor allaxes)).measure.1)).map Prod.fst ↔ _
  rw [tableFromLive_exact I liveFor h, snapshotFromLive_exact I liveFor h,
    snapshotMeasure]
  exact highestRows_exact I l

theorem render_minimal_complete (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (S : A → Bool) :
    (∃ l ∈ (render I liveFor prefer).minimal, axisSet l = S) ↔ Hma.minimal I S := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ((render_minimal_iff I liveFor h prefer l).mp hl).2
  · intro hm
    obtain ⟨l, hl, heq⟩ := subsetrep I S
    change S = axisSet l at heq
    subst S
    exact ⟨l, (render_minimal_iff I liveFor h prefer l).mpr ⟨hl, hm⟩, rfl⟩

theorem render_highest_complete (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (S : A → Bool) :
    (∃ l ∈ (render I liveFor prefer).highest, axisSet l = S) ↔ Hma.highest I S := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ((render_highest_iff I liveFor h prefer l).mp hl).2
  · intro hh
    obtain ⟨l, hl, heq⟩ := subsetrep I S
    change S = axisSet l at heq
    subst S
    exact ⟨l, (render_highest_iff I liveFor h prefer l).mpr ⟨hl, hh⟩, rfl⟩

theorem render_chosen_mem (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) (l : List A)
    (hc : (render I liveFor prefer).chosen = some l) :
    l ∈ (render I liveFor prefer).highest := chooseAxes_mem prefer _ l hc

theorem render_chosen_highest (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (l : List A)
    (hc : (render I liveFor prefer).chosen = some l) : Hma.highest I (axisSet l) :=
  ((render_highest_iff I liveFor h prefer l).mp
    (render_chosen_mem I liveFor prefer l hc)).2

theorem render_chosen_exists (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) :
    ∃ l, (render I liveFor prefer).chosen = some l ∧ Hma.highest I (axisSet l) := by
  obtain ⟨S, hs⟩ := highestexists I
  obtain ⟨l, hl, _⟩ := (render_highest_complete I liveFor h prefer S).mpr hs
  cases hc : (render I liveFor prefer).chosen with
  | none =>
    have he : (render I liveFor prefer).highest = [] :=
      (chooseAxes_none_iff prefer _).mp hc
    rw [he] at hl
    exact False.elim (List.not_mem_nil hl)
  | some selected => exact ⟨selected, rfl, render_chosen_highest I liveFor h prefer selected hc⟩

theorem render_subsets_canonical (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) :
    (render I liveFor prefer).subsets =
      (table I).map (classify I (table I) (mu I allaxes)
        (minimalRows I (table I) (mu I allaxes))) := by
  change (tableFromLive I liveFor).map (classify I (tableFromLive I liveFor)
    (snapshotFromLive I (liveFor allaxes)).measure.1
    (minimalRows I (tableFromLive I liveFor) (snapshotFromLive I (liveFor allaxes)).measure.1)) = _
  rw [tableFromLive_exact I liveFor h, snapshotFromLive_exact I liveFor h, snapshotMeasure]
  rfl

theorem render_subset_exact (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (r : Classified A B)
    (hr : r ∈ (render I liveFor prefer).subsets) :
    r.axes ∈ sublists I.axes ∧ r.value = snapshot I (axisSet r.axes) ∧
    (r.sufficient = true ↔ Hma.sufficient I (axisSet r.axes)) ∧
    (r.minimal = true ↔ Hma.minimal I (axisSet r.axes)) ∧
    (r.highest = true ↔ Hma.highest I (axisSet r.axes)) := by
  rw [render_subsets_canonical I liveFor h prefer] at hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hp
  refine ⟨hl, rfl, ?_, ?_, ?_⟩
  · change decide ((snapshot I (axisSet l)).measure.1 = mu I allaxes) = true ↔ _
    simp only [decide_eq_true_eq, snapshotMeasure, rho, sufficient, classify]
  · exact (minimalFlag_iff I (table I) (mu I allaxes) _).trans (tableMinimalIff I l)
  · exact (highestFlag_iff I (table I) (mu I allaxes) _).trans (tableHighestIff I l)

theorem render_subsets_cover (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (S : A → Bool) :
    ∃ r ∈ (render I liveFor prefer).subsets, axisSet r.axes = S := by
  obtain ⟨l, hl, heq⟩ := subsetrep I S
  rw [render_subsets_canonical I liveFor h prefer]
  refine ⟨classify I (table I) (mu I allaxes) (minimalRows I (table I) (mu I allaxes))
      (l, snapshot I (axisSet l)), List.mem_map_of_mem (List.mem_map_of_mem hl), ?_⟩
  exact heq.symm

theorem chosenContains_iff (selected : Option (List A)) (a : A) :
    chosenContains selected a = true ↔ ∃ l, selected = some l ∧ a ∈ l := by
  cases selected <;> simp [chosenContains]

theorem minimalContains_iff (minima : List (List A)) (a : A) :
    minimalContains minima a = true ↔ ∃ l ∈ minima, a ∈ l := by
  simp only [minimalContains, List.any_eq_true, decide_eq_true_eq]

theorem membership_chosen_iff (selected : Option (List A)) (minima : List (List A)) (a : A) :
    membership selected minima a = .chosen ↔ ∃ l, selected = some l ∧ a ∈ l := by
  rw [← chosenContains_iff]
  unfold membership
  cases h : chosenContains selected a <;> cases hm : minimalContains minima a <;> simp

theorem membership_alternative_iff (selected : Option (List A)) (minima : List (List A)) (a : A) :
    membership selected minima a = .alternative ↔
      (¬ ∃ l, selected = some l ∧ a ∈ l) ∧ (∃ l ∈ minima, a ∈ l) := by
  rw [← chosenContains_iff, ← minimalContains_iff]
  unfold membership
  cases h : chosenContains selected a <;> cases hm : minimalContains minima a <;> simp

theorem membership_none_iff (selected : Option (List A)) (minima : List (List A)) (a : A) :
    membership selected minima a = .none ↔
      (¬ ∃ l, selected = some l ∧ a ∈ l) ∧ (¬ ∃ l ∈ minima, a ∈ l) := by
  rw [← chosenContains_iff, ← minimalContains_iff]
  unfold membership
  cases h : chosenContains selected a <;> cases hm : minimalContains minima a <;> simp

theorem deadFlag_exact (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (a : A) : deadFlag liveFor a = true ↔ Hma.dead I a := by
  simp only [deadFlag, h, decide_eq_true_eq, dead]

theorem render_dispositions_cover (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) (a : A) :
    ∃ d ∈ (render I liveFor prefer).dispositions, d.axis = a := by
  refine ⟨⟨a, membership (render I liveFor prefer).chosen (render I liveFor prefer).minimal a,
      deadFlag liveFor a⟩, ?_, rfl⟩
  exact List.mem_map_of_mem (I.axescomplete a)

theorem render_disposition_exact (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (d : Disposition A)
    (hd : d ∈ (render I liveFor prefer).dispositions) :
    d.membership = membership (render I liveFor prefer).chosen (render I liveFor prefer).minimal d.axis ∧
    (d.emergentDead = true ↔ Hma.dead I d.axis) := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hd
  exact ⟨rfl, deadFlag_exact I liveFor h a⟩

structure RenderCorrect (I : Inst A V B W) (result : Rendered A B) : Prop where
  full : result.full = snapshot I allaxes
  subsets : ∀ r ∈ result.subsets,
    r.axes ∈ sublists I.axes ∧ r.value = snapshot I (axisSet r.axes) ∧
    (r.sufficient = true ↔ Hma.sufficient I (axisSet r.axes)) ∧
    (r.minimal = true ↔ Hma.minimal I (axisSet r.axes)) ∧
    (r.highest = true ↔ Hma.highest I (axisSet r.axes))
  coverage : ∀ S, ∃ r ∈ result.subsets, axisSet r.axes = S
  minimal : ∀ l, l ∈ result.minimal ↔ l ∈ sublists I.axes ∧ Hma.minimal I (axisSet l)
  highest : ∀ l, l ∈ result.highest ↔ l ∈ sublists I.axes ∧ Hma.highest I (axisSet l)
  chosen : ∃ l, result.chosen = some l ∧ Hma.highest I (axisSet l)
  dispositions : ∀ d ∈ result.dispositions,
    d.membership = membership result.chosen result.minimal d.axis ∧
    (d.emergentDead = true ↔ Hma.dead I d.axis)
  axisCoverage : ∀ a, ∃ d ∈ result.dispositions, d.axis = a

theorem render_correct (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) :
    RenderCorrect I (render I liveFor prefer) where
  full := render_full I liveFor h prefer
  subsets := render_subset_exact I liveFor h prefer
  coverage := render_subsets_cover I liveFor h prefer
  minimal := render_minimal_iff I liveFor h prefer
  highest := render_highest_iff I liveFor h prefer
  chosen := render_chosen_exists I liveFor h prefer
  dispositions := render_disposition_exact I liveFor h prefer
  axisCoverage := render_dispositions_cover I liveFor prefer

omit [DecidableEq A] in
theorem chooseAxes_minimum (R : List A → List A → Prop) [DecidableRel R]
    (irrefl : ∀ x, ¬ R x x)
    (transitive : ∀ x y z, R x y → R y z → R x z)
    (xs : List (List A)) (selected : List A)
    (hc : chooseAxes (fun x y => decide (R x y)) xs = some selected) :
    ∀ other ∈ xs, ¬ R other selected := by
  induction xs generalizing selected with
  | nil => simp [chooseAxes] at hc
  | cons x xs ih =>
    cases ht : chooseAxes (fun x y => decide (R x y)) xs with
    | none =>
      have hempty := (chooseAxes_none_iff (fun x y => decide (R x y)) xs).mp ht
      subst xs
      have hselected : x = selected := by simpa [chooseAxes] using hc
      subst selected
      intro other ho
      have heq : other = x := by simpa using ho
      subst other
      exact irrefl x
    | some y =>
      have hy := ih y ht
      by_cases hp : R x y
      · have hselected : x = selected := by simpa [chooseAxes, ht, hp] using hc
        subst selected
        intro other ho hbad
        rcases List.mem_cons.mp ho with rfl | ho
        · exact irrefl _ hbad
        · exact hy other ho (transitive other x y hbad hp)
      · have hselected : y = selected := by simpa [chooseAxes, ht, hp] using hc
        subst selected
        intro other ho
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hp
        · exact hy other ho

omit [DecidableEq A] in
theorem lex_irrefl (R : A → A → Prop) (irrefl : ∀ a, ¬ R a a)
    (xs : List A) : ¬ List.Lex R xs xs := by
  induction xs with
  | nil => intro h; cases h
  | cons x xs ih =>
    intro h
    cases h with
    | rel hbad => exact irrefl x hbad
    | cons htail => exact ih htail

def finLexPrefer {n : Nat} (x y : List (Fin n)) : Bool :=
  decide (List.Lex (fun a b : Fin n => a.val < b.val) x y)

theorem render_chosen_lex_minimum {n : Nat} (I : Inst (Fin n) V B W)
    (liveFor : (Fin n → Bool) → List B) (selected : List (Fin n))
    (hc : (render I liveFor finLexPrefer).chosen = some selected) :
    ∀ other ∈ (render I liveFor finLexPrefer).highest,
      ¬ List.Lex (fun a b : Fin n => a.val < b.val) other selected := by
  apply chooseAxes_minimum (List.Lex (fun a b : Fin n => a.val < b.val))
    (lex_irrefl _ (fun a => Nat.lt_irrefl a.val))
    (fun _ _ _ hxy hyz => List.lex_trans (fun h1 h2 => Nat.lt_trans h1 h2) hxy hyz)
    _ selected hc

def accepts (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) (claimed : Rendered A B) : Bool :=
  decide (render I liveFor prefer = claimed)

theorem accepts_sound (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (h : Exact I liveFor) (prefer : List A → List A → Bool) (claimed : Rendered A B)
    (accepted : accepts I liveFor prefer claimed = true) : RenderCorrect I claimed := by
  have heq : render I liveFor prefer = claimed := of_decide_eq_true accepted
  rw [← heq]
  exact render_correct I liveFor h prefer

theorem tableFromLive_keys (I : Inst A V B W) (liveFor : (A → Bool) → List B) :
    (tableFromLive I liveFor).map Prod.fst = sublists I.axes := by
  simp only [tableFromLive, List.map_map, Function.comp_def]
  exact List.map_id _

theorem render_subset_axis_list (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) :
    (render I liveFor prefer).subsets.map Classified.axes = sublists I.axes := by
  change ((tableFromLive I liveFor).map _).map Classified.axes = _
  rw [List.map_map]
  exact tableFromLive_keys I liveFor

theorem render_subset_count (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) :
    (render I liveFor prefer).subsets.length = 2 ^ I.axes.length := by
  have h := congrArg List.length (render_subset_axis_list I liveFor prefer)
  simpa only [List.length_map, HmaIncremental.sublists_length] using h

theorem render_subset_unique (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) :
    ((render I liveFor prefer).subsets.map Classified.axes).Nodup := by
  rw [render_subset_axis_list]
  exact HmaIncremental.sublists_nodup I.axes I.axesnodup

theorem render_minimal_unique (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) : (render I liveFor prefer).minimal.Nodup := by
  have hn : ((tableFromLive I liveFor).map Prod.fst).Nodup := by
    rw [tableFromLive_keys]
    exact HmaIncremental.sublists_nodup I.axes I.axesnodup
  exact List.Sublist.nodup (List.Sublist.map Prod.fst List.filter_sublist) hn

theorem render_highest_unique (I : Inst A V B W) (liveFor : (A → Bool) → List B)
    (prefer : List A → List A → Bool) : (render I liveFor prefer).highest.Nodup :=
  List.Sublist.nodup (List.Sublist.map Prod.fst List.filter_sublist)
    (render_minimal_unique I liveFor prefer)

section Materialized

variable [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B]

def renderState (I : Inst A V B W) (state : HmaExecutable.State A V B)
    (prefer : List A → List A → Bool) : Rendered A B :=
  render (HmaIncremental.withContract I state.rows) (HmaExecutable.liveList I state) prefer

omit [LawfulBEq A] in
theorem renderState_correct (I : Inst A V B W) (state : HmaExecutable.State A V B)
    (h : HmaExecutable.Valid I state) (prefer : List A → List A → Bool) :
    RenderCorrect (HmaIncremental.withContract I state.rows) (renderState I state prefer) :=
  render_correct _ _ (HmaExecutable.liveList_exact I state h) prefer

def acceptsState (I : Inst A V B W) (state : HmaExecutable.State A V B)
    (prefer : List A → List A → Bool) (claimed : Rendered A B) : Bool :=
  decide (renderState I state prefer = claimed)

omit [LawfulBEq A] in
theorem acceptsState_sound (I : Inst A V B W) (state : HmaExecutable.State A V B)
    (h : HmaExecutable.Valid I state) (prefer : List A → List A → Bool) (claimed : Rendered A B)
    (accepted : acceptsState I state prefer claimed = true) :
    RenderCorrect (HmaIncremental.withContract I state.rows) claimed := by
  have heq : renderState I state prefer = claimed := of_decide_eq_true accepted
  rw [← heq]
  exact renderState_correct I state h prefer

end Materialized

end HmaCertified
