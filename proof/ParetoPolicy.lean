import OptimalController
import ParametricPareto

namespace ParetoPolicy

open OptimalController

def assignments {X : Type} : (n : Nat) → List X → List (Fin n → X)
  | 0, _ => [fun i => Fin.elim0 i]
  | n + 1, values => values.flatMap (fun x =>
      (assignments n values).map (fun rest => Fin.cases x rest))

theorem assignments_complete {X : Type} (n : Nat) (values : List X) (f : Fin n → X)
    (h : ∀ i, f i ∈ values) : f ∈ assignments n values := by
  induction n with
  | zero =>
    have he : f = (fun i : Fin 0 => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    simp [assignments, he]
  | succ n ih =>
    have ht := ih (fun i => f i.succ) (fun i => h i.succ)
    simp only [assignments, List.mem_flatMap, List.mem_map]
    refine ⟨f 0, h 0, fun i => f i.succ, ht, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem flatMap_constant_length {X Y : Type} (xs : List X) (f : X → List Y) (k : Nat)
    (h : ∀ x, x ∈ xs → (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      h x List.mem_cons_self, ih (fun a ha => h a (List.mem_cons_of_mem x ha))]
    rw [Nat.add_mul]
    omega

theorem assignments_count {X : Type} (n : Nat) (values : List X) :
    (assignments n values).length = values.length ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold assignments
    rw [flatMap_constant_length _ _ (values.length ^ n) (by intro x hx; simp [ih])]
    simp [Nat.pow_succ, Nat.mul_comm]

def policies (actions outcomes : Nat) : (horizon : Nat) → List (Policy (Fin actions) (Fin outcomes) horizon)
  | 0 => [.stop]
  | n + 1 => (List.finRange actions).flatMap (fun a =>
      (assignments outcomes (policies actions outcomes n)).map (Policy.step a))

theorem policies_complete (actions outcomes horizon : Nat)
    (policy : Policy (Fin actions) (Fin outcomes) horizon) :
    policy ∈ policies actions outcomes horizon := by
  induction horizon with
  | zero => cases policy; simp [policies]
  | succ n ih =>
    cases policy with
    | step a after =>
      simp only [policies, List.mem_flatMap, List.mem_map]
      exact ⟨a, by simp [List.finRange],
        after, assignments_complete outcomes _ after (fun o => ih (after o)), rfl⟩

theorem policies_count_step (actions outcomes horizon : Nat) :
    (policies actions outcomes (horizon + 1)).length =
      actions * (policies actions outcomes horizon).length ^ outcomes := by
  change ((List.finRange actions).flatMap (fun a =>
    (assignments outcomes (policies actions outcomes horizon)).map (Policy.step a))).length = _
  rw [flatMap_constant_length _ _ ((policies actions outcomes horizon).length ^ outcomes)
    (by intro a ha; simp [assignments_count])]
  simp

variable {S : Type} {actions outcomes : Nat}

def admissible (M : Model Nat S (Fin actions) (Fin outcomes)) :
    {n : Nat} → S → Policy (Fin actions) (Fin outcomes) n → Bool
  | 0, _, .stop => true
  | _ + 1, s, .step a after =>
    (M.actions s).contains a &&
      (M.outcomes s a).all (fun o => admissible M (M.next s a o) (after o))

theorem admissible_exact (M : Model Nat S (Fin actions) (Fin outcomes)) (n : Nat) (s : S)
    (policy : Policy (Fin actions) (Fin outcomes) n) :
    admissible M s policy = true ↔ Admissible M s policy := by
  induction n generalizing s with
  | zero => cases policy; simp [admissible, Admissible]
  | succ n ih =>
    cases policy with
    | step a after => simp [admissible, Admissible, List.all_eq_true, ih]

def qualified (M : Model Nat S (Fin actions) (Fin outcomes)) (n : Nat) (s : S) :
    List (Policy (Fin actions) (Fin outcomes) n) :=
  (policies actions outcomes n).filter (admissible M s)

theorem qualified_exact (M : Model Nat S (Fin actions) (Fin outcomes)) (n : Nat) (s : S)
    (policy : Policy (Fin actions) (Fin outcomes) n) :
    policy ∈ qualified M n s ↔ Admissible M s policy := by
  simp only [qualified, List.mem_filter, admissible_exact]
  exact and_iff_right (policies_complete actions outcomes n policy)

def point (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions id : Nat)
    {n : Nat} (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) : ParametricPareto.Point :=
  ⟨id, List.ofFn (fun i : Fin dimensions => (worst M i.val s policy : Int))⟩

def catalogue (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat) (s : S) :
    List ParametricPareto.Point :=
  ((List.finRange (policies actions outcomes n).length).filter
    (fun i => admissible M s ((policies actions outcomes n).get i))).map
    (fun i => point M dimensions i.val s ((policies actions outcomes n).get i))

def state (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat) (s : S) :
    ParametricPareto.State := ParametricPareto.build (List.range dimensions) (catalogue M dimensions n s)

theorem state_valid (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat) (s : S) :
    ParametricPareto.Valid (state M dimensions n s) := ParametricPareto.build_valid _ _

theorem point_cost (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions id : Nat)
    {n : Nat} (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) (i : Nat)
    (hi : i < dimensions) :
    ParametricPareto.cost (point M dimensions id s policy) i = (worst M i s policy : Int) := by
  simp [ParametricPareto.cost, point, hi]

theorem catalogue_sound (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat)
    (s : S) (p : ParametricPareto.Point) (hp : p ∈ catalogue M dimensions n s) :
    ∃ policy : Policy (Fin actions) (Fin outcomes) n,
      Admissible M s policy ∧ p = point M dimensions p.id s policy := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hp
  refine ⟨(policies actions outcomes n).get i, ?_, ?_⟩
  · exact (admissible_exact M n s _).mp (List.mem_filter.mp hi).2
  · subst p
    rfl

theorem catalogue_complete (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat)
    (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) (hp : Admissible M s policy) :
    ∃ id, point M dimensions id s policy ∈ catalogue M dimensions n s := by
  have hq := policies_complete actions outcomes n policy
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
  refine ⟨i.val, List.mem_map.mpr ⟨i, ?_, ?_⟩⟩
  · apply List.mem_filter.mpr
    refine ⟨by simp [List.finRange], ?_⟩
    rw [hi]
    exact (admissible_exact M n s policy).mpr hp
  rw [hi]

def lookup (actions outcomes n id : Nat) :
    Option (Policy (Fin actions) (Fin outcomes) n) := (policies actions outcomes n)[id]?

theorem catalogue_lookup (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat)
    (s : S) (p : ParametricPareto.Point) (hp : p ∈ catalogue M dimensions n s) :
    ∃ policy : Policy (Fin actions) (Fin outcomes) n,
      lookup actions outcomes n p.id = some policy ∧ Admissible M s policy ∧
        p = point M dimensions p.id s policy := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hp
  refine ⟨(policies actions outcomes n).get i, ?_, ?_, ?_⟩
  · subst p
    simp [lookup, point, List.get_eq_getElem]
  · exact (admissible_exact M n s _).mp (List.mem_filter.mp hi).2
  · subst p; rfl

theorem qualified_nonempty [Inhabited (Fin actions)]
    (M : Model Nat S (Fin actions) (Fin outcomes)) (n : Nat) (s : S) :
    qualified M n s ≠ [] := by
  have h := (qualified_exact M n s (optimize M 0 n s)).mpr (optimize_admissible M 0 n s)
  intro he
  rw [he] at h
  simp at h

theorem catalogue_nonempty [Inhabited (Fin actions)]
    (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat) (s : S) :
    catalogue M dimensions n s ≠ [] := by
  obtain ⟨id, hid⟩ := catalogue_complete M dimensions n s (optimize M 0 n s)
    (optimize_admissible M 0 n s)
  intro he
  rw [he] at hid
  simp at hid

theorem policy_choice_exists [Inhabited (Fin actions)]
    (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat)
    (s : S) (weights : Nat → Nat) :
    ∃ p, ParametricPareto.select (state M dimensions n s) weights = some p :=
  ParametricPareto.nonempty_selects _ weights (catalogue_nonempty M dimensions n s)

theorem policy_frontier_exact (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (p : ParametricPareto.Point) :
    p ∈ ParametricPareto.frontier (state M dimensions n s) ↔
      p ∈ catalogue M dimensions n s ∧
      ∀ policy : Policy (Fin actions) (Fin outcomes) n, Admissible M s policy →
        ParametricPareto.dominates (List.range dimensions) (point M dimensions 0 s policy) p = false := by
  rw [ParametricPareto.frontier_exact _ (state_valid M dimensions n s)]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro policy valid
    obtain ⟨id, hid⟩ := catalogue_complete M dimensions n s policy valid
    have hh := h (point M dimensions id s policy) hid
    exact hh
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro q hq
    obtain ⟨policy, valid, he⟩ := catalogue_sound M dimensions n s q hq
    rw [he]
    exact h policy valid

theorem selected_policy_optimal (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (weights : Nat → Nat) (p : ParametricPareto.Point)
    (selected : ParametricPareto.select (state M dimensions n s) weights = some p) :
    (∃ policy : Policy (Fin actions) (Fin outcomes) n,
      Admissible M s policy ∧ p = point M dimensions p.id s policy) ∧
    (∀ policy : Policy (Fin actions) (Fin outcomes) n, Admissible M s policy →
      ParametricPareto.weighted (List.range dimensions) weights p ≤
        ParametricPareto.weighted (List.range dimensions) weights (point M dimensions 0 s policy)) ∧
    (∀ policy : Policy (Fin actions) (Fin outcomes) n, Admissible M s policy →
      ParametricPareto.dominates (List.range dimensions) (point M dimensions 0 s policy) p = false) := by
  have hopt := ParametricPareto.selected_weighted_optimal _ weights p selected
  refine ⟨catalogue_sound M dimensions n s p hopt.1, ?_, ?_⟩
  · intro policy valid
    obtain ⟨id, hid⟩ := catalogue_complete M dimensions n s policy valid
    have hh := hopt.2 (point M dimensions id s policy) hid
    exact hh
  · intro policy valid
    obtain ⟨id, hid⟩ := catalogue_complete M dimensions n s policy valid
    have hh := ParametricPareto.selected_nondominated _ weights p selected
      (point M dimensions id s policy) hid
    exact hh

inductive Source (S A : Type) where
  | terminal (state : S)
  | branch (state : S) (action : A)
  deriving DecidableEq

def sources (M : Model Nat S (Fin actions) (Fin outcomes)) : {n : Nat} → S →
    Policy (Fin actions) (Fin outcomes) n → List (Source S (Fin actions))
  | 0, s, .stop => [.terminal s]
  | _ + 1, s, .step a after => .branch s a ::
    (M.outcomes s a).flatMap (fun o => sources M (M.next s a o) (after o))

def sameSource [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) : Source S (Fin actions) → Bool
  | .terminal s => (List.range dimensions).all (fun i => decide (M.terminal i s = N.terminal i s))
  | .branch s a => decide (M.actions s = N.actions s) &&
    decide (M.outcomes s a = N.outcomes s a) &&
    (M.outcomes s a).all (fun o => decide (M.next s a o = N.next s a o) &&
      (List.range dimensions).all (fun i => decide (M.cost i s a o = N.cost i s a o)))

theorem sameSource_branch [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) (s : S) (a : Fin actions) :
    sameSource M N dimensions (.branch s a) = true ↔
      (M.actions s = N.actions s ∧ M.outcomes s a = N.outcomes s a) ∧
      (∀ o, o ∈ M.outcomes s a → M.next s a o = N.next s a o ∧
        ∀ i, i < dimensions → M.cost i s a o = N.cost i s a o) := by
  simp [sameSource, Bool.and_eq_true, List.all_eq_true]

def reusable [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) : Bool :=
  (sources M s policy).all (sameSource M N dimensions)

theorem reusable_children [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (a : Fin actions)
    (after : Fin outcomes → Policy (Fin actions) (Fin outcomes) n)
    (h : reusable M N dimensions s (.step a after) = true) :
    sameSource M N dimensions (.branch s a) = true ∧
      ∀ o, o ∈ M.outcomes s a → reusable M N dimensions (M.next s a o) (after o) = true := by
  have all := List.all_eq_true.mp h
  refine ⟨all _ List.mem_cons_self, ?_⟩
  intro o ho
  apply List.all_eq_true.mpr
  intro source hs
  exact all source (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨o, ho, hs⟩))

theorem reusable_worst [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (policy : Policy (Fin actions) (Fin outcomes) n)
    (h : reusable M N dimensions s policy = true) (i : Nat) (hi : i < dimensions) :
    worst M i s policy = worst N i s policy := by
  induction n generalizing s with
  | zero =>
    cases policy
    have ht : sameSource M N dimensions (.terminal s) = true :=
      List.all_eq_true.mp h _ List.mem_cons_self
    exact of_decide_eq_true (List.all_eq_true.mp ht i (List.mem_range.mpr hi))
  | succ n ih =>
    cases policy with
    | step a after =>
      obtain ⟨hb, hc⟩ := reusable_children M N dimensions n s a after h
      have hb := (sameSource_branch M N dimensions s a).mp hb
      simp only [worst]
      rw [← hb.1.2]
      apply maximum_congr
      intro o ho
      rw [(hb.2 o ho).2 i hi, ← (hb.2 o ho).1]
      rw [ih _ (after o) (hc o ho)]

theorem all_congr {X : Type} (xs : List X) (f g : X → Bool)
    (h : ∀ x, x ∈ xs → f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem flatMap_congr {X Y : Type} (xs : List X) (f g : X → List Y)
    (h : ∀ x, x ∈ xs → f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem reusable_admissible [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (policy : Policy (Fin actions) (Fin outcomes) n)
    (h : reusable M N dimensions s policy = true) :
    admissible M s policy = admissible N s policy := by
  induction n generalizing s with
  | zero => cases policy; rfl
  | succ n ih =>
    cases policy with
    | step a after =>
      obtain ⟨hb, hc⟩ := reusable_children M N dimensions n s a after h
      have hb := (sameSource_branch M N dimensions s a).mp hb
      simp only [admissible]
      rw [← hb.1.1, ← hb.1.2]
      congr 1
      apply all_congr
      intro o ho
      rw [← (hb.2 o ho).1]
      exact ih _ (after o) (hc o ho)

theorem reusable_sources [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (policy : Policy (Fin actions) (Fin outcomes) n)
    (h : reusable M N dimensions s policy = true) :
    sources M s policy = sources N s policy := by
  induction n generalizing s with
  | zero => cases policy; rfl
  | succ n ih =>
    cases policy with
    | step a after =>
      obtain ⟨hb, hc⟩ := reusable_children M N dimensions n s a after h
      have hb := (sameSource_branch M N dimensions s a).mp hb
      simp only [sources]
      rw [← hb.1.2]
      congr 1
      apply flatMap_congr
      intro o ho
      rw [← (hb.2 o ho).1]
      exact ih _ (after o) (hc o ho)

theorem reusable_profile [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions id n : Nat) (s : S) (policy : Policy (Fin actions) (Fin outcomes) n)
    (h : reusable M N dimensions s policy = true) :
    point M dimensions id s policy = point N dimensions id s policy := by
  unfold point
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [reusable_worst M N dimensions n s policy h i.val i.isLt]

structure Record (S : Type) (actions outcomes horizon : Nat) where
  id : Nat
  policy : Policy (Fin actions) (Fin outcomes) horizon
  admitted : Bool
  profile : List Int
  dependencies : List (Source S (Fin actions))

def materialize (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions id : Nat)
    {n : Nat} (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) : Record S actions outcomes n :=
  ⟨id, policy, admissible M s policy, (point M dimensions id s policy).profile, sources M s policy⟩

def RecordValid (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions : Nat)
    {n : Nat} (s : S) (record : Record S actions outcomes n) : Prop :=
  record.admitted = admissible M s record.policy ∧
    record.profile = (point M dimensions record.id s record.policy).profile ∧
    record.dependencies = sources M s record.policy

theorem materialize_valid (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions id : Nat)
    {n : Nat} (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) :
    RecordValid M dimensions s (materialize M dimensions id s policy) := ⟨rfl, rfl, rfl⟩

def refresh [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (s : S) (record : Record S actions outcomes n) :
    Record S actions outcomes n :=
  if record.dependencies.all (sameSource M N dimensions) then record
  else materialize N dimensions record.id s record.policy

theorem refresh_exact [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (s : S) (record : Record S actions outcomes n)
    (valid : RecordValid M dimensions s record) :
    refresh M N dimensions s record = materialize N dimensions record.id s record.policy := by
  unfold refresh
  split
  next h =>
    have reuse : reusable M N dimensions s record.policy = true := by
      simpa [reusable, valid.2.2] using h
    have ha := (valid.1.trans (reusable_admissible M N dimensions n s record.policy reuse))
    have hp := valid.2.1.trans (congrArg ParametricPareto.Point.profile
      (reusable_profile M N dimensions record.id n s record.policy reuse))
    have hs := valid.2.2.trans (reusable_sources M N dimensions n s record.policy reuse)
    cases record
    simp only [materialize]
    simp_all
  next _ => rfl

def cache (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat) (s : S) :
    List (Record S actions outcomes n) :=
  (List.finRange (policies actions outcomes n).length).map
    (fun i => materialize M dimensions i.val s ((policies actions outcomes n).get i))

def refreshCache [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (s : S) (records : List (Record S actions outcomes n)) :
    List (Record S actions outcomes n) := records.map (refresh M N dimensions s)

theorem cache_record_lookup (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (record : Record S actions outcomes n)
    (hr : record ∈ cache M dimensions n s) :
    lookup actions outcomes n record.id = some record.policy ∧ RecordValid M dimensions s record := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hr
  subst record
  constructor
  · simp [lookup, materialize, List.get_eq_getElem]
  · exact materialize_valid M dimensions i.val s _

theorem refresh_cache_exact [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) :
    refreshCache M N dimensions s (cache M dimensions n s) = cache N dimensions n s := by
  simp only [refreshCache, cache, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact refresh_exact M N dimensions s _ (materialize_valid M dimensions i.val s _)

def cacheCatalogue {n : Nat} (records : List (Record S actions outcomes n)) : List ParametricPareto.Point :=
  (records.filter (fun r => r.admitted)).map (fun r => ⟨r.id, r.profile⟩)

theorem cache_catalogue_exact (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) :
    cacheCatalogue (cache M dimensions n s) = catalogue M dimensions n s := by
  simp only [cacheCatalogue, cache, List.filter_map, List.map_map, catalogue]
  rfl

theorem refreshed_catalogue_exact [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) :
    cacheCatalogue (refreshCache M N dimensions s (cache M dimensions n s)) =
      catalogue N dimensions n s := by
  rw [refresh_cache_exact, cache_catalogue_exact]

theorem sameSource_refl [DecidableEq S] (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) (source : Source S (Fin actions)) :
    sameSource M M dimensions source = true := by
  cases source <;> simp [sameSource]

theorem refresh_reuses [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (s : S) (record : Record S actions outcomes n)
    (same : record.dependencies.all (sameSource M N dimensions) = true) :
    refresh M N dimensions s record = record := by simp [refresh, same]

theorem refresh_recomputes [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (s : S) (record : Record S actions outcomes n)
    (changed : record.dependencies.all (sameSource M N dimensions) = false) :
    refresh M N dimensions s record = materialize N dimensions record.id s record.policy := by
  simp [refresh, changed]

def profilesNeeded [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (records : List (Record S actions outcomes n)) : Nat :=
  (records.filter (fun r => !(r.dependencies.all (sameSource M N dimensions)))).length

def profilesReused [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (records : List (Record S actions outcomes n)) : Nat :=
  (records.filter (fun r => r.dependencies.all (sameSource M N dimensions))).length

theorem profiles_partition [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (records : List (Record S actions outcomes n)) :
    profilesReused M N dimensions records + profilesNeeded M N dimensions records = records.length :=
  ParametricPareto.filter_partition records (fun r => r.dependencies.all (sameSource M N dimensions))

theorem unchanged_no_profiles [DecidableEq S] (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (records : List (Record S actions outcomes n)) :
    profilesNeeded M M dimensions records = 0 := by
  unfold profilesNeeded
  have h : records.filter (fun r => !(r.dependencies.all (sameSource M M dimensions))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro r hr
    have hs : r.dependencies.all (sameSource M M dimensions) = true :=
      List.all_eq_true.mpr (fun source _ => sameSource_refl M dimensions source)
    simp [hs]
  rw [h]
  rfl

theorem cache_length (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) :
    (cache M dimensions n s).length = (policies actions outcomes n).length := by simp [cache]

theorem refresh_length [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions : Nat) {n : Nat} (s : S) (records : List (Record S actions outcomes n)) :
    (refreshCache M N dimensions s records).length = records.length := by simp [refreshCache]

def reconcileState [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (old : ParametricPareto.State) : ParametricPareto.State :=
  ParametricPareto.reconcile old (List.range dimensions)
    (cacheCatalogue (refreshCache M N dimensions s (cache M dimensions n s)))

theorem reconcile_policy_frontier [DecidableEq S] (M N : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (old : ParametricPareto.State) (valid : ParametricPareto.Valid old)
    (p : ParametricPareto.Point) :
    p ∈ ParametricPareto.frontier (reconcileState M N dimensions n s old) ↔
      p ∈ catalogue N dimensions n s ∧
      ∀ policy : Policy (Fin actions) (Fin outcomes) n, Admissible N s policy →
        ParametricPareto.dominates (List.range dimensions) (point N dimensions 0 s policy) p = false := by
  unfold reconcileState
  rw [refreshed_catalogue_exact]
  rw [ParametricPareto.reconcile_frontier old valid]
  have h := policy_frontier_exact N dimensions n s p
  rw [ParametricPareto.frontier_exact _ (state_valid N dimensions n s)] at h
  exact h

def within (dimensions : Nat) (budget : Nat → Nat) (p : ParametricPareto.Point) : Bool :=
  (List.range dimensions).all (fun i => decide (ParametricPareto.cost p i ≤ (budget i : Int)))

theorem within_exact (dimensions : Nat) (budget : Nat → Nat) (p : ParametricPareto.Point) :
    within dimensions budget p = true ↔
      ∀ i, i < dimensions → ParametricPareto.cost p i ≤ (budget i : Int) := by
  simp [within, List.all_eq_true]

def BudgetAdmissible (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions : Nat)
    (budget : Nat → Nat) {n : Nat} (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) : Prop :=
  Admissible M s policy ∧ ∀ i, i < dimensions → worst M i s policy ≤ budget i

theorem point_within (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions id : Nat)
    (budget : Nat → Nat) {n : Nat} (s : S) (policy : Policy (Fin actions) (Fin outcomes) n) :
    within dimensions budget (point M dimensions id s policy) = true ↔
      ∀ i, i < dimensions → worst M i s policy ≤ budget i := by
  rw [within_exact]
  constructor
  · intro h i hi
    have hh := h i hi
    rw [point_cost M dimensions id s policy i hi] at hh
    exact Int.ofNat_le.mp hh
  · intro h i hi
    rw [point_cost M dimensions id s policy i hi]
    exact Int.ofNat_le.mpr (h i hi)

def boundedCatalogue (M : Model Nat S (Fin actions) (Fin outcomes)) (dimensions n : Nat)
    (s : S) (budget : Nat → Nat) : List ParametricPareto.Point :=
  (catalogue M dimensions n s).filter (within dimensions budget)

theorem bounded_catalogue_complete (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (budget : Nat → Nat)
    (policy : Policy (Fin actions) (Fin outcomes) n) (h : BudgetAdmissible M dimensions budget s policy) :
    ∃ id, point M dimensions id s policy ∈ boundedCatalogue M dimensions n s budget := by
  obtain ⟨id, hid⟩ := catalogue_complete M dimensions n s policy h.1
  exact ⟨id, List.mem_filter.mpr ⟨hid, (point_within M dimensions id budget s policy).mpr h.2⟩⟩

theorem bounded_catalogue_sound (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (budget : Nat → Nat) (p : ParametricPareto.Point)
    (hp : p ∈ boundedCatalogue M dimensions n s budget) :
    ∃ policy : Policy (Fin actions) (Fin outcomes) n,
      BudgetAdmissible M dimensions budget s policy ∧ p = point M dimensions p.id s policy := by
  obtain ⟨hm, hb⟩ := List.mem_filter.mp hp
  obtain ⟨policy, ha, he⟩ := catalogue_sound M dimensions n s p hm
  refine ⟨policy, ⟨ha, ?_⟩, he⟩
  rw [he] at hb
  exact (point_within M dimensions p.id budget s policy).mp hb

theorem budget_downward_closed (dimensions : Nat) (budget : Nat → Nat)
    (p q : ParametricPareto.Point) (hp : within dimensions budget p = true)
    (dominates : ParametricPareto.dominates (List.range dimensions) q p = true) :
    within dimensions budget q = true := by
  apply (within_exact dimensions budget q).mpr
  intro i hi
  have hd := (FiniteFrontier.pareto_exact (List.range dimensions) ParametricPareto.cost q p).mp dominates
  exact Int.le_trans (hd.1 i (List.mem_range.mpr hi)) ((within_exact dimensions budget p).mp hp i hi)

theorem budget_continuation (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (budget : Nat → Nat) (s : S) (a : Fin actions)
    (after : Fin outcomes → Policy (Fin actions) (Fin outcomes) n)
    (h : BudgetAdmissible M dimensions budget s (.step a after))
    (o : Fin outcomes) (ho : o ∈ M.outcomes s a) :
    (∀ i, i < dimensions → M.cost i s a o ≤ budget i) ∧
      BudgetAdmissible M dimensions (fun i => budget i - M.cost i s a o)
        (M.next s a o) (after o) := by
  have bound : ∀ i, i < dimensions →
      M.cost i s a o + worst M i (M.next s a o) (after o) ≤ budget i := by
    intro i hi
    exact Nat.le_trans (maximum_upper (M.outcomes s a)
      (fun out => M.cost i s a out + worst M i (M.next s a out) (after out)) o ho) (h.2 i hi)
  refine ⟨?_, ⟨h.1.2 o ho, ?_⟩⟩
  · intro i hi; have hh := bound i hi; omega
  · intro i hi
    have hh := bound i hi
    change worst M i (M.next s a o) (after o) ≤ budget i - M.cost i s a o
    omega

theorem budget_continuation_exists (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (budget : Nat → Nat) (s : S) (a : Fin actions)
    (after : Fin outcomes → Policy (Fin actions) (Fin outcomes) n)
    (h : BudgetAdmissible M dimensions budget s (.step a after))
    (o : Fin outcomes) (ho : o ∈ M.outcomes s a) :
    boundedCatalogue M dimensions n (M.next s a o) (fun i => budget i - M.cost i s a o) ≠ [] := by
  have hc := (budget_continuation M dimensions n budget s a after h o ho).2
  obtain ⟨id, hid⟩ := bounded_catalogue_complete M dimensions n (M.next s a o) _ (after o) hc
  intro he
  rw [he] at hid
  simp at hid

theorem budget_ledger_step (spent budget initial cost : Nat)
    (ledger : spent + budget = initial) (supported : cost ≤ budget) :
    (spent + cost) + (budget - cost) = initial := by omega

theorem bounded_frontier_nondominated (M : Model Nat S (Fin actions) (Fin outcomes))
    (dimensions n : Nat) (s : S) (budget : Nat → Nat) (p : ParametricPareto.Point)
    (hp : p ∈ FiniteFrontier.frontier (boundedCatalogue M dimensions n s budget)
      (ParametricPareto.dominates (List.range dimensions))) :
    ∀ policy : Policy (Fin actions) (Fin outcomes) n, Admissible M s policy →
      ParametricPareto.dominates (List.range dimensions) (point M dimensions 0 s policy) p = false := by
  have hf := (FiniteFrontier.frontier_exact _ _ p).mp hp
  have hb := (List.mem_filter.mp hf.1).2
  intro policy valid
  obtain ⟨id, hid⟩ := catalogue_complete M dimensions n s policy valid
  cases hd : ParametricPareto.dominates (List.range dimensions) (point M dimensions id s policy) p with
  | false => exact hd
  | true =>
    have within := budget_downward_closed dimensions budget p _ hb hd
    have hm : point M dimensions id s policy ∈ boundedCatalogue M dimensions n s budget :=
      List.mem_filter.mpr ⟨hid, within⟩
    have hn := hf.2 _ hm
    rw [hd] at hn
    contradiction

end ParetoPolicy
