import FiniteFrontier

namespace ParametricPareto

structure Point where
  id : Nat
  profile : List Int
  deriving DecidableEq, Repr

def cost (p : Point) (i : Nat) : Int := (p.profile[i]?).getD 0

def dominates (axes : List Nat) (y x : Point) : Bool :=
  FiniteFrontier.strictPareto axes cost y x

structure Cell where
  left : Point
  right : Point
  value : Bool
  deriving DecidableEq, Repr

def read : List Cell → Point → Point → Bool
  | [], _, _ => false
  | c :: cs, y, x => if c.left = y ∧ c.right = x then c.value else read cs y x

def pairs (xs : List Point) : List (Point × Point) :=
  xs.flatMap (fun y => xs.map (fun x => (y, x)))

theorem mem_pairs (xs : List Point) (y x : Point) :
    (y,x) ∈ pairs xs ↔ y ∈ xs ∧ x ∈ xs := by
  simp [pairs]

theorem pairs_length (xs : List Point) : (pairs xs).length = xs.length * xs.length := by
  have h : ∀ ys : List Point,
      (ys.flatMap (fun y => xs.map (fun x => (y,x)))).length = ys.length * xs.length := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih => simp [List.flatMap_cons, ih, Nat.add_mul, Nat.add_comm]
  exact h xs

def cells (ks : List (Point × Point)) (f : Point → Point → Bool) : List Cell :=
  ks.map (fun k => ⟨k.1, k.2, f k.1 k.2⟩)

theorem read_cells (ks : List (Point × Point)) (f : Point → Point → Bool)
    (y x : Point) (h : (y,x) ∈ ks) : read (cells ks f) y x = f y x := by
  induction ks with
  | nil => simp at h
  | cons k ks ih =>
    simp only [cells, List.map_cons, read]
    split
    next he => simp [he.1, he.2]
    next hn =>
      apply ih
      rcases List.mem_cons.mp h with hk | hk
      · have he : k.1 = y ∧ k.2 = x := by cases k; cases hk; exact ⟨rfl,rfl⟩
        exact False.elim (hn he)
      · exact hk

structure State where
  axes : List Nat
  catalogue : List Point
  comparisons : List Cell
  deriving Repr

def Valid (s : State) : Prop :=
  ∀ y ∈ s.catalogue, ∀ x ∈ s.catalogue,
    read s.comparisons y x = dominates s.axes y x

def build (axes : List Nat) (catalogue : List Point) : State :=
  ⟨axes, catalogue, cells (pairs catalogue) (dominates axes)⟩

theorem build_valid (axes : List Nat) (catalogue : List Point) :
    Valid (build axes catalogue) := by
  intro y hy x hx
  exact read_cells _ _ y x ((mem_pairs catalogue y x).mpr ⟨hy,hx⟩)

def reusable (old : State) (axes : List Nat) (y x : Point) : Bool :=
  decide (old.axes = axes ∧ y ∈ old.catalogue ∧ x ∈ old.catalogue)

def updatedValue (old : State) (axes : List Nat) (y x : Point) : Bool :=
  if reusable old axes y x then read old.comparisons y x else dominates axes y x

def reconcile (old : State) (axes : List Nat) (catalogue : List Point) : State :=
  ⟨axes, catalogue, cells (pairs catalogue) (updatedValue old axes)⟩

theorem reused_value_exact (old : State) (valid : Valid old) (axes : List Nat)
    (y x : Point) : updatedValue old axes y x = dominates axes y x := by
  unfold updatedValue
  split
  next h =>
    have hh := of_decide_eq_true h
    obtain ⟨ha,hy,hx⟩ := hh
    rw [valid y hy x hx, ha]
  next _ => rfl

theorem reconcile_valid (old : State) (valid : Valid old) (axes : List Nat)
    (catalogue : List Point) : Valid (reconcile old axes catalogue) := by
  intro y hy x hx
  change read (cells (pairs catalogue) (updatedValue old axes)) y x = _
  rw [read_cells _ _ y x ((mem_pairs catalogue y x).mpr ⟨hy,hx⟩)]
  exact reused_value_exact old valid axes y x

theorem reconcile_reuses (old : State) (axes : List Nat) (y x : Point)
    (h : reusable old axes y x = true) :
    updatedValue old axes y x = read old.comparisons y x := by
  simp [updatedValue, h]

theorem reconcile_recomputes (old : State) (axes : List Nat) (y x : Point)
    (h : reusable old axes y x = false) :
    updatedValue old axes y x = dominates axes y x := by
  simp [updatedValue, h]

theorem reconcile_storage (old : State) (axes : List Nat) (catalogue : List Point) :
    (reconcile old axes catalogue).comparisons.length = catalogue.length * catalogue.length := by
  simp [reconcile, cells, pairs_length]

theorem build_storage (axes : List Nat) (catalogue : List Point) :
    (build axes catalogue).comparisons.length = catalogue.length * catalogue.length := by
  simp [build, cells, pairs_length]

theorem reconcile_keys (old : State) (axes : List Nat) (catalogue : List Point) :
    (reconcile old axes catalogue).comparisons.map (fun c => (c.left,c.right)) = pairs catalogue := by
  simp [reconcile, cells, List.map_map, Function.comp_def]

theorem reconcile_cells_current (old : State) (axes : List Nat) (catalogue : List Point)
    (c : Cell) (hc : c ∈ (reconcile old axes catalogue).comparisons) :
    c.left ∈ catalogue ∧ c.right ∈ catalogue := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hc
  exact (mem_pairs catalogue k.1 k.2).mp hk

def frontier (s : State) : List Point :=
  FiniteFrontier.frontier s.catalogue (read s.comparisons)

theorem frontier_exact (s : State) (valid : Valid s) (x : Point) :
    x ∈ frontier s ↔
      x ∈ s.catalogue ∧ ∀ y ∈ s.catalogue, dominates s.axes y x = false := by
  rw [frontier, FiniteFrontier.frontier_exact]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => (valid y hy x hx) ▸ h y hy⟩
  · rintro ⟨hx,h⟩
    exact ⟨hx, fun y hy => (valid y hy x hx).symm ▸ h y hy⟩

theorem frontier_original (s : State) (valid : Valid s) (x : Point) :
    x ∈ frontier s ↔
      x ∈ FiniteFrontier.frontier s.catalogue (FiniteFrontier.strictPareto s.axes cost) := by
  rw [frontier_exact s valid, FiniteFrontier.frontier_exact]
  rfl

theorem reconcile_frontier (old : State) (valid : Valid old) (axes : List Nat)
    (catalogue : List Point) (x : Point) :
    x ∈ frontier (reconcile old axes catalogue) ↔
      x ∈ catalogue ∧ ∀ y ∈ catalogue, dominates axes y x = false :=
  frontier_exact _ (reconcile_valid old valid axes catalogue) x

def comparisonsNeeded (old : State) (axes : List Nat) (catalogue : List Point) : Nat :=
  ((pairs catalogue).filter (fun k => !(reusable old axes k.1 k.2))).length

def comparisonsReused (old : State) (axes : List Nat) (catalogue : List Point) : Nat :=
  ((pairs catalogue).filter (fun k => reusable old axes k.1 k.2)).length

theorem filter_partition {A : Type} (xs : List A) (p : A → Bool) :
    (xs.filter p).length + (xs.filter (fun x => !(p x))).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [List.filter_cons, h] <;> omega

theorem comparison_partition (old : State) (axes : List Nat) (catalogue : List Point) :
    comparisonsReused old axes catalogue + comparisonsNeeded old axes catalogue =
      catalogue.length * catalogue.length := by
  exact (filter_partition (pairs catalogue) (fun k => reusable old axes k.1 k.2)).trans
    (pairs_length catalogue)

theorem unchanged_no_comparisons (old : State) :
    comparisonsNeeded old old.axes old.catalogue = 0 := by
  unfold comparisonsNeeded
  have h : (pairs old.catalogue).filter
      (fun k => !(reusable old old.axes k.1 k.2)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k hk
    obtain ⟨hy,hx⟩ := (mem_pairs old.catalogue k.1 k.2).mp hk
    simp [reusable, hy, hx]
  rw [h]
  rfl

theorem filter_pair_product (xs : List Point) (p : Point → Bool) :
    ((pairs xs).filter (fun k => p k.1 && p k.2)).length =
      (xs.filter p).length * (xs.filter p).length := by
  have h : ∀ ys : List Point,
      ((ys.flatMap (fun y => xs.map (fun x => (y,x)))).filter
        (fun k => p k.1 && p k.2)).length =
      (ys.filter p).length * (xs.filter p).length := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
      rw [List.flatMap_cons, List.filter_append, List.length_append, ih]
      rw [List.filter_map]
      cases hp : p y <;>
        simp [hp, Function.comp_def, List.filter_cons, Nat.add_mul, Nat.add_comm]
  exact h xs

def retained (old : State) (catalogue : List Point) : List Point :=
  catalogue.filter (fun p => decide (p ∈ old.catalogue))

theorem reused_square (old : State) (catalogue : List Point) :
    comparisonsReused old old.axes catalogue = (retained old catalogue).length ^ 2 := by
  have he : ∀ k : Point × Point, reusable old old.axes k.1 k.2 =
      (decide (k.1 ∈ old.catalogue) && decide (k.2 ∈ old.catalogue)) := by
    intro k
    by_cases hy : k.1 ∈ old.catalogue <;> by_cases hx : k.2 ∈ old.catalogue <;>
      simp [reusable, hy, hx]
  unfold comparisonsReused
  simp only [he]
  simpa [retained, Nat.pow_succ] using
    filter_pair_product catalogue (fun p => decide (p ∈ old.catalogue))

theorem needed_square (old : State) (catalogue : List Point) :
    comparisonsNeeded old old.axes catalogue =
      catalogue.length ^ 2 - (retained old catalogue).length ^ 2 := by
  have h := comparison_partition old old.axes catalogue
  rw [reused_square] at h
  have hp : catalogue.length ^ 2 = catalogue.length * catalogue.length := by
    simp [Nat.pow_succ]
  omega

theorem retraction_no_comparisons (old : State) (catalogue : List Point)
    (h : ∀ p ∈ catalogue, p ∈ old.catalogue) :
    comparisonsNeeded old old.axes catalogue = 0 := by
  have hr : retained old catalogue = catalogue := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact decide_eq_true (h p hp)
  rw [needed_square, hr]
  omega

theorem append_retained (old : State) (added : List Point)
    (fresh : ∀ p ∈ added, p ∉ old.catalogue) :
    retained old (old.catalogue ++ added) = old.catalogue := by
  unfold retained
  rw [List.filter_append]
  have hold : old.catalogue.filter (fun p => decide (p ∈ old.catalogue)) = old.catalogue := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact decide_eq_true hp
  have hnew : added.filter (fun p => decide (p ∈ old.catalogue)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    simp [fresh p hp]
  rw [hold, hnew, List.append_nil]

theorem append_comparison_work (old : State) (added : List Point)
    (fresh : ∀ p ∈ added, p ∉ old.catalogue) :
    comparisonsNeeded old old.axes (old.catalogue ++ added) =
      2 * old.catalogue.length * added.length + added.length * added.length := by
  rw [needed_square, append_retained old added fresh, List.length_append]
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  have h : (old.catalogue.length + added.length) * (old.catalogue.length + added.length) =
      old.catalogue.length * old.catalogue.length +
      (2 * old.catalogue.length * added.length + added.length * added.length) := by
    have ht : 2 * old.catalogue.length * added.length =
        old.catalogue.length * added.length + old.catalogue.length * added.length := by
      rw [Nat.two_mul, Nat.add_mul]
    rw [ht]
    simp only [Nat.add_mul, Nat.mul_add]
    rw [Nat.mul_comm added.length old.catalogue.length]
    omega
  rw [h]
  omega

theorem schema_change_recomputes (old : State) (axes : List Nat) (catalogue : List Point)
    (different : old.axes ≠ axes) :
    comparisonsNeeded old axes catalogue = catalogue.length ^ 2 := by
  unfold comparisonsNeeded
  have h : (pairs catalogue).filter (fun k => !(reusable old axes k.1 k.2)) = pairs catalogue := by
    apply List.filter_eq_self.mpr
    intro k _
    simp [reusable, different]
  rw [h, pairs_length]
  simp [Nat.pow_succ]

def replay (s : State) : List (List Nat × List Point) → State
  | [] => s
  | e :: es => replay (reconcile s e.1 e.2) es

theorem replay_valid (s : State) (h : Valid s) (events : List (List Nat × List Point)) :
    Valid (replay s events) := by
  induction events generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (reconcile_valid s h e.1 e.2)

theorem every_prefix_exact (s : State) (h : Valid s)
    (events : List (List Nat × List Point)) (n : Nat) (x : Point) :
    x ∈ frontier (replay s (events.take n)) ↔
      x ∈ (replay s (events.take n)).catalogue ∧
      ∀ y ∈ (replay s (events.take n)).catalogue,
        dominates (replay s (events.take n)).axes y x = false :=
  frontier_exact _ (replay_valid s h _) x

def weighted (axes : List Nat) (weights : Nat → Nat) (p : Point) : Int :=
  (axes.map (fun i => (weights i : Int) * cost p i)).sum

def total (axes : List Nat) (p : Point) : Int :=
  (axes.map (cost p)).sum

theorem sum_monotone (axes : List Nat) (f g : Nat → Int)
    (h : ∀ i ∈ axes, f i ≤ g i) :
    (axes.map f).sum ≤ (axes.map g).sum := by
  induction axes with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Int.add_le_add (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

theorem sum_strict (axes : List Nat) (f g : Nat → Int)
    (h : ∀ i ∈ axes, f i ≤ g i) (strict : ∃ i ∈ axes, f i < g i) :
    (axes.map f).sum < (axes.map g).sum := by
  induction axes with
  | nil => simp at strict
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨i,hi,hs⟩ := strict
    rcases List.mem_cons.mp hi with rfl | hi
    · exact Int.add_lt_add_of_lt_of_le hs (sum_monotone as f g (fun i hi => h i (by simp [hi])))
    · exact Int.add_lt_add_of_le_of_lt (h a (by simp))
        (ih (fun i hi => h i (by simp [hi])) ⟨i,hi,hs⟩)

theorem dominates_weighted (axes : List Nat) (weights : Nat → Nat) (y x : Point)
    (h : dominates axes y x = true) : weighted axes weights y ≤ weighted axes weights x := by
  have hp := (FiniteFrontier.pareto_exact axes cost y x).mp h
  exact sum_monotone axes _ _ (fun i hi =>
    Int.mul_le_mul_of_nonneg_left (hp.1 i hi) (Int.ofNat_zero_le (weights i)))

theorem dominates_total (axes : List Nat) (y x : Point)
    (h : dominates axes y x = true) : total axes y < total axes x := by
  have hp := (FiniteFrontier.pareto_exact axes cost y x).mp h
  exact sum_strict axes _ _ hp.1 hp.2

abbrev Key := Int × Int × Nat

def key (axes : List Nat) (weights : Nat → Nat) (p : Point) : Key :=
  (weighted axes weights p, total axes p, p.id)

def keyLE (a b : Key) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 ≤ b.2.2)))

instance (a b : Key) : Decidable (keyLE a b) := inferInstanceAs (Decidable (_ ∨ _))

theorem keyLE_refl (a : Key) : keyLE a a := by simp [keyLE]

theorem keyLE_total (a b : Key) : keyLE a b ∨ keyLE b a := by
  unfold keyLE
  omega

theorem keyLE_trans (a b c : Key) (hab : keyLE a b) (hbc : keyLE b c) : keyLE a c := by
  unfold keyLE at *
  omega

theorem keyLE_primary (a b : Key) (h : keyLE a b) : a.1 ≤ b.1 := by
  unfold keyLE at h
  omega

def best (rank : Point → Key) (a b : Point) : Point :=
  if keyLE (rank a) (rank b) then a else b

theorem best_mem (rank : Point → Key) (a b : Point) : best rank a b = a ∨ best rank a b = b := by
  unfold best
  split <;> simp

theorem best_le_left (rank : Point → Key) (a b : Point) :
    keyLE (rank (best rank a b)) (rank a) := by
  unfold best
  split
  next _ => exact keyLE_refl _
  next h => exact (keyLE_total (rank a) (rank b)).resolve_left h

theorem best_le_right (rank : Point → Key) (a b : Point) :
    keyLE (rank (best rank a b)) (rank b) := by
  unfold best
  split
  next h => exact h
  next _ => exact keyLE_refl _

def choose (rank : Point → Key) : List Point → Option Point
  | [] => none
  | a :: as => match choose rank as with
    | none => some a
    | some b => some (best rank a b)

theorem choose_none (rank : Point → Key) (xs : List Point) :
    choose rank xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [choose]
  | cons a as => cases h : choose rank as <;> simp [choose, h]

theorem choose_correct (rank : Point → Key) (xs : List Point) (p : Point)
    (h : choose rank xs = some p) :
    p ∈ xs ∧ ∀ q ∈ xs, keyLE (rank p) (rank q) := by
  induction xs generalizing p with
  | nil => simp [choose] at h
  | cons a as ih =>
    cases ht : choose rank as with
    | none =>
      have hp : a = p := by simpa [choose, ht] using h
      have hempty := (choose_none rank as).mp ht
      subst p
      subst as
      exact ⟨by simp, fun q hq => by simpa using (List.mem_singleton.mp hq) ▸ keyLE_refl (rank a)⟩
    | some b =>
      have hp : best rank a b = p := by simpa [choose, ht] using h
      have hb := ih b ht
      subst p
      constructor
      · rcases best_mem rank a b with ha | he
        · simp [ha]
        · simp [he, hb.1]
      · intro q hq
        rcases List.mem_cons.mp hq with he | hq
        · subst q
          exact best_le_left rank a b
        · exact keyLE_trans _ _ _ (best_le_right rank a b) (hb.2 q hq)

def select (s : State) (weights : Nat → Nat) : Option Point :=
  choose (key s.axes weights) s.catalogue

theorem selected_weighted_optimal (s : State) (weights : Nat → Nat) (p : Point)
    (h : select s weights = some p) :
    p ∈ s.catalogue ∧ ∀ q ∈ s.catalogue,
      weighted s.axes weights p ≤ weighted s.axes weights q := by
  have hp := choose_correct (key s.axes weights) s.catalogue p h
  exact ⟨hp.1, fun q hq => keyLE_primary _ _ (hp.2 q hq)⟩

theorem selected_nondominated (s : State) (weights : Nat → Nat) (p : Point)
    (h : select s weights = some p) :
    ∀ q ∈ s.catalogue, dominates s.axes q p = false := by
  have hp := choose_correct (key s.axes weights) s.catalogue p h
  intro q hq
  cases hd : dominates s.axes q p with
  | false => rfl
  | true =>
    have hw := dominates_weighted s.axes weights q p hd
    have ht := dominates_total s.axes q p hd
    have hk := hp.2 q hq
    simp only [key, keyLE] at hk
    omega

theorem selected_on_frontier (s : State) (valid : Valid s) (weights : Nat → Nat)
    (p : Point) (h : select s weights = some p) : p ∈ frontier s := by
  exact (frontier_exact s valid p).mpr
    ⟨(selected_weighted_optimal s weights p h).1, selected_nondominated s weights p h⟩

theorem nonempty_selects (s : State) (weights : Nat → Nat)
    (h : s.catalogue ≠ []) : ∃ p, select s weights = some p := by
  cases hs : select s weights with
  | none => exact False.elim (h ((choose_none _ _).mp hs))
  | some p => exact ⟨p, rfl⟩

def weaklyLE (axes : List Nat) (y x : Point) : Bool :=
  axes.all (fun i => decide (cost y i ≤ cost x i))

theorem weaklyLE_exact (axes : List Nat) (y x : Point) :
    weaklyLE axes y x = true ↔ ∀ i ∈ axes, cost y i ≤ cost x i := by
  simp [weaklyLE, List.all_eq_true]

theorem weaklyLE_refl (axes : List Nat) (x : Point) : weaklyLE axes x x = true := by
  simp [weaklyLE]

theorem weaklyLE_trans (axes : List Nat) (z y x : Point)
    (hzy : weaklyLE axes z y = true) (hyx : weaklyLE axes y x = true) :
    weaklyLE axes z x = true := by
  apply (weaklyLE_exact axes z x).mpr
  intro i hi
  exact Int.le_trans ((weaklyLE_exact axes z y).mp hzy i hi)
    ((weaklyLE_exact axes y x).mp hyx i hi)

theorem dominates_weaklyLE (axes : List Nat) (y x : Point)
    (h : dominates axes y x = true) : weaklyLE axes y x = true := by
  exact (weaklyLE_exact axes y x).mpr
    ((FiniteFrontier.pareto_exact axes cost y x).mp h).1

theorem frontier_coverage (s : State) (valid : Valid s) (x : Point)
    (hx : x ∈ s.catalogue) :
    ∃ y, y ∈ frontier s ∧ weaklyLE s.axes y x = true := by
  let eligible := s.catalogue.filter (fun y => weaklyLE s.axes y x)
  have hex : x ∈ eligible := by
    exact List.mem_filter.mpr ⟨hx, weaklyLE_refl s.axes x⟩
  have hne : eligible ≠ [] := by intro h; rw [h] at hex; simp at hex
  let localState := build s.axes eligible
  obtain ⟨y,hy⟩ := nonempty_selects localState (fun _ => 0) hne
  have hylocal := (selected_weighted_optimal localState (fun _ => 0) y hy).1
  have hymem : y ∈ s.catalogue ∧ weaklyLE s.axes y x = true := List.mem_filter.mp hylocal
  refine ⟨y, (frontier_exact s valid y).mpr ⟨hymem.1, ?_⟩, hymem.2⟩
  intro q hq
  cases hd : dominates s.axes q y with
  | false => rfl
  | true =>
    have hqx := weaklyLE_trans s.axes q y x (dominates_weaklyLE s.axes q y hd) hymem.2
    have hqeligible : q ∈ localState.catalogue := List.mem_filter.mpr ⟨hq,hqx⟩
    have hn := selected_nondominated localState (fun _ => 0) y hy q hqeligible
    change dominates s.axes q y = false at hn
    rw [hd] at hn
    contradiction

theorem frontier_nonempty (s : State) (valid : Valid s) (hne : s.catalogue ≠ []) :
    frontier s ≠ [] := by
  obtain ⟨x,hx⟩ := nonempty_selects s (fun _ => 0) hne
  have hf := selected_on_frontier s valid (fun _ => 0) x hx
  intro he
  rw [he] at hf
  simp at hf

def selectFrontier (s : State) (weights : Nat → Nat) : Option Point :=
  choose (key s.axes weights) (frontier s)

theorem frontier_selected_optimal (s : State) (valid : Valid s) (weights : Nat → Nat)
    (p : Point) (h : selectFrontier s weights = some p) :
    p ∈ frontier s ∧ ∀ q ∈ s.catalogue,
      weighted s.axes weights p ≤ weighted s.axes weights q := by
  have hp := choose_correct (key s.axes weights) (frontier s) p h
  refine ⟨hp.1, ?_⟩
  intro q hq
  obtain ⟨r,hr,hweak⟩ := frontier_coverage s valid q hq
  have hpr := keyLE_primary _ _ (hp.2 r hr)
  have hrq : weighted s.axes weights r ≤ weighted s.axes weights q := by
    apply sum_monotone
    intro i hi
    exact Int.mul_le_mul_of_nonneg_left ((weaklyLE_exact s.axes r q).mp hweak i hi)
      (Int.ofNat_zero_le (weights i))
  exact Int.le_trans hpr hrq

theorem nonempty_frontier_selects (s : State) (valid : Valid s) (weights : Nat → Nat)
    (h : s.catalogue ≠ []) : ∃ p, selectFrontier s weights = some p := by
  cases hs : selectFrontier s weights with
  | none => exact False.elim ((frontier_nonempty s valid h) ((choose_none _ _).mp hs))
  | some p => exact ⟨p, rfl⟩

theorem frontier_retains_equal_identities (s : State) (valid : Valid s) (x y : Point)
    (hx : x ∈ frontier s) (hy : y ∈ s.catalogue)
    (same : ∀ i ∈ s.axes, cost x i = cost y i) : y ∈ frontier s := by
  have hfx := (frontier_exact s valid x).mp hx
  apply (frontier_exact s valid y).mpr
  refine ⟨hy, ?_⟩
  intro q hq
  cases hd : dominates s.axes q y with
  | false => rfl
  | true =>
    have hp := (FiniteFrontier.pareto_exact s.axes cost q y).mp hd
    have hd' : dominates s.axes q x = true := by
      apply (FiniteFrontier.pareto_exact s.axes cost q x).mpr
      constructor
      · intro i hi
        rw [same i hi]
        exact hp.1 i hi
      · obtain ⟨i,hi,hs⟩ := hp.2
        exact ⟨i,hi,(same i hi).symm ▸ hs⟩
    rw [hfx.2 q hq] at hd'
    contradiction

theorem parametric_every_prefix (s : State) (valid : Valid s)
    (events : List (List Nat × List Point)) (n : Nat) (weights : Nat → Nat)
    (p : Point) (h : select (replay s (events.take n)) weights = some p) :
    p ∈ frontier (replay s (events.take n)) ∧
      ∀ q ∈ (replay s (events.take n)).catalogue,
        weighted (replay s (events.take n)).axes weights p ≤
        weighted (replay s (events.take n)).axes weights q := by
  exact ⟨selected_on_frontier _ (replay_valid s valid _) weights p h,
    (selected_weighted_optimal _ weights p h).2⟩

abbrev Certified := { s : State // Valid s }

def start (axes : List Nat) (catalogue : List Point) : Certified :=
  ⟨build axes catalogue, build_valid axes catalogue⟩

def advance (old : Certified) (axes : List Nat) (catalogue : List Point) : Certified :=
  ⟨reconcile old.val axes catalogue, reconcile_valid old.val old.property axes catalogue⟩

theorem certified_frontier (s : Certified) (x : Point) :
    x ∈ frontier s.val ↔ x ∈ s.val.catalogue ∧
      ∀ y ∈ s.val.catalogue, dominates s.val.axes y x = false :=
  frontier_exact s.val s.property x

theorem certified_selection (s : Certified) (weights : Nat → Nat) (p : Point)
    (h : selectFrontier s.val weights = some p) :
    p ∈ frontier s.val ∧ ∀ q ∈ s.val.catalogue,
      weighted s.val.axes weights p ≤ weighted s.val.axes weights q :=
  frontier_selected_optimal s.val s.property weights p h

theorem weighted_scale (axes : List Nat) (weights : Nat → Nat) (scale : Nat) (p : Point) :
    weighted axes (fun i => scale * weights i) p = (scale : Int) * weighted axes weights p := by
  induction axes with
  | nil => simp [weighted]
  | cons a as ih =>
    change (scale * weights a : Nat) * cost p a +
      weighted as (fun i => scale * weights i) p =
      (scale : Int) * ((weights a : Int) * cost p a + weighted as weights p)
    rw [ih, Int.natCast_mul, Int.mul_add, Int.mul_assoc]

theorem positive_mul_lt_iff (scale a b : Int) (positive : 0 < scale) :
    scale * a < scale * b ↔ a < b := by
  constructor
  · intro h
    by_cases hab : a < b
    · exact hab
    · have hba : b ≤ a := by omega
      have hm := Int.mul_le_mul_of_nonneg_left hba (show 0 ≤ scale by omega)
      omega
  · intro h
    exact Int.mul_lt_mul_of_pos_left h positive

theorem scaled_key_order (axes : List Nat) (weights : Nat → Nat) (scale : Nat)
    (positive : 0 < scale) (a b : Point) :
    keyLE (key axes (fun i => scale * weights i) a)
      (key axes (fun i => scale * weights i) b) ↔
    keyLE (key axes weights a) (key axes weights b) := by
  have hp : (0 : Int) < (scale : Int) := Int.ofNat_pos.mpr positive
  have hn : (scale : Int) ≠ 0 := by omega
  simp only [keyLE, key, weighted_scale, positive_mul_lt_iff _ _ _ hp,
    Int.mul_eq_mul_left_iff hn]

theorem choose_order_congr (left right : Point → Key)
    (same : ∀ a b, keyLE (left a) (left b) ↔ keyLE (right a) (right b))
    (xs : List Point) : choose left xs = choose right xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [choose, ih]
    cases h : choose right as with
    | none => rfl
    | some b => simp [best, same a b]

theorem parameter_scale_invariant (s : State) (weights : Nat → Nat) (scale : Nat)
    (positive : 0 < scale) :
    selectFrontier s (fun i => scale * weights i) = selectFrontier s weights := by
  exact choose_order_congr _ _ (scaled_key_order s.axes weights scale positive) _

abbrev Linear := List (Nat × Int)

structure Inequality where
  against : Point
  terms : Linear
  deriving DecidableEq, Repr

structure Region where
  point : Point
  inequalities : List Inequality
  deriving DecidableEq, Repr

def coefficients (axes : List Nat) (p q : Point) : Linear :=
  axes.map (fun i => (i, cost q i - cost p i))

def evaluate (weights : Nat → Nat) (terms : Linear) : Int :=
  (terms.map (fun term => (weights term.1 : Int) * term.2)).sum

def region (s : State) (p : Point) : Region :=
  ⟨p, s.catalogue.map (fun q => ⟨q,coefficients s.axes p q⟩)⟩

def regions (s : State) : List Region := (frontier s).map (region s)

theorem region_points (s : State) : (regions s).map Region.point = frontier s := by
  simp [regions, region, List.map_map, Function.comp_def]

def acceptsParameters (weights : Nat → Nat) (r : Region) : Bool :=
  r.inequalities.all (fun inequality => decide (0 ≤ evaluate weights inequality.terms))

theorem evaluate_difference (axes : List Nat) (weights : Nat → Nat) (p q : Point) :
    evaluate weights (coefficients axes p q) =
      weighted axes weights q - weighted axes weights p := by
  induction axes with
  | nil => simp [evaluate, coefficients, weighted]
  | cons a as ih =>
    change (weights a : Int) * (cost q a - cost p a) +
      evaluate weights (coefficients as p q) =
      ((weights a : Int) * cost q a + weighted as weights q) -
      ((weights a : Int) * cost p a + weighted as weights p)
    rw [ih, Int.mul_sub]
    omega

theorem region_exact (s : State) (weights : Nat → Nat) (p : Point) :
    acceptsParameters weights (region s p) = true ↔
      ∀ q ∈ s.catalogue, weighted s.axes weights p ≤ weighted s.axes weights q := by
  simp only [acceptsParameters, region, List.all_map, Function.comp_def,
    List.all_eq_true, decide_eq_true_eq, evaluate_difference]
  constructor
  · intro h q hq
    have hh := h q hq
    omega
  · intro h q hq
    have hh := h q hq
    omega

theorem region_member_exact (s : State) (r : Region) (hr : r ∈ regions s)
    (weights : Nat → Nat) :
    r.point ∈ frontier s ∧
      (acceptsParameters weights r = true ↔
        ∀ q ∈ s.catalogue, weighted s.axes weights r.point ≤ weighted s.axes weights q) := by
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hr
  exact ⟨hp,region_exact s weights p⟩

theorem regions_cover_parameters (s : State) (valid : Valid s)
    (nonempty : s.catalogue ≠ []) (weights : Nat → Nat) :
    ∃ r ∈ regions s, acceptsParameters weights r = true := by
  obtain ⟨p,hp⟩ := nonempty_frontier_selects s valid weights nonempty
  have selected := frontier_selected_optimal s valid weights p hp
  exact ⟨region s p, List.mem_map.mpr ⟨p,selected.1,rfl⟩,
    (region_exact s weights p).mpr selected.2⟩

theorem selected_region_accepts (s : State) (valid : Valid s) (weights : Nat → Nat)
    (p : Point) (hp : selectFrontier s weights = some p) :
    region s p ∈ regions s ∧ acceptsParameters weights (region s p) = true := by
  have selected := frontier_selected_optimal s valid weights p hp
  exact ⟨List.mem_map.mpr ⟨p,selected.1,rfl⟩, (region_exact s weights p).mpr selected.2⟩

theorem region_storage (s : State) (p : Point) :
    (region s p).inequalities.length = s.catalogue.length ∧
      ∀ row ∈ (region s p).inequalities, row.terms.length = s.axes.length := by
  constructor
  · simp [region]
  · intro row hr
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hr
    simp [coefficients]

def appendBatches (s : State) : List (List Point) → State
  | [] => s
  | added :: rest => appendBatches (reconcile s s.axes (s.catalogue ++ added)) rest

def freshBatches (s : State) : List (List Point) → Prop
  | [] => True
  | added :: rest => (∀ p ∈ added, p ∉ s.catalogue) ∧
      freshBatches (reconcile s s.axes (s.catalogue ++ added)) rest

def appendWork (s : State) : List (List Point) → Nat
  | [] => 0
  | added :: rest => comparisonsNeeded s s.axes (s.catalogue ++ added) +
      appendWork (reconcile s s.axes (s.catalogue ++ added)) rest

theorem append_work_telescopes (s : State) (batches : List (List Point))
    (fresh : freshBatches s batches) :
    appendWork s batches + s.catalogue.length ^ 2 =
      (appendBatches s batches).catalogue.length ^ 2 := by
  induction batches generalizing s with
  | nil => simp [appendBatches, appendWork]
  | cons added rest ih =>
    have hi := ih (reconcile s s.axes (s.catalogue ++ added)) fresh.2
    have hd := comparison_partition s s.axes (s.catalogue ++ added)
    rw [reused_square, append_retained s added fresh.1] at hd
    have hn : (s.catalogue ++ added).length * (s.catalogue ++ added).length =
        (s.catalogue ++ added).length ^ 2 := by simp [Nat.pow_succ]
    rw [hn] at hd
    change appendWork (reconcile s s.axes (s.catalogue ++ added)) rest +
      (s.catalogue ++ added).length ^ 2 = _ at hi
    change comparisonsNeeded s s.axes (s.catalogue ++ added) +
      appendWork (reconcile s s.axes (s.catalogue ++ added)) rest +
      s.catalogue.length ^ 2 = _
    change _ = (appendBatches (reconcile s s.axes (s.catalogue ++ added)) rest).catalogue.length ^ 2
    omega

private def leftPoint : Point := ⟨0, [0,2]⟩
private def middlePoint : Point := ⟨1, [1,1]⟩
private def rightPoint : Point := ⟨2, [2,0]⟩
private def dominatedPoint : Point := ⟨3, [3,3]⟩
private def exampleState : State := build [0,1]
  [leftPoint,middlePoint,rightPoint,dominatedPoint]

private def unsupportedMiddle : Point := ⟨1,[2,2]⟩
private def unsupportedState : State := build [0,1] [⟨0,[0,3]⟩,unsupportedMiddle,⟨2,[3,0]⟩]

theorem unsupported_region_zero_only (weights : Nat → Nat) :
    acceptsParameters weights (region unsupportedState unsupportedMiddle) = true ↔
      weights 0 = 0 ∧ weights 1 = 0 := by
  rw [region_exact]
  simp [unsupportedState, unsupportedMiddle, build, weighted, cost]
  omega

#guard (frontier exampleState).map Point.id == [0,1,2]
#guard (selectFrontier exampleState (fun i => if i = 0 then 1 else 0)).map Point.id == some 0
#guard (selectFrontier exampleState (fun i => if i = 1 then 1 else 0)).map Point.id == some 2
#guard (selectFrontier exampleState (fun _ => 0)).map Point.id == some 0
#guard comparisonsNeeded exampleState [0,1] exampleState.catalogue == 0
#guard comparisonsNeeded exampleState [0,1] [middlePoint,rightPoint] == 0
#guard comparisonsNeeded exampleState [0,1]
  [leftPoint,middlePoint,rightPoint,⟨3,[0,0]⟩] == 7
#guard (frontier (reconcile exampleState [0,1]
  [leftPoint,middlePoint,rightPoint,⟨3,[0,0]⟩])).map Point.id == [3]
#guard (frontier (reconcile (build [0,1] [⟨0,[0,0]⟩,⟨1,[1,1]⟩])
  [0,1] [⟨1,[1,1]⟩])).map Point.id == [1]
#guard (frontier (build [0,1] [⟨0,[0,0]⟩,⟨1,[0,0]⟩])).map Point.id == [0,1]
#guard (selectFrontier (build [0,1] [⟨0,[-3,1]⟩,⟨1,[-1,-1]⟩])
  (fun _ => 0)).map Point.id == some 0
#guard (frontier unsupportedState).map Point.id == [0,1,2]

end ParametricPareto
