import Incremental

/- Exact finite enumeration costs. These equalities do not assert that every
   update touches every subset, or that an explicit exponential result has a
   polynomial representation. -/

namespace HmaIncremental

open Hma

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]

theorem sublists_length {α : Type} (xs : List α) : (sublists xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [sublists, List.length_append, List.length_map, List.length_cons, ih,
      Nat.pow_succ]
    omega

theorem sublists_member_subset {α : Type} (xs ys : List α) (h : ys ∈ sublists xs) :
    ∀ a ∈ ys, a ∈ xs := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := by simpa [sublists] using h
    simp [hy]
  | cons x xs ih =>
    rcases List.mem_append.mp h with h | h
    · intro a ha
      exact List.mem_cons_of_mem x (ih ys h a ha)
    · obtain ⟨zs, hz, rfl⟩ := List.mem_map.mp h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · simp
      · exact List.mem_cons_of_mem x (ih zs hz a ha)

theorem sublists_nodup {α : Type} (xs : List α) (h : xs.Nodup) : (sublists xs).Nodup := by
  induction xs with
  | nil => simp [sublists]
  | cons x xs ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp h
    have hi := ih hn
    apply List.pairwise_append.mpr
    refine ⟨hi, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact hi.imp (fun {_ _} hab heq => hab (List.cons.inj heq).2)
    · intro ys hy zs hz heq
      obtain ⟨ws, hw, hwz⟩ := List.mem_map.mp hz
      rw [← hwz] at heq
      have hx : x ∈ ys := by rw [heq]; simp
      exact hnot (sublists_member_subset xs ys hy x hx)

theorem sublists_mem_ext {α : Type} (xs : List α) (h : xs.Nodup)
    (ys zs : List α) (hy : ys ∈ sublists xs) (hz : zs ∈ sublists xs)
    (hext : ∀ a, a ∈ ys ↔ a ∈ zs) : ys = zs := by
  induction xs generalizing ys zs with
  | nil =>
    have hy' : ys = [] := by simpa [sublists] using hy
    have hz' : zs = [] := by simpa [sublists] using hz
    exact hy'.trans hz'.symm
  | cons x xs ih =>
    obtain ⟨hnot, hn⟩ := List.nodup_cons.mp h
    rcases List.mem_append.mp hy with hy | hy <;>
      rcases List.mem_append.mp hz with hz | hz
    · exact ih hn ys zs hy hz hext
    · obtain ⟨ws, hw, hwz⟩ := List.mem_map.mp hz
      have hx : x ∈ zs := by rw [← hwz]; simp
      exact False.elim (hnot (sublists_member_subset xs ys hy x ((hext x).mpr hx)))
    · obtain ⟨ws, hw, hwy⟩ := List.mem_map.mp hy
      have hx : x ∈ ys := by rw [← hwy]; simp
      exact False.elim (hnot (sublists_member_subset xs zs hz x ((hext x).mp hx)))
    · obtain ⟨ys', hy', hyy⟩ := List.mem_map.mp hy
      obtain ⟨zs', hz', hzz⟩ := List.mem_map.mp hz
      rw [← hyy, ← hzz]
      apply congrArg (x :: ·)
      apply ih hn ys' zs' hy' hz'
      intro a
      have hm := hext a
      rw [← hyy, ← hzz] at hm
      constructor
      · intro ha
        rcases List.mem_cons.mp (hm.mp (List.mem_cons_of_mem x ha)) with heq | hmem
        · subst a
          exact False.elim (hnot (sublists_member_subset xs ys' hy' x ha))
        · exact hmem

      · intro ha
        rcases List.mem_cons.mp (hm.mpr (List.mem_cons_of_mem x ha)) with heq | hmem
        · subst a
          exact False.elim (hnot (sublists_member_subset xs zs' hz' x ha))
        · exact hmem

theorem subset_functions_nodup (I : Inst A V B W) :
    ((sublists I.axes).map HmaCheck.axisSet).Nodup := by
  apply List.pairwise_map.mpr
  apply (sublists_nodup I.axes I.axesnodup).imp_of_mem
  intro left right hleft hright hne heq
  apply hne
  apply sublists_mem_ext I.axes I.axesnodup left right hleft hright
  intro a
  have ha := congrArg (fun S => S a) heq
  exact decide_eq_decide.mp ha

def cumulativePairs : Nat → Nat
  | 0 => 0
  | n + 1 => cumulativePairs n + n

theorem pairs_length {α : Type} (xs : List α) : (pairs xs).length = cumulativePairs xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [pairs, List.length_append, List.length_map, List.length_cons, ih, cumulativePairs]
    omega

theorem cumulativePairs_twice (n : Nat) : 2 * cumulativePairs n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ k =>
      simp only [cumulativePairs, Nat.succ_eq_add_one] at *
      simp only [Nat.add_sub_cancel] at *
      simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul] at *
      omega

theorem pair_delta_exact {α : Type} (x : α) (xs : List α) :
    (pairs (x :: xs)).length - (pairs xs).length = xs.length := by
  simp only [pairs, List.length_append, List.length_map]
  omega

def freeAxes {α : Type} (axes : List α) (required : α → Bool) : List α :=
  axes.filter (fun a => !(required a))

def cone {α : Type} (axes : List α) (required : α → Bool) : List (List α) :=
  (sublists (freeAxes axes required)).map (fun optional => axes.filter required ++ optional)

theorem filter_partition_length {α : Type} (axes : List α) (p : α → Bool) :
    (axes.filter p).length + (freeAxes axes p).length = axes.length := by
  induction axes with
  | nil => rfl
  | cons a xs ih =>
    cases hp : p a <;> simp [freeAxes, hp] at * <;> omega

theorem cone_length {α : Type} (axes : List α) (required : α → Bool) :
    (cone axes required).length = 2 ^ (axes.length - (axes.filter required).length) := by
  simp only [cone, List.length_map, sublists_length]
  have h := filter_partition_length axes required
  congr 1
  omega

theorem cone_nodup {α : Type} (axes : List α) (required : α → Bool) (h : axes.Nodup) :
    (cone axes required).Nodup := by
  have hf : (freeAxes axes required).Nodup := List.Sublist.nodup (List.filter_sublist) h
  apply List.pairwise_map.mpr
  exact (sublists_nodup _ hf).imp (fun {_ _} hab heq => hab (List.append_cancel_left heq))

theorem cone_covers (I : Inst A V B W) (required S : A → Bool)
    (h : ∀ a, required a = true → S a = true) :
    ∃ axes ∈ cone I.axes required, HmaCheck.axisSet axes = S := by
  refine ⟨I.axes.filter required ++ (freeAxes I.axes required).filter S,
    List.mem_map_of_mem (Hma.filtermemsublists S (freeAxes I.axes required)), ?_⟩
  funext a
  unfold HmaCheck.axisSet
  have ha := I.axescomplete a
  have hpoint := h a
  cases hr : required a <;> cases hs : S a <;>
    simp [freeAxes, ha, hr, hs] at *

theorem cone_sound (I : Inst A V B W) (required : A → Bool) (selected : List A)
    (h : selected ∈ cone I.axes required) :
    ∀ a, required a = true → HmaCheck.axisSet selected a = true := by
  obtain ⟨optional, _, heq⟩ := List.mem_map.mp h
  intro a ha
  rw [← heq]
  simp only [HmaCheck.axisSet, decide_eq_true_eq]
  exact List.mem_append_left _ (List.mem_filter.mpr ⟨I.axescomplete a, ha⟩)

/- Independent binary choices exhibit the combinatorial expansion without
   materializing a Cartesian product of all row values. The Hma instance
   adapter for the paired-axis examples is checked separately in the gate. -/

def binaryChoices : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (binaryChoices n).map (false :: ·) ++ (binaryChoices n).map (true :: ·)

theorem binaryChoices_length (n : Nat) : (binaryChoices n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [binaryChoices, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem binaryChoices_nodup (n : Nat) : (binaryChoices n).Nodup := by
  induction n with
  | zero => simp [binaryChoices]
  | succ n ih =>
    apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact ih.imp (fun {_ _} hab heq => hab (List.cons.inj heq).2)
    · apply List.pairwise_map.mpr
      exact ih.imp (fun {_ _} hab heq => hab (List.cons.inj heq).2)
    · intro xs hx ys hy heq
      obtain ⟨as, _, ha⟩ := List.mem_map.mp hx
      obtain ⟨bs, _, hb⟩ := List.mem_map.mp hy
      rw [← ha, ← hb] at heq
      simp at heq

theorem binaryChoices_member_length (n : Nat) (xs : List Bool) (h : xs ∈ binaryChoices n) :
    xs.length = n := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := by simpa only [binaryChoices, List.mem_singleton] using h
    simp [hx]
  | succ n ih =>
    rcases List.mem_append.mp h with h | h <;>
      obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp h <;>
      simp only [List.length_cons, ih ys hy]

theorem binaryChoices_complete (xs : List Bool) : xs ∈ binaryChoices xs.length := by
  induction xs with
  | nil => simp [binaryChoices]
  | cons x xs ih =>
    cases x
    · exact List.mem_append_left _ (List.mem_map_of_mem ih)
    · exact List.mem_append_right _ (List.mem_map_of_mem ih)

end HmaIncremental
