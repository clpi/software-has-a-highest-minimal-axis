/-
  The standing controls: Instances X, D, and E of the spec,
  as concrete checks that the definitions compute the
  claimed answers. Every computational check is by kernel
  decision only.
-/

import Hma

open Hma

namespace Ctl

/-- An axis set of the three axis instances, named by the
    list of its axes. -/
def subx (l : List (Fin 3)) : Fin 3 → Bool := fun a => decide (a ∈ l)

/-- The eight axis sets of a three axis instance. -/
theorem sublists012 (l : List (Fin 3)) (h : l ∈ sublists [0, 1, 2]) :
    l = [] ∨ l = [2] ∨ l = [1] ∨ l = [1, 2] ∨ l = [0] ∨ l = [0, 2] ∨
      l = [0, 1] ∨ l = [0, 1, 2] := by
  have h3 : l ∈ [[], [2], [1], [1, 2], [0], [0, 2], [0, 1], [0, 1, 2]] := h
  simp only [List.mem_cons, List.mem_singleton] at h3
  rcases h3 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h3
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact (List.not_mem_nil h3).elim

/- Instance X: highest is not vacuous. Axes a, b, c read as
   0, 1, 2; components p, q, r, s read as 0, 1, 2, 3. -/

def instx : Inst (Fin 3) Bool (Fin 4) Bool where
  axes := [0, 1, 2]
  axesnodup := by decide
  axescomplete := by decide
  comps := [0, 1, 2, 3]
  contract := [false, true].flatMap (fun u => [false, true].flatMap (fun v =>
    [false, true].map (fun w => (fun a => if a = 0 then u else if a = 1 then v else w))))
  beh := fun x b => if b = 0 then (x 0 != x 2) else if b = 1 then (x 0 != x 2)
    else if b = 2 then x 1 else x 0
  edges := [[0, 1]]
  weight := fun _ => 1
  weightpos := by
    intro e he _
    simp at he
    subst he
    decide

theorem xvalues :
    mu instx (subx [0]) = 1 ∧ lam instx (subx [0]) = 3 ∧
    mu instx (subx [2]) = 1 ∧ lam instx (subx [2]) = 2 ∧
    mu instx (allaxes (A := Fin 3)) = 1 ∧ mu instx (noaxes (A := Fin 3)) = 0 ∧
    rho instx (subx [0]) = (1, 3) ∧ rho instx (subx [2]) = (1, 2) := by
  decide

theorem xlives :
    livelist instx (allaxes (A := Fin 3)) = [0, 1, 2, 3] ∧
    livelist instx (subx [0]) = [0, 1, 3] ∧
    livelist instx (subx [2]) = [0, 1] ∧
    engagedlist instx (subx [0]) = [[0, 1]] ∧
    engagedlist instx (subx [2]) = [[0, 1]] := by
  decide

theorem xaminimal : minimal instx (subx [0]) := by
  refine ⟨by decide, ?_⟩
  intro T hp
  obtain ⟨l, hl, hT⟩ := subsetrep instx T
  rw [hT] at hp ⊢
  have hl2 := sublists012 l hl
  rcases hl2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hp <;> decide

theorem xcminimal : minimal instx (subx [2]) := by
  refine ⟨by decide, ?_⟩
  intro T hp
  obtain ⟨l, hl, hT⟩ := subsetrep instx T
  rw [hT] at hp ⊢
  have hl2 := sublists012 l hl
  rcases hl2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hp <;> decide

theorem xahighest : highest instx (subx [0]) := by
  refine ⟨xaminimal, ?_⟩
  intro T hminT
  obtain ⟨l, hl, hT⟩ := subsetrep instx T
  rw [hT] at hminT ⊢
  have hl2 := sublists012 l hl
  rcases hl2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | decide
      | exact False.elim (hminT.2 (subx [0]) (by decide) (by decide))

/-- The corrected dead axis fact in Instance X: axis c is
    emergent-dead, and the singleton of c is nevertheless
    minimal sufficient. Deadness therefore does not keep an
    axis out of every minimal sufficient set. -/
theorem xcdeadandminimal : dead instx 2 ∧ minimal instx (subx [2]) :=
  ⟨by decide, xcminimal⟩

theorem xcnothighest : ¬ highest instx (subx [2]) := by
  intro h
  exact absurd (h.2 (subx [0]) xaminimal) (by decide)

/-- A dead axis does make the full axis set non-minimal:
    the corrected corollary, checked in Instance X. -/
theorem xdeadnotminimal : ¬ minimal instx (allaxes (A := Fin 3)) :=
  deadnotminimal instx (a := 2) (by decide)

/- Instance D: the degenerate whole set case. The contract
   is the two constant configurations; components p and q
   read axes a and b. -/

def instd : Inst (Fin 3) Bool (Fin 2) Bool where
  axes := [0, 1, 2]
  axesnodup := by decide
  axescomplete := by decide
  comps := [0, 1]
  contract := [fun _ => false, fun _ => true]
  beh := fun x b => if b = 0 then x 0 else x 1
  edges := [[0, 1]]
  weight := fun _ => 1
  weightpos := by
    intro e he _
    simp at he
    subst he
    decide

theorem dvalues :
    mu instd (allaxes (A := Fin 3)) = 1 ∧
    mu instd (subx [0]) = 0 ∧ mu instd (subx [0, 1]) = 0 ∧
    livelist instd (allaxes (A := Fin 3)) = [0, 1] ∧
    livelist instd (subx [0, 1]) = [] := by
  decide

theorem dnoproper :
    ∀ T, proper instd T (allaxes (A := Fin 3)) → ¬ sufficient instd T := by
  intro T hp
  obtain ⟨l, hl, hT⟩ := subsetrep instd T
  rw [hT] at hp ⊢
  have hl2 := sublists012 l hl
  rcases hl2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    revert hp <;> decide

theorem danswer :
    ∀ S, highest instd S → S = allaxes (A := Fin 3) :=
  (degenerate instd).1 dnoproper

theorem dfullhighest : highest instd (allaxes (A := Fin 3)) := by
  obtain ⟨S, hS⟩ := highestexists instd
  have hSeq := danswer S hS
  subst hSeq
  exact hS

/- Instance E: the empty contract and the singleton
   contract. No variation exists in either; the empty axis
   set is the unique highest minimal vector. -/

def inste1 : Inst (Fin 3) Bool (Fin 2) Bool where
  axes := [0, 1, 2]
  axesnodup := by decide
  axescomplete := by decide
  comps := [0, 1]
  contract := []
  beh := fun x b => if b = 0 then x 0 else x 1
  edges := [[0, 1]]
  weight := fun _ => 1
  weightpos := by
    intro e he _
    simp at he
    subst he
    decide

def inste2 : Inst (Fin 3) Bool (Fin 2) Bool where
  axes := [0, 1, 2]
  axesnodup := by decide
  axescomplete := by decide
  comps := [0, 1]
  contract := [fun _ => false]
  beh := fun x b => if b = 0 then x 0 else x 1
  edges := [[0, 1]]
  weight := fun _ => 1
  weightpos := by
    intro e he _
    simp at he
    subst he
    decide

theorem evalues :
    mu inste1 (allaxes (A := Fin 3)) = 0 ∧ mu inste2 (subx [0]) = 0 ∧
    livelist inste1 (allaxes (A := Fin 3)) = [] ∧
    livelist inste2 (allaxes (A := Fin 3)) = [] := by
  decide

theorem eonehighest :
    highest inste1 (noaxes (A := Fin 3)) ∧
      ∀ S, highest inste1 S → S = noaxes (A := Fin 3) :=
  emptyoronehighest inste1 (by
    intro x _ hx
    exact (List.not_mem_nil
      (show x ∈ ([] : List (Fin 3 → Bool)) from hx)).elim)

theorem etwohighest :
    highest inste2 (noaxes (A := Fin 3)) ∧
      ∀ S, highest inste2 S → S = noaxes (A := Fin 3) :=
  emptyoronehighest inste2 (by
    intro x y hx hy
    have hx2 : x ∈ [(fun _ => false : Fin 3 → Bool)] := hx
    have hy2 : y ∈ [(fun _ => false : Fin 3 → Bool)] := hy
    simp only [List.mem_singleton] at hx2 hy2
    rw [hx2, hy2])

end Ctl
