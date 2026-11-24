import CertifiedReplay
import ParametricPareto

namespace HmaPareto

open Hma HmaCheck HmaCertified

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]

def qualifiedRows (output : HmaReplay.Output (A := A) (V := V) (B := B) (W := W) I) :
    List (Classified A B) := output.value.subsets.filter (fun r => r.minimal)

def profile (resource : A → Int) (r : Classified A B) : List Int :=
  [(r.axes.length : Int), -(r.value.measure.2 : Int), (r.axes.map resource).sum]

def point (idOf : List A → Nat) (resource : A → Int) (r : Classified A B) :
    ParametricPareto.Point := ⟨idOf r.axes, profile resource r⟩

def candidates (output : HmaReplay.Output (A := A) (V := V) (B := B) (W := W) I)
    (idOf : List A → Nat) (resource : A → Int) : List ParametricPareto.Point :=
  (qualifiedRows output).map (point idOf resource)

def idealProfile (I : Inst A V B W) (resource : A → Int) (axes : List A) : List Int :=
  [(axes.length : Int), -(lam I (axisSet axes) : Int), (axes.map resource).sum]

def idealPoint (I : Inst A V B W) (idOf : List A → Nat) (resource : A → Int)
    (axes : List A) : ParametricPareto.Point :=
  ⟨idOf axes, idealProfile I resource axes⟩

theorem qualifiedRows_exact (I : Inst A V B W) (output : HmaReplay.Output I)
    (r : Classified A B) :
    r ∈ qualifiedRows output ↔ r ∈ output.value.subsets ∧ Hma.minimal I (axisSet r.axes) := by
  simp only [qualifiedRows, List.mem_filter]
  constructor
  · rintro ⟨hr,hm⟩
    exact ⟨hr, ((output.correct.subsets r hr).2.2.2.1).mp hm⟩
  · rintro ⟨hr,hm⟩
    exact ⟨hr, ((output.correct.subsets r hr).2.2.2.1).mpr hm⟩

theorem qualifiedRows_cover (I : Inst A V B W) (output : HmaReplay.Output I)
    (axes : List A) (hc : axes ∈ sublists I.axes) (hm : Hma.minimal I (axisSet axes)) :
    ∃ r ∈ qualifiedRows output, r.axes = axes := by
  obtain ⟨r,hr,he⟩ := output.correct.coverage (axisSet axes)
  have hsame : r.axes = axes := by
    apply HmaIncremental.sublists_mem_ext I.axes I.axesnodup r.axes axes
      (output.correct.subsets r hr).1 hc
    intro a
    have ha := congrArg (fun S => S a) he
    exact decide_eq_decide.mp ha
  refine ⟨r, (qualifiedRows_exact I output r).mpr ⟨hr, ?_⟩, hsame⟩
  rw [hsame]
  exact hm

theorem point_exact (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) (r : Classified A B)
    (hr : r ∈ qualifiedRows output) :
    point idOf resource r = idealPoint I idOf resource r.axes := by
  have hs := (qualifiedRows_exact I output r).mp hr
  have hv := (output.correct.subsets r hs.1).2.1
  unfold point idealPoint profile idealProfile
  rw [hv, snapshotMeasure]
  rfl

theorem candidates_exact (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) (p : ParametricPareto.Point) :
    p ∈ candidates output idOf resource ↔
      ∃ axes, axes ∈ sublists I.axes ∧ Hma.minimal I (axisSet axes) ∧
        p = idealPoint I idOf resource axes := by
  constructor
  · intro hp
    obtain ⟨r,hr,hp⟩ := List.mem_map.mp hp
    have hs := (qualifiedRows_exact I output r).mp hr
    exact ⟨r.axes, (output.correct.subsets r hs.1).1, hs.2,
      hp.symm.trans (point_exact I output idOf resource r hr)⟩
  · rintro ⟨axes,hc,hm,rfl⟩
    obtain ⟨r,hr,he⟩ := qualifiedRows_cover I output axes hc hm
    apply List.mem_map.mpr
    refine ⟨r,hr,?_⟩
    rw [point_exact I output idOf resource r hr, he]

def start (output : HmaReplay.Output (A := A) (V := V) (B := B) (W := W) I)
    (idOf : List A → Nat) (resource : A → Int) : ParametricPareto.Certified :=
  ParametricPareto.start [0,1,2] (candidates output idOf resource)

def advance (old : ParametricPareto.Certified)
    (output : HmaReplay.Output (A := A) (V := V) (B := B) (W := W) I)
    (idOf : List A → Nat) (resource : A → Int) : ParametricPareto.Certified :=
  ParametricPareto.advance old [0,1,2] (candidates output idOf resource)

def objective (I : Inst A V B W) (resource : A → Int) (weights : Nat → Nat)
    (axes : List A) : Int :=
  ParametricPareto.weighted [0,1,2] weights (idealPoint I (fun _ => 0) resource axes)

theorem objective_formula (I : Inst A V B W) (resource : A → Int) (weights : Nat → Nat)
    (axes : List A) : objective I resource weights axes =
      (weights 0 : Int) * (axes.length : Int) +
      (weights 1 : Int) * (-(lam I (axisSet axes) : Int)) +
      (weights 2 : Int) * (axes.map resource).sum := by
  simp [objective, ParametricPareto.weighted, ParametricPareto.cost,
    idealPoint, idealProfile, Int.add_assoc]

theorem ideal_weighted_objective (I : Inst A V B W) (idOf : List A → Nat)
    (resource : A → Int) (weights : Nat → Nat) (axes : List A) :
    ParametricPareto.weighted [0,1,2] weights (idealPoint I idOf resource axes) =
      objective I resource weights axes := rfl

theorem selected_hma_optimal (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) (weights : Nat → Nat)
    (p : ParametricPareto.Point)
    (h : ParametricPareto.selectFrontier (start output idOf resource).val weights = some p) :
    ∃ axes, axes ∈ sublists I.axes ∧ Hma.minimal I (axisSet axes) ∧
      p = idealPoint I idOf resource axes ∧
      (∀ other ∈ sublists I.axes, Hma.minimal I (axisSet other) →
        objective I resource weights axes ≤ objective I resource weights other) ∧
      (∀ other ∈ sublists I.axes, Hma.minimal I (axisSet other) →
        ParametricPareto.dominates [0,1,2]
          (idealPoint I idOf resource other) (idealPoint I idOf resource axes) = false) := by
  have hs := ParametricPareto.certified_selection (start output idOf resource) weights p h
  have hf := (ParametricPareto.certified_frontier (start output idOf resource) p).mp hs.1
  obtain ⟨axes,hc,hm,hp⟩ := (candidates_exact I output idOf resource p).mp hf.1
  refine ⟨axes,hc,hm,hp,?_,?_⟩
  · intro other ho hmin
    have hmem := (candidates_exact I output idOf resource _).mpr ⟨other,ho,hmin,rfl⟩
    have hh := hs.2 _ hmem
    rw [hp] at hh
    exact hh
  · intro other ho hmin
    have hmem := (candidates_exact I output idOf resource _).mpr ⟨other,ho,hmin,rfl⟩
    have hh := hf.2 _ hmem
    rw [hp] at hh
    exact hh

theorem advanced_hma_optimal (old : ParametricPareto.Certified)
    (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) (weights : Nat → Nat)
    (p : ParametricPareto.Point)
    (h : ParametricPareto.selectFrontier (advance old output idOf resource).val weights = some p) :
    ∃ axes, axes ∈ sublists I.axes ∧ Hma.minimal I (axisSet axes) ∧
      p = idealPoint I idOf resource axes ∧
      (∀ other ∈ sublists I.axes, Hma.minimal I (axisSet other) →
        objective I resource weights axes ≤ objective I resource weights other) := by
  have hs := ParametricPareto.certified_selection (advance old output idOf resource) weights p h
  have hf := (ParametricPareto.certified_frontier (advance old output idOf resource) p).mp hs.1
  obtain ⟨axes,hc,hm,hp⟩ := (candidates_exact I output idOf resource p).mp hf.1
  refine ⟨axes,hc,hm,hp,?_⟩
  intro other ho hmin
  have hmem := (candidates_exact I output idOf resource _).mpr ⟨other,ho,hmin,rfl⟩
  have hh := hs.2 _ hmem
  rw [hp] at hh
  exact hh

theorem advanced_frontier_exact (old : ParametricPareto.Certified)
    (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) (p : ParametricPareto.Point) :
    p ∈ ParametricPareto.frontier (advance old output idOf resource).val ↔
      p ∈ candidates output idOf resource ∧
      ∀ q ∈ candidates output idOf resource, ParametricPareto.dominates [0,1,2] q p = false :=
  ParametricPareto.certified_frontier _ p

theorem minimum_preserves_engaged (I : Inst A V B W) (axes : List A)
    (h : Hma.minimal I (axisSet axes)) :
    engagedlist I (axisSet axes) = engagedlist I allaxes :=
  engagedlistofsufficient I h.1

theorem candidates_nonempty (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) : candidates output idOf resource ≠ [] := by
  obtain ⟨S,hm⟩ := Hma.highestexists I
  obtain ⟨r,hr,he⟩ := output.correct.coverage S
  have hmin : Hma.minimal I (axisSet r.axes) := by rw [he]; exact hm.1
  have hc := (output.correct.subsets r hr).1
  have hmem := (candidates_exact I output idOf resource _).mpr ⟨r.axes,hc,hmin,rfl⟩
  intro hn
  rw [hn] at hmem
  simp at hmem

theorem start_selects (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) (weights : Nat → Nat) :
    ∃ p, ParametricPareto.selectFrontier (start output idOf resource).val weights = some p :=
  ParametricPareto.nonempty_frontier_selects _ (start output idOf resource).property weights
    (candidates_nonempty I output idOf resource)

theorem advance_selects (old : ParametricPareto.Certified)
    (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int) (weights : Nat → Nat) :
    ∃ p, ParametricPareto.selectFrontier (advance old output idOf resource).val weights = some p :=
  ParametricPareto.nonempty_frontier_selects _ (advance old output idOf resource).property weights
    (candidates_nonempty I output idOf resource)

theorem identity_preserved (I : Inst A V B W) (output : HmaReplay.Output I)
    (idOf : List A → Nat) (resource : A → Int)
    (injective : ∀ xs ∈ sublists I.axes, ∀ ys ∈ sublists I.axes, idOf xs = idOf ys → xs = ys)
    (r s : Classified A B) (hr : r ∈ qualifiedRows output) (hs : s ∈ qualifiedRows output)
    (same : (point idOf resource r).id = (point idOf resource s).id) : r.axes = s.axes := by
  exact injective r.axes (output.correct.subsets r ((qualifiedRows_exact I output r).mp hr).1).1
    s.axes (output.correct.subsets s ((qualifiedRows_exact I output s).mp hs).1).1 same

end HmaPareto
