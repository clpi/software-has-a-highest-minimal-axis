import Hma

/- Finite executable views of the existing predicates. These lemmas connect
   the checker's cached table to Hma.minimal and Hma.highest. They do not prove
   an external solver or its input decoder correct. -/

namespace HmaCheck

open Hma

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]

def axisSet (l : List A) : A → Bool := fun a => decide (a ∈ l)

structure Snapshot (B : Type) where
  live : List B
  edges : List (List B)
  measure : Nat × Nat
  deriving DecidableEq, Repr

def activeEdge (edges : List (List B)) (live : List B) (e : List B) : Bool :=
  decide (e ∈ edges ∧ 2 ≤ e.length ∧ ∀ b ∈ e, b ∈ live)

def snapshot (I : Inst A V B W) (S : A → Bool) : Snapshot B :=
  let live := livelist I S
  let active := activeEdge I.edges live
  { live := live
    edges := I.edges.filter active
    measure := ((I.edges.map (fun e => if active e then I.weight e else 0)).sum,
      live.length) }

theorem snapshotLive (I : Inst A V B W) (S : A → Bool) :
    (snapshot I S).live = livelist I S := rfl

theorem snapshotEdges (I : Inst A V B W) (S : A → Bool) :
    (snapshot I S).edges = engagedlist I S := by
  unfold snapshot engagedlist
  apply filtercongr
  intro e _
  unfold activeEdge
  rw [decide_eq_decide]

theorem snapshotMeasure (I : Inst A V B W) (S : A → Bool) :
    (snapshot I S).measure = rho I S := by
  simp only [snapshot, activeEdge, rho, mu, lam, engaged, decide_eq_true_eq]

def table (I : Inst A V B W) : List (List A × Snapshot B) :=
  (sublists I.axes).map (fun l => (l, snapshot I (axisSet l)))

abbrev tableMinimal (I : Inst A V B W) (rows : List (List A × Snapshot B))
    (fullmu : Nat) (l : List A) (value : Snapshot B) : Prop :=
  value.measure.1 = fullmu ∧
    ∀ row ∈ rows, proper I (axisSet row.1) (axisSet l) → row.2.measure.1 ≠ fullmu

abbrev tableHighest (I : Inst A V B W) (rows : List (List A × Snapshot B))
    (fullmu : Nat) (l : List A) (value : Snapshot B) : Prop :=
  tableMinimal I rows fullmu l value ∧
    ∀ row ∈ rows, tableMinimal I rows fullmu row.1 row.2 →
      row.2.measure.1 < value.measure.1 ∨
        (row.2.measure.1 = value.measure.1 ∧ row.2.measure.2 ≤ value.measure.2)

theorem tableMinimalIff (I : Inst A V B W) (l : List A) :
    tableMinimal I (table I) (mu I allaxes) l (snapshot I (axisSet l)) ↔
      minimal I (axisSet l) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [snapshotMeasure, rho] using h.1
    · intro T hp
      obtain ⟨t, ht, hT⟩ := subsetrep I T
      change T = axisSet t at hT
      subst T
      have hh := h.2 (t, snapshot I (axisSet t)) (List.mem_map_of_mem ht) hp
      simpa only [snapshotMeasure, rho] using hh
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [snapshotMeasure, rho] using h.1
    · intro row hr hp
      obtain ⟨t, _, ht⟩ := List.mem_map.mp hr
      subst row
      simpa only [snapshotMeasure, rho] using h.2 (axisSet t) hp

theorem tableHighestIff (I : Inst A V B W) (l : List A) :
    tableHighest I (table I) (mu I allaxes) l (snapshot I (axisSet l)) ↔
      highest I (axisSet l) := by
  constructor
  · intro h
    refine ⟨(tableMinimalIff I l).1 h.1, ?_⟩
    intro T hmin
    obtain ⟨t, ht, hT⟩ := subsetrep I T
    change T = axisSet t at hT
    subst T
    have hh := h.2 (t, snapshot I (axisSet t)) (List.mem_map_of_mem ht)
      ((tableMinimalIff I t).2 hmin)
    simpa only [snapshotMeasure, rho] using hh
  · intro h
    refine ⟨(tableMinimalIff I l).2 h.1, ?_⟩
    intro row hr hm
    obtain ⟨t, _, ht⟩ := List.mem_map.mp hr
    subst row
    have hh := h.2 (axisSet t) ((tableMinimalIff I t).1 hm)
    simpa only [snapshotMeasure, rho] using hh

end HmaCheck
