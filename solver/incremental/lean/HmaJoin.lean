/-
  System 3's cone rule over the highest minimal axis repo's own
  definitions (Hma.lean at b12fdb2, imported, unchanged).

  Appending contract rows N to an instance I gives the instance
  joinI I N. Liveness in joinI is liveness in I or a witness pair that
  involves a new row (join_live). The agreement condition of a pair is
  its difference set lying inside S (agreeoff_iff_diff), so S depends
  only on pairs whose difference set is inside S. If no pair involving
  a new row is a witness for component b in S, b's liveness in S is
  unchanged (scoped_live); if that holds for every component, S's live
  list, lambda and mu are unchanged (scoped_rho): S need not be
  re-measured.
-/
import Hma

namespace HmaJoin
open Hma

variable {A V B W : Type} [DecidableEq A] [DecidableEq B] [DecidableEq V] [DecidableEq W]

/-- The instance with rows N appended to its contract. -/
def joinI (I : Inst A V B W) (N : List (A → V)) : Inst A V B W :=
  { I with contract := I.contract ++ N }

/-- A witness pair for b in S: agreeing off S, differing on b. -/
abbrev witness (I : Inst A V B W) (b : B) (S : A → Bool) (x x' : A → V) : Prop :=
  agreeoff I x x' S ∧ I.beh x b ≠ I.beh x' b

/-- The difference-set reading: a pair agrees off S exactly when every
    axis on which it differs is in S. -/
theorem agreeoff_iff_diff (I : Inst A V B W) (x x' : A → V) (S : A → Bool) :
    agreeoff I x x' S ↔ ∀ a ∈ I.axes, x a ≠ x' a → S a = true := by
  constructor
  · intro h a ha hne
    cases hS : S a
    · exact absurd (h a ha hS) hne
    · rfl
  · intro h a ha hS
    by_cases he : x a = x' a
    · exact he
    · have := h a ha he
      rw [hS] at this
      exact absurd this (by decide)

/-- Join rule: liveness after the join is liveness before, or a witness
    pair with at least one new row. -/
theorem join_live (I : Inst A V B W) (N : List (A → V)) (b : B) (S : A → Bool) :
    live (joinI I N) b S ↔
      live I b S ∨
      ∃ x ∈ I.contract ++ N, ∃ x' ∈ I.contract ++ N,
        (x ∈ N ∨ x' ∈ N) ∧ witness I b S x x' := by
  constructor
  · rintro ⟨x, hx, x', hx', hw⟩
    by_cases hxo : x ∈ I.contract
    · by_cases hxo' : x' ∈ I.contract
      · exact Or.inl ⟨x, hxo, x', hxo', hw⟩
      · have : x' ∈ N := by
          rcases List.mem_append.mp hx' with h | h
          · exact absurd h hxo'
          · exact h
        exact Or.inr ⟨x, hx, x', hx', Or.inr this, hw⟩
    · have : x ∈ N := by
        rcases List.mem_append.mp hx with h | h
        · exact absurd h hxo
        · exact h
      exact Or.inr ⟨x, hx, x', hx', Or.inl this, hw⟩
  · rintro (⟨x, hx, x', hx', hw⟩ | ⟨x, hx, x', hx', _, hw⟩)
    · exact ⟨x, List.mem_append_left _ hx, x', List.mem_append_left _ hx', hw⟩
    · exact ⟨x, hx, x', hx', hw⟩

/-- Scope: if no pair involving a new row witnesses b in S, b's
    liveness in S is unchanged by the join. -/
theorem scoped_live (I : Inst A V B W) (N : List (A → V)) (b : B) (S : A → Bool)
    (h : ∀ x ∈ I.contract ++ N, ∀ x' ∈ I.contract ++ N,
      (x ∈ N ∨ x' ∈ N) → ¬ witness I b S x x') :
    live (joinI I N) b S ↔ live I b S := by
  rw [join_live]
  constructor
  · rintro (h1 | ⟨x, hx, x', hx', hn, hw⟩)
    · exact h1
    · exact absurd hw (h x hx x' hx' hn)
  · exact Or.inl

/-- Superset rule: a witness for S is a witness for every superset of S
    (the cone of a difference set is every subset containing it). -/
theorem witness_mono (I : Inst A V B W) {S T : A → Bool} (hST : subset I S T)
    {b : B} {x x' : A → V} (hw : witness I b S x x') : witness I b T x x' := by
  refine ⟨?_, hw.2⟩
  intro a ha hT
  cases hS : S a
  · exact hw.1 a ha hS
  · exact absurd (hST a ha hS) (by rw [hT]; decide)

/-- Scoped re-measure: if every component keeps its liveness in S, the
    live list, lambda and mu of S are the carried ones. -/
theorem scoped_rho (I : Inst A V B W) (N : List (A → V)) (S : A → Bool)
    (h : ∀ b, live (joinI I N) b S ↔ live I b S) :
    livelist (joinI I N) S = livelist I S ∧
      lam (joinI I N) S = lam I S ∧ mu (joinI I N) S = mu I S := by
  have hl : livelist (joinI I N) S = livelist I S := by
    unfold livelist
    apply filtercongr
    intro b _
    exact decide_eq_decide.mpr (h b)
  refine ⟨hl, ?_, ?_⟩
  · unfold lam; rw [hl]
  · unfold mu
    congr 1
    apply List.map_congr_left
    intro e _
    have : engaged (joinI I N) S e ↔ engaged I S e := by
      unfold engaged
      rw [hl]
      rfl
    by_cases he : engaged I S e
    · rw [if_pos (this.mpr he), if_pos he]; rfl
    · rw [if_neg (fun h' => he (this.mp h')), if_neg he]

end HmaJoin
