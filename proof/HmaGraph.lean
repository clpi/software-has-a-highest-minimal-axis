import Hma
import HypergraphIncremental
import Incremental

/- HMA is a projection of the family's existing all-premise closure.
   Retained history is not a semantic field: reconstructed current rows,
   behavior and interaction declarations determine the graph. -/

namespace HmaGraph

open Hma HypergraphIncremental

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]

inductive Atom (A V B : Type) where
  | row : (A → V) → Atom A V B
  | axis : A → Atom A V B
  | live : B → Atom A V B
  | interaction : List B → Atom A V B

def differences (I : Inst A V B W) (x y : A → V) : List A :=
  I.axes.filter (fun a => decide (x a ≠ y a))

def pairPremises (I : Inst A V B W) (x y : A → V) : List (Atom A V B) :=
  [.row x, .row y] ++ (differences I x y).map Atom.axis

inductive Rule (I : Inst A V B W) : List (Atom A V B) → Atom A V B → Prop where
  | pair (x y : A → V) (b : B) (hx : x ∈ I.contract) (hy : y ∈ I.contract)
      (different : I.beh x b ≠ I.beh y b) :
      Rule I (pairPremises I x y) (.live b)
  | interaction (e : List B) (he : e ∈ I.edges) (hlen : 2 ≤ e.length)
      (components : ∀ b ∈ e, b ∈ I.comps) :
      Rule I (e.map Atom.live) (.interaction e)

def roots (I : Inst A V B W) (S : A → Bool) : Atom A V B → Prop
  | .row x => x ∈ I.contract
  | .axis a => S a = true
  | .live _ => False
  | .interaction _ => False

def graph (I : Inst A V B W) (S : A → Bool) : Hypergraph (Atom A V B) :=
  ⟨roots I S, Rule I⟩

theorem differences_selected (I : Inst A V B W) (S : A → Bool) (x y : A → V) :
    (∀ a ∈ differences I x y, S a = true) ↔ agreeoff I x y S := by
  constructor
  · intro h a ha hS
    by_cases equal : x a = y a
    · exact equal
    · have selected := h a (List.mem_filter.mpr ⟨ha, decide_eq_true equal⟩)
      rw [hS] at selected
      contradiction
  · intro h a ha
    obtain ⟨inAxes, different⟩ := List.mem_filter.mp ha
    have hd : x a ≠ y a := of_decide_eq_true different
    cases hS : S a with
    | false => exact False.elim (hd (h a inAxes hS))
    | true => rfl

def meaning (I : Inst A V B W) (S : A → Bool) : Atom A V B → Prop
  | .row x => x ∈ I.contract
  | .axis a => S a = true
  | .live b => Hma.live I b S
  | .interaction e => engaged I S e

theorem derives_meaning (I : Inst A V B W) (S : A → Bool) :
    ∀ a, derives (graph I S) a → meaning I S a := by
  apply Qualification.least
  · intro a h
    cases a with
    | row _ => exact h
    | axis _ => exact h
    | live _ => exact False.elim h
    | interaction _ => exact False.elim h
  · intro ps a rule hp
    cases rule with
    | pair x y b hx hy different =>
      refine ⟨x, hx, y, hy, ?_, different⟩
      apply (differences_selected I S x y).mp
      intro a ha
      exact hp (.axis a) (List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
    | interaction e he hlen components =>
      refine ⟨he, hlen, ?_⟩
      intro b hb
      apply List.mem_filter.mpr
      exact ⟨components b hb, decide_eq_true (hp (.live b) (List.mem_map.mpr ⟨b, hb, rfl⟩))⟩

theorem row_exact (I : Inst A V B W) (S : A → Bool) (x : A → V) :
    derives (graph I S) (.row x) ↔ x ∈ I.contract :=
  ⟨derives_meaning I S _, fun h => Qualification.Derives.root h⟩

theorem axis_exact (I : Inst A V B W) (S : A → Bool) (a : A) :
    derives (graph I S) (.axis a) ↔ S a = true :=
  ⟨derives_meaning I S _, fun h => Qualification.Derives.root h⟩

theorem live_exact (I : Inst A V B W) (S : A → Bool) (b : B) :
    derives (graph I S) (.live b) ↔ Hma.live I b S := by
  refine ⟨derives_meaning I S _, ?_⟩
  rintro ⟨x, hx, y, hy, agree, different⟩
  apply Qualification.Derives.step (Rule.pair x y b hx hy different)
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .root hx
    · exact .root hy
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact .root ((differences_selected I S x y).mpr agree a ha)

theorem interaction_exact (I : Inst A V B W) (S : A → Bool) (e : List B) :
    derives (graph I S) (.interaction e) ↔ engaged I S e := by
  refine ⟨derives_meaning I S _, ?_⟩
  rintro ⟨he, hlen, hp⟩
  apply Qualification.Derives.step
    (Rule.interaction e he hlen (fun b hb => (List.mem_filter.mp (hp b hb)).1))
  intro p h
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
  exact (live_exact I S b).mpr (of_decide_eq_true (List.mem_filter.mp (hp b hb)).2)

theorem supportCount_hypergraph_exact (I : Inst A V B W) (rows : List (A → V))
    (S : A → Bool) (b : B) :
    0 < HmaIncremental.supportCount I rows b S ↔
      derives (graph (HmaIncremental.withContract I rows) S) (.live b) :=
  (HmaIncremental.supportCount_positive_iff I rows b S).trans
    (live_exact (HmaIncremental.withContract I rows) S b).symm

theorem occupiedCount_hypergraph_exact (I : Inst A V B W) (rows : List (A → V))
    (S : A → Bool) (b : B) :
    0 < HmaIncremental.occupiedCount I rows b S ↔
      derives (graph (HmaIncremental.withContract I rows) S) (.live b) :=
  (HmaIncremental.occupiedCount_positive_iff I rows b S).trans
    (live_exact (HmaIncremental.withContract I rows) S b).symm

theorem incremental_live_exact (old new : Inst A V B W) (S T : A → Bool) (b : B) :
    incremental (graph old S) (graph new T) (.live b) ↔ Hma.live new b T :=
  (incremental_exact _ _ _).trans (live_exact new T b)

theorem incremental_interaction_exact (old new : Inst A V B W)
    (S T : A → Bool) (e : List B) :
    incremental (graph old S) (graph new T) (.interaction e) ↔ engaged new T e :=
  (incremental_exact _ _ _).trans (interaction_exact new T e)

/- Any current-state projector, including minimality and tie selection after
   closure, receives extensionally identical input. -/
theorem incremental_projection_exact {R : Type} (old new : Inst A V B W)
    (S T : A → Bool) (observe : (Atom A V B → Prop) → R) :
    observe (incremental (graph old S) (graph new T)) = observe (derives (graph new T)) := by
  have same : incremental (graph old S) (graph new T) = derives (graph new T) := by
    funext a
    exact propext (incremental_exact _ _ a)
  rw [same]

/- A checkpoint may replace all derivation history if it reconstructs these
   current semantic inputs. Contract order and repeated deliveries are absent
   from this condition; interaction multiplicity and order remain explicit. -/
structure Reconstructs (I J : Inst A V B W) : Prop where
  axes : I.axes = J.axes
  comps : I.comps = J.comps
  rows : ∀ x, x ∈ I.contract ↔ x ∈ J.contract
  behavior : ∀ x ∈ I.contract, ∀ b, I.beh x b = J.beh x b
  edges : I.edges = J.edges
  weights : ∀ e ∈ I.edges, I.weight e = J.weight e

theorem reconstructs_symm {I J : Inst A V B W} (h : Reconstructs I J) :
    Reconstructs J I where
  axes := h.axes.symm
  comps := h.comps.symm
  rows x := (h.rows x).symm
  behavior x hx b := (h.behavior x ((h.rows x).mpr hx) b).symm
  edges := h.edges.symm
  weights e he := (h.weights e (h.edges.symm ▸ he)).symm

theorem reconstructed_live {I J : Inst A V B W} (h : Reconstructs I J)
    (S : A → Bool) (b : B) : Hma.live I b S ↔ Hma.live J b S := by
  have forward {I J : Inst A V B W} (h : Reconstructs I J)
      (hl : Hma.live I b S) : Hma.live J b S := by
    obtain ⟨x, hx, y, hy, agree, different⟩ := hl
    refine ⟨x, (h.rows x).mp hx, y, (h.rows y).mp hy, ?_, ?_⟩
    · intro a ha hs
      exact agree a (h.axes.symm ▸ ha) hs
    · rw [← h.behavior x hx b, ← h.behavior y hy b]
      exact different
  exact ⟨forward h, forward (reconstructs_symm h)⟩

theorem reconstructed_livelist {I J : Inst A V B W} (h : Reconstructs I J)
    (S : A → Bool) : livelist I S = livelist J S := by
  unfold livelist
  rw [h.comps]
  apply filtercongr
  intro b _
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using reconstructed_live h S b

theorem reconstructed_engaged {I J : Inst A V B W} (h : Reconstructs I J)
    (S : A → Bool) (e : List B) : engaged I S e ↔ engaged J S e := by
  simp only [engaged, h.edges, reconstructed_livelist h S]

theorem reconstructed_mu {I J : Inst A V B W} (h : Reconstructs I J)
    (S : A → Bool) : mu I S = mu J S := by
  unfold mu
  have same : I.edges.map (fun e => if engaged I S e then I.weight e else 0) =
      I.edges.map (fun e => if engaged J S e then J.weight e else 0) := by
    apply List.map_congr_left
    intro e he
    simp only [reconstructed_engaged h S e, h.weights e he]
  rw [same, h.edges]

theorem reconstructed_rho {I J : Inst A V B W} (h : Reconstructs I J)
    (S : A → Bool) : rho I S = rho J S := by
  simp only [rho, lam, reconstructed_mu h S, reconstructed_livelist h S]

theorem reconstructed_minimal {I J : Inst A V B W} (h : Reconstructs I J)
    (S : A → Bool) : minimal I S ↔ minimal J S := by
  simp only [minimal, sufficient, proper, subset, h.axes, reconstructed_mu h]

theorem reconstructed_highest {I J : Inst A V B W} (h : Reconstructs I J)
    (S : A → Bool) : highest I S ↔ highest J S := by
  simp only [highest, reconstructed_minimal h, rhole, lam,
    reconstructed_mu h, reconstructed_livelist h]

theorem reconstructed_dead {I J : Inst A V B W} (h : Reconstructs I J)
    (a : A) : dead I a ↔ dead J a := by
  simp only [dead, reconstructed_livelist h]

theorem reconstructed_incremental_live {I J old : Inst A V B W}
    (h : Reconstructs I J) (S T : A → Bool) (b : B) :
    incremental (graph old T) (graph J S) (.live b) ↔ Hma.live I b S :=
  (incremental_live_exact old J T S b).trans (reconstructed_live h S b).symm

end HmaGraph
