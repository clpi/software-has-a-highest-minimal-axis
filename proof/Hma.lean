/-
  The highest minimal axis: the proved core.

  The object, from the spec this repo carries as SPEC.md.
  An instance is a qualified parametric system: a finite
  list of named axes, each configuration a function from
  axes to a uniform finite value type, a contract naming
  the allowed configurations, a finite list of behavior
  components, a behavior function from configurations to
  component values, a hypergraph on the components, and a
  weight for each hyperedge, positive on every hyperedge
  of size at least two.

  An axis set is a function from axes to Bool. Varying an
  axis set inside the contract makes a component live when
  some variation over the set changes it; the engaged
  hyperedges are those of size at least two lying inside
  the live set; the emergence measure mu is the engaged
  weight sum, and the refinement coordinate lambda is the
  live count. The refinement vector rho is the pair
  (mu, lambda) under lexicographic order. An axis set is
  sufficient when its mu reaches the full axis set's mu,
  minimal when no proper subset is sufficient, and
  highest minimal when its rho stands over every minimal
  sufficient set's rho.

  This module proves: monotonicity of liveness, mu, and
  lambda under subsets (L1); sufficiency forcing equality
  of the engaged structure, the positive weights being
  load bearing (L2); existence of a highest minimal axis
  set for every instance (T1); strict fall of mu on every
  proper subset of a highest minimal set (T2); maximality
  and rho uniqueness across highest minimal sets (T3);
  functoriality of the induced transformation on
  variations, with structure preservation (T4); and the
  degenerate characterization, with its empty and
  singleton contract corollary (T5). The corrected dead
  axis facts close the module: removing an emergent-dead
  axis is already sufficient, so a dead axis makes the
  full set non-minimal; the stronger sentence, that a
  dead axis belongs to no minimal sufficient set, is
  false, and Instance X in the controls is the standing
  counterexample.

  Finite sets are carried as lists and as Bool valued
  functions, in the hand rolled style of the family: no
  library beyond the Lean core is used.
-/

namespace Hma

variable {A V B W : Type} [DecidableEq A] [DecidableEq B] [DecidableEq V] [DecidableEq W]

structure Inst (A V B W : Type) [DecidableEq A] [DecidableEq B] [DecidableEq V] [DecidableEq W] where
  axes : List A
  axesnodup : axes.Nodup
  axescomplete : ∀ a, a ∈ axes
  comps : List B
  contract : List (A → V)
  beh : (A → V) → B → W
  edges : List (List B)
  weight : List B → Nat
  weightpos : ∀ e ∈ edges, 2 ≤ e.length → 0 < weight e

def allaxes : A → Bool := fun _ => true
def noaxes : A → Bool := fun _ => false

abbrev subset (I : Inst A V B W) (S T : A → Bool) : Prop :=
  ∀ a ∈ I.axes, S a = true → T a = true

abbrev proper (I : Inst A V B W) (S T : A → Bool) : Prop :=
  subset I S T ∧ ∃ a ∈ I.axes, T a = true ∧ S a = false

abbrev agreeoff (I : Inst A V B W) (x x' : A → V) (S : A → Bool) : Prop :=
  ∀ a ∈ I.axes, S a = false → x a = x' a

abbrev live (I : Inst A V B W) (b : B) (S : A → Bool) : Prop :=
  ∃ x ∈ I.contract, ∃ x' ∈ I.contract, agreeoff I x x' S ∧ I.beh x b ≠ I.beh x' b

instance livedec (I : Inst A V B W) (S : A → Bool) : DecidablePred (fun b => live I b S) :=
  fun b => by unfold live agreeoff; infer_instance

def livelist (I : Inst A V B W) (S : A → Bool) : List B :=
  I.comps.filter (fun b => decide (live I b S))

abbrev engaged (I : Inst A V B W) (S : A → Bool) (e : List B) : Prop :=
  e ∈ I.edges ∧ 2 ≤ e.length ∧ ∀ b ∈ e, b ∈ livelist I S

instance engageddec (I : Inst A V B W) (S : A → Bool) : DecidablePred (engaged I S) :=
  fun e => by unfold engaged; infer_instance

def engagedlist (I : Inst A V B W) (S : A → Bool) : List (List B) :=
  I.edges.filter (fun e => decide (engaged I S e))

def mu (I : Inst A V B W) (S : A → Bool) : Nat :=
  (I.edges.map (fun e => if engaged I S e then I.weight e else 0)).sum

def lam (I : Inst A V B W) (S : A → Bool) : Nat := (livelist I S).length

def rho (I : Inst A V B W) (S : A → Bool) : Nat × Nat := (mu I S, lam I S)

abbrev rhole (I : Inst A V B W) (S T : A → Bool) : Prop :=
  mu I S < mu I T ∨ (mu I S = mu I T ∧ lam I S ≤ lam I T)

abbrev sufficient (I : Inst A V B W) (S : A → Bool) : Prop := mu I S = mu I (allaxes (A := A))

abbrev minimal (I : Inst A V B W) (S : A → Bool) : Prop :=
  sufficient I S ∧ ∀ T, proper I T S → ¬ sufficient I T

abbrev highest (I : Inst A V B W) (S : A → Bool) : Prop :=
  minimal I S ∧ ∀ T, minimal I T → rhole I T S

def rem (S : A → Bool) (a : A) : A → Bool := fun x => S x && decide (x ≠ a)

abbrev dead (I : Inst A V B W) (a : A) : Prop :=
  livelist I (rem allaxes a) = livelist I allaxes

abbrev variation (I : Inst A V B W) (S : A → Bool) (x x' : A → V) : Prop :=
  x ∈ I.contract ∧ x' ∈ I.contract ∧ agreeoff I x x' S

def trans (I : Inst A V B W) (p : (A → V) × (A → V)) : (B → W) × (B → W) :=
  (I.beh p.1, I.beh p.2)

def sublists : List α → List (List α)
  | [] => [[]]
  | a :: l => sublists l ++ (sublists l).map (a :: ·)


/- Monotonicity and the finite list machinery. -/

theorem filterlenmono {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    have ih := filterlenmono p q l h
    by_cases hpa : p a = true
    · by_cases hqa : q a = true
      · rw [List.filter_cons, List.filter_cons, if_pos hpa, if_pos hqa,
          List.length_cons, List.length_cons]; omega
      · exact absurd (h a hpa) hqa
    · by_cases hqa : q a = true
      · rw [List.filter_cons, List.filter_cons, if_neg hpa, if_pos hqa,
          List.length_cons]; omega
      · rw [List.filter_cons, List.filter_cons, if_neg hpa, if_neg hqa]; omega

theorem filterlenstrict {α : Type} (p q : α → Bool) :
    ∀ (l : List α), l.Nodup → (∀ x, p x = true → q x = true) →
      ∀ a0 ∈ l, q a0 = true → p a0 = false →
      (l.filter p).length < (l.filter q).length
  | [], _, _, a0, h0, _, _ => by simp at h0
  | a :: l, hnd, h, a0, ha0, hq, hp => by
    rw [List.nodup_cons] at hnd
    have ihmono := filterlenmono p q l h
    by_cases haa : a = a0
    · subst haa
      have hpa : ¬ p a = true := fun hh => Bool.false_ne_true (hp.symm.trans hh)
      rw [List.filter_cons, List.filter_cons, if_neg hpa, if_pos hq,
        List.length_cons]; omega
    · have ha0l : a0 ∈ l := by
        rcases List.mem_cons.mp ha0 with h1 | h1
        · exact absurd h1.symm haa
        · exact h1
      have ih := filterlenstrict p q l hnd.2 h a0 ha0l hq hp
      by_cases hpa : p a = true
      · by_cases hqa : q a = true
        · rw [List.filter_cons, List.filter_cons, if_pos hpa, if_pos hqa,
            List.length_cons, List.length_cons]; omega
        · exact absurd (h a hpa) hqa
      · by_cases hqa : q a = true
        · rw [List.filter_cons, List.filter_cons, if_neg hpa, if_pos hqa,
            List.length_cons]; omega
        · rw [List.filter_cons, List.filter_cons, if_neg hpa, if_neg hqa]; omega

theorem summmono {α : Type} (fs ft : α → Nat) :
    ∀ (l : List α), (∀ e ∈ l, fs e ≤ ft e) → (l.map fs).sum ≤ (l.map ft).sum
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    have ih := summmono fs ft l (fun e he => h e (List.mem_cons_of_mem a he))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    simp only [List.map_cons, List.sum_cons]; omega

theorem sumstrict {α : Type} [DecidableEq α] (fs ft : α → Nat) :
    ∀ (l : List α) (e0 : α), e0 ∈ l → (∀ e ∈ l, fs e ≤ ft e) →
      fs e0 < ft e0 → (l.map fs).sum < (l.map ft).sum
  | [], _, h0, _, _ => by simp at h0
  | a :: l, e0, he, h, h0 => by
    have ihmono := summmono fs ft l (fun e he2 => h e (List.mem_cons_of_mem a he2))
    by_cases haa : a = e0
    · subst haa
      have ha := h a (List.mem_cons.mpr (Or.inl rfl))
      simp only [List.map_cons, List.sum_cons]; omega
    · have hel : e0 ∈ l := by
        rcases List.mem_cons.mp he with h1 | h1
        · exact absurd h1.symm haa
        · exact h1
      have ih := sumstrict fs ft l e0 hel (fun e he2 => h e (List.mem_cons_of_mem a he2)) h0
      have ha := h a (List.mem_cons.mpr (Or.inl rfl))
      simp only [List.map_cons, List.sum_cons]; omega

theorem filtercongr {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ e ∈ l, p e = q e) → l.filter p = l.filter q
  | [], _ => rfl
  | a :: l, h => by
    have ih := filtercongr p q l (fun e he => h e (List.mem_cons_of_mem a he))
    have ha := h a (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter_cons, ha, ih]

theorem subsetrefl (I : Inst A V B W) (S : A → Bool) : subset I S S :=
  fun _ _ h => h

theorem subsettrans (I : Inst A V B W) {S T U : A → Bool} :
    subset I S T → subset I T U → subset I S U :=
  fun h1 h2 a ha hs => h2 a ha (h1 a ha hs)

theorem subsetall (I : Inst A V B W) (S : A → Bool) : subset I S allaxes :=
  fun _ _ _ => rfl

theorem agreeoffmono (I : Inst A V B W) {S T : A → Bool} {x x' : A → V} :
    subset I S T → agreeoff I x x' S → agreeoff I x x' T := by
  intro hsub hagree a ha hTa
  apply hagree a ha
  cases hSa : S a
  · rfl
  · have h1 := hsub a ha hSa
    rw [hTa] at h1
    exact False.elim (Bool.false_ne_true h1)

theorem livemono (I : Inst A V B W) {S T : A → Bool} (h : subset I S T) {b : B} :
    live I b S → live I b T := by
  rintro ⟨x, hx, x', hx', hagree, hne⟩
  exact ⟨x, hx, x', hx', agreeoffmono I h hagree, hne⟩

theorem livemem (I : Inst A V B W) (S : A → Bool) (b : B) :
    b ∈ livelist I S ↔ b ∈ I.comps ∧ live I b S := by
  unfold livelist
  rw [List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, of_decide_eq_true h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, decide_eq_true h2⟩

theorem engagedmono (I : Inst A V B W) {S T : A → Bool} (h : subset I S T) {e : List B} :
    engaged I S e → engaged I T e := by
  rintro ⟨h1, h2, h3⟩
  refine ⟨h1, h2, fun b hb => ?_⟩
  have hb2 := h3 b hb
  rw [livemem] at hb2 ⊢
  exact ⟨hb2.1, livemono I h hb2.2⟩

theorem mumono (I : Inst A V B W) {S T : A → Bool} (h : subset I S T) :
    mu I S ≤ mu I T := by
  unfold mu
  apply summmono
  intro e _
  by_cases hs : engaged I S e
  · have ht : engaged I T e := engagedmono I h hs
    simp only [if_pos hs, if_pos ht]
    exact Nat.le_refl _
  · by_cases ht : engaged I T e
    · simp only [if_neg hs, if_pos ht]
      exact Nat.zero_le _
    · simp only [if_neg hs, if_neg ht]
      exact Nat.le_refl _

theorem lammmono (I : Inst A V B W) {S T : A → Bool} (h : subset I S T) :
    lam I S ≤ lam I T := by
  unfold lam livelist
  apply filterlenmono
  intro b hb
  rw [decide_eq_true_eq] at hb ⊢
  exact livemono I h hb

theorem cardle (I : Inst A V B W) (S : A → Bool) :
    (I.axes.filter S).length ≤ I.axes.length :=
  List.length_filter_le _ _

theorem lamle (I : Inst A V B W) (S : A → Bool) : lam I S ≤ I.comps.length := by
  unfold lam livelist
  exact List.length_filter_le _ _

theorem filternil {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = false) → l.filter p = []
  | [], _ => rfl
  | a :: l, h => by
    have ha : ¬ p a = true := fun hh =>
      Bool.false_ne_true ((h a (List.mem_cons.mpr (Or.inl rfl))).symm.trans hh)
    rw [List.filter_cons, if_neg ha]
    exact filternil p l (fun x hx => h x (List.mem_cons_of_mem a hx))

theorem mapcongr {α β : Type} (f g : α → β) :
    ∀ (l : List α), (∀ e ∈ l, f e = g e) → l.map f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.map_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
      mapcongr f g l (fun e he => h e (List.mem_cons_of_mem a he))]

theorem mapsumzero {α : Type} (f : α → Nat) :
    ∀ (l : List α), (∀ e ∈ l, f e = 0) → (l.map f).sum = 0
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, List.sum_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
      mapsumzero f l (fun e he => h e (List.mem_cons_of_mem a he))]

/-- The size of an axis set: the axes it keeps, counted on the
    instance's axis list. -/
def card (I : Inst A V B W) (S : A → Bool) : Nat := (I.axes.filter S).length

theorem cardstrict (I : Inst A V B W) {S T : A → Bool} (h : proper I T S) :
    card I T < card I S := by
  unfold card
  rcases h.2 with ⟨a0, ha0, hS, hT⟩
  have hsub : ∀ x, T x = true → S x = true :=
    fun x hx => h.1 x (I.axescomplete x) hx
  exact filterlenstrict T S I.axes I.axesnodup hsub a0 ha0 hS hT

/- L2: sufficiency forces the engaged structure. -/

theorem engagedofsufficient (I : Inst A V B W) {S : A → Bool}
    (hsuff : sufficient I S) :
    ∀ e, engaged I (allaxes (A := A)) e → engaged I S e := by
  intro e he
  apply Classical.byContradiction
  intro hne
  have hmono : ∀ f ∈ I.edges,
      (if engaged I S f then I.weight f else 0) ≤
        (if engaged I (allaxes (A := A)) f then I.weight f else 0) := by
    intro f _
    by_cases hf : engaged I S f
    · have hf2 := engagedmono I (subsetall I S) hf
      simp only [if_pos hf, if_pos hf2]
      exact Nat.le_refl _
    · by_cases hf2 : engaged I (allaxes (A := A)) f
      · simp only [if_neg hf, if_pos hf2]
        exact Nat.zero_le _
      · simp only [if_neg hf, if_neg hf2]
        exact Nat.le_refl _
  have hlt : mu I S < mu I (allaxes (A := A)) := by
    unfold mu
    apply sumstrict _ _ I.edges e he.1 hmono
    simp only [if_neg hne, if_pos he]
    exact I.weightpos e he.1 he.2.1
  exact (Nat.ne_of_lt hlt) hsuff

theorem engagedlistofsufficient (I : Inst A V B W) {S : A → Bool}
    (hsuff : sufficient I S) :
    engagedlist I S = engagedlist I (allaxes (A := A)) := by
  unfold engagedlist
  apply filtercongr
  intro e _
  rw [decide_eq_decide]
  exact ⟨fun h => engagedmono I (subsetall I S) h,
    fun h => engagedofsufficient I hsuff e h⟩

/- Every axis set is named by a sublist of the axis list. -/

theorem filtermemsublists {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.filter p ∈ sublists l
  | [] => by simp [sublists]
  | a :: l => by
    have ih := filtermemsublists p l
    by_cases hpa : p a = true
    · have hrw : (a :: l).filter p = a :: l.filter p := by
        rw [List.filter_cons, if_pos hpa]
      rw [hrw]
      show _ ∈ sublists l ++ (sublists l).map (a :: ·)
      exact List.mem_append_right _ (List.mem_map_of_mem ih)
    · have hrw : (a :: l).filter p = l.filter p := by
        rw [List.filter_cons, if_neg hpa]
      rw [hrw]
      show _ ∈ sublists l ++ (sublists l).map (a :: ·)
      exact List.mem_append_left _ ih

theorem subsetrep (I : Inst A V B W) (S : A → Bool) :
    ∃ l ∈ sublists I.axes, S = fun a => decide (a ∈ l) := by
  refine ⟨I.axes.filter S, filtermemsublists S I.axes, ?_⟩
  funext a
  by_cases hSa : S a = true
  · have hmem : a ∈ I.axes.filter S :=
      List.mem_filter.mpr ⟨I.axescomplete a, hSa⟩
    simp [hSa, hmem]
  · have hSf : S a = false := by
      cases hb : S a
      · rfl
      · exact absurd hb hSa
    have hmem : a ∉ I.axes.filter S :=
      fun hh => hSa (List.mem_filter.mp hh).2
    simp [hSf, hmem]

/- Existence: descent to a minimal sufficient set, then
   refinement ascent to a highest one. -/

theorem minimalexists (I : Inst A V B W) :
    ∀ (n : Nat) (S : A → Bool), card I S ≤ n → sufficient I S →
      ∃ T, subset I T S ∧ minimal I T := by
  intro n
  induction n with
  | zero =>
    intro S hcard hsuff
    rcases Classical.em (∀ T, proper I T S → ¬ sufficient I T) with hmin | hnot
    · exact ⟨S, subsetrefl I S, hsuff, hmin⟩
    · exfalso
      have hex : ∃ T, proper I T S ∧ sufficient I T := by
        apply Classical.byContradiction
        intro hnex
        apply hnot
        intro T hp hs
        exact hnex ⟨T, hp, hs⟩
      rcases hex with ⟨T, hprop, _⟩
      have hlt := cardstrict I hprop
      omega
  | succ n ih =>
    intro S hcard hsuff
    rcases Classical.em (∀ T, proper I T S → ¬ sufficient I T) with hmin | hnot
    · exact ⟨S, subsetrefl I S, hsuff, hmin⟩
    · have hex : ∃ T, proper I T S ∧ sufficient I T := by
        apply Classical.byContradiction
        intro hnex
        apply hnot
        intro T hp hs
        exact hnex ⟨T, hp, hs⟩
      rcases hex with ⟨T, hprop, hsuffT⟩
      have hlt := cardstrict I hprop
      rcases ih T (by omega) hsuffT with ⟨U, hUT, hminU⟩
      exact ⟨U, subsettrans I hUT hprop.1, hminU⟩

theorem highestfromminimal (I : Inst A V B W) :
    ∀ (n : Nat) (S : A → Bool), minimal I S →
      I.comps.length - lam I S ≤ n → ∃ T, highest I T := by
  intro n
  induction n with
  | zero =>
    intro S hmin hmeasure
    rcases Classical.em (∀ T, minimal I T → rhole I T S) with hmax | hnot
    · exact ⟨S, hmin, hmax⟩
    · exfalso
      have hex : ∃ T, minimal I T ∧ ¬ rhole I T S := by
        apply Classical.byContradiction
        intro hnex
        apply hnot
        intro T hminT
        apply Classical.byContradiction
        intro hnr
        exact hnex ⟨T, hminT, hnr⟩
      rcases hex with ⟨T, hminT, hnr⟩
      have hmu : mu I T = mu I S := by
        have h1 : sufficient I T := hminT.1
        have h2 : sufficient I S := hmin.1
        unfold sufficient at h1 h2
        rw [h1, h2]
      have hlam : lam I S < lam I T := by
        by_cases hle : lam I T ≤ lam I S
        · exact absurd (Or.inr ⟨hmu, hle⟩) hnr
        · omega
      have hbound : lam I T ≤ I.comps.length := lamle I T
      omega
  | succ n ih =>
    intro S hmin hmeasure
    rcases Classical.em (∀ T, minimal I T → rhole I T S) with hmax | hnot
    · exact ⟨S, hmin, hmax⟩
    · have hex : ∃ T, minimal I T ∧ ¬ rhole I T S := by
        apply Classical.byContradiction
        intro hnex
        apply hnot
        intro T hminT
        apply Classical.byContradiction
        intro hnr
        exact hnex ⟨T, hminT, hnr⟩
      rcases hex with ⟨T, hminT, hnr⟩
      have hmu : mu I T = mu I S := by
        have h1 : sufficient I T := hminT.1
        have h2 : sufficient I S := hmin.1
        unfold sufficient at h1 h2
        rw [h1, h2]
      have hlam : lam I S < lam I T := by
        by_cases hle : lam I T ≤ lam I S
        · exact absurd (Or.inr ⟨hmu, hle⟩) hnr
        · omega
      have hbound : lam I T ≤ I.comps.length := lamle I T
      exact ih T hminT (by omega)

/-- T1: a highest minimal axis set exists for every instance. -/
theorem highestexists (I : Inst A V B W) : ∃ S, highest I S := by
  have hsuff : sufficient I (allaxes (A := A)) := rfl
  rcases minimalexists I (card I (allaxes (A := A))) (allaxes (A := A))
    (Nat.le_refl _) hsuff with ⟨T, _, hminT⟩
  exact highestfromminimal I I.comps.length T hminT (Nat.sub_le _ _)

/-- T2: under a highest minimal set, every proper subset
    falls strictly below the full emergence. -/
theorem highestproper (I : Inst A V B W) {S S' : A → Bool} :
    highest I S → proper I S' S → mu I S' < mu I (allaxes (A := A)) := by
  intro hhigh hprop
  have hnsuff : ¬ sufficient I S' := hhigh.1.2 S' hprop
  have hle : mu I S' ≤ mu I (allaxes (A := A)) := mumono I (subsetall I S')
  unfold sufficient at hnsuff
  omega

/-- T3, maximality clause: a highest minimal set stands over
    every minimal sufficient set in the refinement order. -/
theorem highestmax (I : Inst A V B W) {S T : A → Bool} :
    highest I S → minimal I T → rhole I T S :=
  fun hhigh hmin => hhigh.2 T hmin

/-- T3, uniqueness clause: any two highest minimal sets have
    the same refinement vector. -/
theorem highestunique (I : Inst A V B W) {S T : A → Bool} :
    highest I S → highest I T → rho I S = rho I T := by
  intro h1 h2
  have ha := h1.2 T h2.1
  have hb := h2.2 S h1.1
  unfold rhole at ha hb
  have hmu : mu I S = mu I T := by
    rcases ha with h | ⟨h, _⟩ <;> rcases hb with h' | ⟨h', _⟩ <;> omega
  have hlam : lam I S = lam I T := by
    rcases ha with h | ⟨_, h⟩ <;> rcases hb with h' | ⟨_, h'⟩ <;> omega
  unfold rho
  rw [hmu, hlam]

/- T4: the induced transformation on variations. -/

theorem variationcomp (I : Inst A V B W) {S : A → Bool} {x x' x'' : A → V} :
    variation I S x x' → variation I S x' x'' → variation I S x x'' :=
  fun h1 h2 => ⟨h1.1, h2.2.1,
    fun a ha hSa => (h1.2.2 a ha hSa).trans (h2.2.2 a ha hSa)⟩

theorem variationrefl (I : Inst A V B W) {S : A → Bool} {x : A → V}
    (hx : x ∈ I.contract) : variation I S x x :=
  ⟨hx, hx, fun _ _ _ => rfl⟩

theorem transid (I : Inst A V B W) (x : A → V) :
    trans I (x, x) = (I.beh x, I.beh x) := rfl

theorem transcomp (I : Inst A V B W) (x x' x'' : A → V) :
    trans I (x, x'') = ((trans I (x, x')).1, (trans I (x', x'')).2) := rfl

theorem highestengaged (I : Inst A V B W) {S : A → Bool} (h : highest I S) :
    engagedlist I S = engagedlist I (allaxes (A := A)) ∧
      ∀ e, engaged I S e → ∀ b ∈ e, b ∈ livelist I S :=
  ⟨engagedlistofsufficient I h.1.1, fun _ he => he.2.2⟩

/-- T5: the degenerate characterization. The whole axis set
    is forced exactly when no proper subset is sufficient. -/
theorem degenerate (I : Inst A V B W) :
    (∀ T, proper I T (allaxes (A := A)) → ¬ sufficient I T) ↔
      (∀ S, highest I S → S = allaxes (A := A)) := by
  constructor
  · intro hno S hhigh
    funext a
    by_cases hSa : S a = true
    · simp [allaxes, hSa]
    · exfalso
      have hSf : S a = false := by
        cases hb : S a
        · rfl
        · exact absurd hb hSa
      have hprop : proper I S (allaxes (A := A)) :=
        ⟨subsetall I S, a, I.axescomplete a, rfl, hSf⟩
      exact hno S hprop hhigh.1.1
  · intro hall T hprop hsuff
    rcases minimalexists I (card I T) T (Nat.le_refl _) hsuff with ⟨U, _, hminU⟩
    rcases highestfromminimal I I.comps.length U hminU (Nat.sub_le _ _)
      with ⟨S, hhigh⟩
    have hSeq : S = allaxes (A := A) := hall S hhigh
    have hprop' : proper I T S := by
      rw [hSeq]
      exact hprop
    exact hhigh.1.2 T hprop' hsuff

/- The empty and singleton contract corollary of T5: when
   the contract carries at most one configuration, no
   variation exists, the empty axis set is the unique
   highest minimal vector. -/

theorem emptyoronehighest (I : Inst A V B W)
    (hcon : ∀ x y, x ∈ I.contract → y ∈ I.contract → x = y) :
    highest I (noaxes (A := A)) ∧
      ∀ S, highest I S → S = noaxes (A := A) := by
  have hlive : ∀ (S : A → Bool) (b : B), ¬ live I b S := by
    intro S b h
    rcases h with ⟨x, hx, x', hx', _, hne⟩
    exact hne (by rw [hcon x x' hx hx'])
  have hlist : ∀ S : A → Bool, livelist I S = [] := by
    intro S
    unfold livelist
    apply filternil
    intro b _
    exact decide_eq_false (hlive S b)
  have hmu : ∀ S : A → Bool, mu I S = 0 := by
    intro S
    unfold mu
    apply mapsumzero
    intro e he
    by_cases heng : engaged I S e
    · exfalso
      rcases e with _ | ⟨b, e'⟩
      · exact absurd heng.2.1 (by decide : ¬ (2 ≤ 0))
      · have hb := heng.2.2 b (List.mem_cons.mpr (Or.inl rfl))
        rw [hlist S] at hb
        simp at hb
    · simp only [if_neg heng]
  have hsuffempty : sufficient I (noaxes (A := A)) := by
    unfold sufficient
    rw [hmu, hmu]
  constructor
  · refine ⟨⟨hsuffempty, ?_⟩, ?_⟩
    · intro T hprop _
      rcases hprop.2 with ⟨a, _, htrue, _⟩
      exact Bool.false_ne_true htrue
    · intro T _
      refine Or.inr ⟨?_, ?_⟩
      · unfold sufficient at *
        rw [hmu, hmu]
      · unfold lam
        rw [hlist T, hlist (noaxes (A := A))]
        exact Nat.le_refl _
  · intro S hhigh
    funext a
    by_cases hSa : S a = true
    · exfalso
      have hprop : proper I (noaxes (A := A)) S :=
        ⟨fun _ _ hh => (Bool.false_ne_true hh).elim, a, I.axescomplete a, hSa, rfl⟩
      exact hhigh.1.2 _ hprop hsuffempty
    · cases hb : S a
      · simp [noaxes, hb]
      · exact absurd hb hSa

/- The corrected dead axis facts: an emergent-dead axis
   makes the full set non-minimal, because removing it
   already reaches the full emergence. The stronger sentence
   one might guess, that a dead axis belongs to no minimal
   sufficient set, is false: Instance X is the standing
   counterexample, carried in the controls. -/

theorem mueqofliveeq (I : Inst A V B W) {S T : A → Bool}
    (h : livelist I S = livelist I T) : mu I S = mu I T := by
  unfold mu
  congr 1
  apply mapcongr
  intro e _
  by_cases hS : engaged I S e
  · have hT : engaged I T e :=
      ⟨hS.1, hS.2.1, fun b hb => by rw [← h]; exact hS.2.2 b hb⟩
    simp only [if_pos hS, if_pos hT]
  · by_cases hT : engaged I T e
    · exfalso
      apply hS
      exact ⟨hT.1, hT.2.1, fun b hb => by rw [h]; exact hT.2.2 b hb⟩
    · simp only [if_neg hS, if_neg hT]

theorem deadremovesufficient (I : Inst A V B W) {a : A} (h : dead I a) :
    sufficient I (rem (allaxes (A := A)) a) :=
  mueqofliveeq I h

theorem deadnotminimal (I : Inst A V B W) {a : A} (h : dead I a) :
    ¬ minimal I (allaxes (A := A)) := by
  intro hmin
  apply hmin.2 (rem (allaxes (A := A)) a) _ (deadremovesufficient I h)
  refine ⟨fun _ _ _ => rfl, a, I.axescomplete a, rfl, ?_⟩
  simp [rem, allaxes]


/-- L1, bundled: under a subset, liveness, the emergence
    measure, and the refinement coordinate all grow. -/
theorem livelistsubset (I : Inst A V B W) {S T : A → Bool} (h : subset I S T) :
    ∀ b ∈ livelist I S, b ∈ livelist I T := by
  intro b hb
  rw [livemem] at hb ⊢
  exact ⟨hb.1, livemono I h hb.2⟩

theorem monotone (I : Inst A V B W) {S T : A → Bool} (h : subset I S T) :
    (∀ b, live I b S → live I b T) ∧ mu I S ≤ mu I T ∧ lam I S ≤ lam I T :=
  ⟨fun _ => livemono I h, mumono I h, lammmono I h⟩

end Hma
