import IncrementalCounts
import Init.Data.List.FinRange

namespace HmaExponential

open Hma

theorem ofFn_nodup {α : Type} (n : Nat) (f : Fin n → α)
    (hinj : ∀ i j, f i = f j → i = j) : (List.ofFn f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp h
      have hbad := congrArg Fin.val (hinj i.succ 0 hi)
      simp at hbad
    · apply ih
      intro i j hij
      exact Fin.ext (Nat.succ.inj (congrArg Fin.val (hinj i.succ j.succ hij)))

abbrev Axis (n : Nat) := Fin n × Bool

def axes (n : Nat) : List (Axis n) :=
  List.ofFn (fun i : Fin n => (i, false)) ++ List.ofFn (fun i : Fin n => (i, true))

theorem axes_complete (n : Nat) (a : Axis n) : a ∈ axes n := by
  obtain ⟨i, b⟩ := a
  cases b
  · exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem axes_nodup (n : Nat) : (axes n).Nodup := by
  apply List.pairwise_append.mpr
  refine ⟨ofFn_nodup _ _ (fun _ _ h => (Prod.mk.inj h).1),
    ofFn_nodup _ _ (fun _ _ h => (Prod.mk.inj h).1), ?_⟩
  intro a ha b hb heq
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hb
  rw [← hi, ← hj] at heq
  simp at heq

def zeroRow (n : Nat) : Axis n → Bool := fun _ => false
def unitRow {n : Nat} (selected : Axis n) : Axis n → Bool := fun a => decide (a = selected)
def behavior {n : Nat} (x : Axis n → Bool) (b : Axis n) : Bool :=
  x (b.1, false) || x (b.1, true)
def edge {n : Nat} (i : Fin n) : List (Axis n) := [(i, false), (i, true)]

def paired (n : Nat) : Inst (Axis n) Bool (Axis n) Bool :=
  { axes := axes n
    axesnodup := axes_nodup n
    axescomplete := axes_complete n
    comps := axes n
    contract := zeroRow n :: (axes n).map unitRow
    beh := behavior
    edges := List.ofFn edge
    weight := fun _ => 1
    weightpos := by intros; decide }

def hits {n : Nat} (S : Axis n → Bool) (i : Fin n) : Prop :=
  S (i, false) = true ∨ S (i, true) = true

theorem live_iff_hits {n : Nat} (S : Axis n → Bool) (b : Axis n) :
    live (paired n) b S ↔ hits S b.1 := by
  constructor
  · rintro ⟨x, _, y, _, hagree, hchange⟩
    by_cases hf : S (b.1, false) = true
    · exact Or.inl hf
    by_cases ht : S (b.1, true) = true
    · exact Or.inr ht
    have hff : S (b.1, false) = false := Bool.eq_false_iff.mpr hf
    have htf : S (b.1, true) = false := Bool.eq_false_iff.mpr ht
    have h1 := hagree (b.1, false) (axes_complete n _) hff
    have h2 := hagree (b.1, true) (axes_complete n _) htf
    apply False.elim
    apply hchange
    change behavior x b = behavior y b
    simp only [behavior, h1, h2]
  · intro h
    have make : ∀ selected : Axis n, selected.1 = b.1 → S selected = true →
        live (paired n) b S := by
      intro selected hgroup hs
      refine ⟨zeroRow n, by simp [paired], unitRow selected,
        List.mem_cons_of_mem _ (List.mem_map_of_mem (axes_complete n selected)), ?_, ?_⟩
      · intro a _ ha
        have hne : a ≠ selected := by
          intro heq
          subst a
          simp [hs] at ha
        simp [zeroRow, unitRow, hne]
      · obtain ⟨i, which⟩ := selected
        simp only at hgroup
        subst i
        cases which <;> simp [paired, behavior, unitRow, zeroRow]
    rcases h with hf | ht
    · exact make (b.1, false) rfl hf
    · exact make (b.1, true) rfl ht

def covers {n : Nat} (S : Axis n → Bool) : Prop := ∀ i, hits S i

theorem live_of_covers {n : Nat} (S : Axis n → Bool) (h : covers S) (b : Axis n) :
    live (paired n) b S := (live_iff_hits S b).mpr (h b.1)

theorem sufficient_iff_covers {n : Nat} (S : Axis n → Bool) :
    sufficient (paired n) S ↔ covers S := by
  constructor
  · intro hs i
    have he : edge i ∈ (paired n).edges := List.mem_ofFn.mpr ⟨i, rfl⟩
    have hfull : engaged (paired n) allaxes (edge i) := by
      refine ⟨he, by simp [edge], ?_⟩
      intro b _
      apply List.mem_filter.mpr
      exact ⟨axes_complete n b, by simp only [decide_eq_true_eq]; exact
        (live_iff_hits allaxes b).mpr (Or.inl rfl)⟩
    have heng := Hma.engagedofsufficient (paired n) hs (edge i) hfull
    have hb := heng.2.2 (i, false) (by simp [edge])
    have hlive : live (paired n) (i, false) S := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp hb).2
    exact (live_iff_hits S (i, false)).mp hlive
  · intro h
    have hlive : livelist (paired n) S = livelist (paired n) allaxes := by
      apply Hma.filtercongr
      intro b _
      rw [decide_eq_decide]
      exact ⟨fun _ => (live_iff_hits allaxes b).mpr (Or.inl rfl), fun _ => live_of_covers S h b⟩
    exact Hma.mueqofliveeq (paired n) hlive

def choose {n : Nat} (choice : Fin n → Bool) : Axis n → Bool :=
  fun a => decide (a.2 = choice a.1)

theorem choose_covers {n : Nat} (choice : Fin n → Bool) : covers (choose choice) := by
  intro i
  cases hc : choice i <;> simp [hits, choose, hc]

theorem choose_minimal {n : Nat} (choice : Fin n → Bool) : minimal (paired n) (choose choice) := by
  refine ⟨(sufficient_iff_covers _).mpr (choose_covers choice), ?_⟩
  intro T hp hs
  obtain ⟨a, ha, hselected, hmissing⟩ := hp.2
  have hchoice : a.2 = choice a.1 := by simpa only [choose, decide_eq_true_eq] using hselected
  have hcover := (sufficient_iff_covers T).mp hs a.1
  rcases hcover with hf | ht
  · have hsub := hp.1 (a.1, false) (axes_complete n _) hf
    have hc : false = choice a.1 := by simpa [choose] using hsub
    have heq : a = (a.1, false) := Prod.ext rfl (hchoice.trans hc.symm)
    rw [heq] at hmissing
    simp [hf] at hmissing
  · have hsub := hp.1 (a.1, true) (axes_complete n _) ht
    have hc : true = choice a.1 := by simpa [choose] using hsub
    have heq : a = (a.1, true) := Prod.ext rfl (hchoice.trans hc.symm)
    rw [heq] at hmissing
    simp [ht] at hmissing

theorem choose_highest {n : Nat} (choice : Fin n → Bool) : highest (paired n) (choose choice) := by
  refine ⟨choose_minimal choice, ?_⟩
  intro T hT
  have hcover := (sufficient_iff_covers T).mp hT.1
  have hlive : livelist (paired n) T = livelist (paired n) (choose choice) := by
    apply Hma.filtercongr
    intro b _
    rw [decide_eq_decide]
    exact ⟨fun _ => live_of_covers _ (choose_covers choice) b, fun _ => live_of_covers T hcover b⟩
  exact Or.inr ⟨hT.1.trans (choose_minimal choice).1.symm, by simp only [lam, hlive, Nat.le_refl]⟩

theorem minimal_is_choice {n : Nat} (S : Axis n → Bool) (h : minimal (paired n) S) :
    ∃ choice : Fin n → Bool, S = choose choice := by
  let choice : Fin n → Bool := fun i => if S (i, false) then false else true
  have hcovers := (sufficient_iff_covers S).mp h.1
  have hsub : subset (paired n) (choose choice) S := by
    rintro ⟨i, b⟩ _ hb
    by_cases hf : S (i, false) = true
    · have hbf : b = false := by simpa [choose, choice, hf] using hb
      subst b
      exact hf
    · have hbt : b = true := by simpa [choose, choice, hf] using hb
      subst b
      exact (hcovers i).resolve_left hf
  refine ⟨choice, ?_⟩
  funext a
  cases hs : S a <;> cases ht : choose choice a
  · rfl
  · have hbad := hsub a (axes_complete n a) ht
    simp [hs] at hbad
  · have hproper : proper (paired n) (choose choice) S :=
      ⟨hsub, a, axes_complete n a, hs, ht⟩
    exact False.elim (h.2 (choose choice) hproper (choose_minimal choice).1)
  · rfl

theorem choose_injective {n : Nat} (f g : Fin n → Bool) (h : choose f = choose g) : f = g := by
  funext i
  have hi := congrArg (fun S => S (i, f i)) h
  simpa [choose] using hi.symm

def functions : (n : Nat) → List (Fin n → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 => (functions n).map (fun f => Fin.cases false f) ++
      (functions n).map (fun f => Fin.cases true f)

theorem functions_length (n : Nat) : (functions n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [functions, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem functions_nodup (n : Nat) : (functions n).Nodup := by
  induction n with
  | zero => simp [functions]
  | succ n ih =>
    have inj : ∀ (b : Bool) (f g : Fin n → Bool),
        (Fin.cases b f : Fin (n + 1) → Bool) = Fin.cases b g → f = g := by
      intro b f g h
      funext i
      exact congrArg (fun v => v i.succ) h
    apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply List.pairwise_map.mpr
      exact ih.imp (fun {_ _} hne heq => hne (inj false _ _ heq))
    · apply List.pairwise_map.mpr
      exact ih.imp (fun {_ _} hne heq => hne (inj true _ _ heq))
    · intro f hf g hg heq
      obtain ⟨f', _, hff⟩ := List.mem_map.mp hf
      obtain ⟨g', _, hgg⟩ := List.mem_map.mp hg
      rw [← hff, ← hgg] at heq
      have hbad := congrArg (fun v => v 0) heq
      simp at hbad

theorem functions_complete (n : Nat) (f : Fin n → Bool) : f ∈ functions n := by
  induction n with
  | zero =>
    have heq : f = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    simp [functions, heq]
  | succ n ih =>
    have heq : (Fin.cases (f 0) (fun i => f i.succ) : Fin (n + 1) → Bool) = f := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    cases hb : f 0
    · apply List.mem_append_left
      exact List.mem_map.mpr ⟨_, ih _, by simpa [hb] using heq⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr ⟨_, ih _, by simpa [hb] using heq⟩

def minima (n : Nat) : List (Axis n → Bool) := (functions n).map choose

theorem minima_length (n : Nat) : (minima n).length = 2 ^ n := by
  simp only [minima, List.length_map, functions_length]

theorem minima_nodup (n : Nat) : (minima n).Nodup := by
  apply List.pairwise_map.mpr
  exact (functions_nodup n).imp (fun {_ _} hne heq => hne (choose_injective _ _ heq))

theorem minimal_iff_mem_minima (n : Nat) (S : Axis n → Bool) :
    minimal (paired n) S ↔ S ∈ minima n := by
  constructor
  · intro h
    obtain ⟨choice, rfl⟩ := minimal_is_choice S h
    exact List.mem_map_of_mem (functions_complete n choice)
  · intro h
    obtain ⟨choice, _, rfl⟩ := List.mem_map.mp h
    exact choose_minimal choice

theorem highest_iff_mem_minima (n : Nat) (S : Axis n → Bool) :
    highest (paired n) S ↔ S ∈ minima n := by
  constructor
  · intro h
    exact (minimal_iff_mem_minima n S).mp h.1
  · intro h
    obtain ⟨choice, _, rfl⟩ := List.mem_map.mp h
    exact choose_highest choice

theorem axes_length (n : Nat) : (paired n).axes.length = 2 * n := by
  simp only [paired, axes, List.length_append, List.length_ofFn]
  omega

theorem contract_length (n : Nat) : (paired n).contract.length = 2 * n + 1 := by
  simp only [paired, axes, List.length_cons, List.length_map, List.length_append, List.length_ofFn]
  omega

theorem unitRow_injective {n : Nat} (x y : Axis n) (h : unitRow x = unitRow y) : x = y := by
  have hx := congrArg (fun f => f x) h
  simpa [unitRow] using hx.symm

theorem contract_nodup (n : Nat) : (paired n).contract.Nodup := by
  apply List.nodup_cons.mpr
  constructor
  · intro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    have hbad := congrArg (fun f => f a) ha
    simp [unitRow, zeroRow] at hbad
  · apply List.pairwise_map.mpr
    exact (axes_nodup n).imp (fun {_ _} hne heq => hne (unitRow_injective _ _ heq))

theorem exponential_minimal_family (n : Nat) :
    (paired n).axes.length = 2 * n ∧ (paired n).contract.length = 2 * n + 1 ∧
    (paired n).contract.Nodup ∧
    (minima n).Nodup ∧ (minima n).length = 2 ^ n ∧
    (∀ S, S ∈ minima n ↔ minimal (paired n) S) ∧
    (∀ S, S ∈ minima n ↔ highest (paired n) S) := by
  exact ⟨axes_length n, contract_length n, contract_nodup n, minima_nodup n, minima_length n,
    fun S => (minimal_iff_mem_minima n S).symm,
    fun S => (highest_iff_mem_minima n S).symm⟩

end HmaExponential
