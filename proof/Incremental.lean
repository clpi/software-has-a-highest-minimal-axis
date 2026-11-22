import FiniteCheck
import Init.Data.List.Count

/- Incremental row-pair witnesses for the original Hma predicates.
   The retained rows, rather than an unbounded event history, determine what
   future observations can be reconstructed. All equalities in this file are
   mathematical model equalities; the external implementation is checked. -/

namespace HmaIncremental

open Hma

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]

def withContract (I : Inst A V B W) (rows : List (A → V)) : Inst A V B W :=
  { I with contract := rows }

def difference (I : Inst A V B W) (x y : A → V) : List A :=
  I.axes.filter (fun a => decide (x a ≠ y a))

theorem difference_iff_agreeoff (I : Inst A V B W) (x y : A → V) (S : A → Bool) :
    (∀ a ∈ difference I x y, S a = true) ↔ agreeoff I x y S := by
  constructor
  · intro h a ha hfalse
    by_cases heq : x a = y a
    · exact heq
    · have ht := h a (List.mem_filter.mpr ⟨ha, by simpa using heq⟩)
      simp [hfalse] at ht
  · intro h a ha
    obtain ⟨hin, hne⟩ := List.mem_filter.mp ha
    have hn : x a ≠ y a := by simpa using hne
    cases hs : S a
    · exact False.elim (hn (h a hin hs))
    · rfl

abbrev pairChanges (I : Inst A V B W) (b : B) (S : A → Bool)
    (x y : A → V) : Prop := agreeoff I x y S ∧ I.beh x b ≠ I.beh y b

instance pairChangesDec (I : Inst A V B W) (b : B) (S : A → Bool)
    (x y : A → V) : Decidable (pairChanges I b S x y) := by
  unfold pairChanges agreeoff
  infer_instance

theorem pairChanges_symm (I : Inst A V B W) (b : B) (S : A → Bool)
    {x y : A → V} (h : pairChanges I b S x y) : pairChanges I b S y x := by
  exact ⟨fun a ha hs => (h.1 a ha hs).symm, Ne.symm h.2⟩

theorem pairChanges_irrefl (I : Inst A V B W) (b : B) (S : A → Bool)
    (x : A → V) : ¬ pairChanges I b S x x := by
  intro h
  exact h.2 rfl

def pairs {α : Type} : List α → List (α × α)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ pairs xs

theorem pairs_cover {α : Type} (P : α → α → Prop)
    (hsymm : ∀ x y, P x y → P y x) (hirrefl : ∀ x, ¬ P x x)
    (xs : List α) :
    (∃ p ∈ pairs xs, P p.1 p.2) ↔ ∃ x ∈ xs, ∃ y ∈ xs, P x y := by
  induction xs with
  | nil => simp [pairs]
  | cons a xs ih =>
    constructor
    · rintro ⟨p, hp, hP⟩
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨y, hy, heq⟩ := List.mem_map.mp hp
        subst p
        exact ⟨a, by simp, y, by simp [hy], hP⟩
      · obtain ⟨x, hx, y, hy, hxy⟩ := ih.mp ⟨p, hp, hP⟩
        exact ⟨x, by simp [hx], y, by simp [hy], hxy⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      rcases List.mem_cons.mp hx with heq | hx
      · subst x
        rcases List.mem_cons.mp hy with heq | hy
        · subst y
          exact False.elim (hirrefl a hxy)
        · exact ⟨(a, y), List.mem_append_left _ (List.mem_map_of_mem hy), hxy⟩
      · rcases List.mem_cons.mp hy with heq | hy
        · subst y
          exact ⟨(a, x), List.mem_append_left _ (List.mem_map_of_mem hx), hsymm x a hxy⟩
        · obtain ⟨p, hp, hP⟩ := ih.mpr ⟨x, hx, y, hy, hxy⟩
          exact ⟨p, List.mem_append_right _ hp, hP⟩

def supportCount (I : Inst A V B W) (rows : List (A → V)) (b : B) (S : A → Bool) : Nat :=
  (pairs rows).countP (fun p => decide (pairChanges I b S p.1 p.2))

theorem supportCount_positive_iff (I : Inst A V B W) (rows : List (A → V))
    (b : B) (S : A → Bool) :
    0 < supportCount I rows b S ↔ live (withContract I rows) b S := by
  rw [supportCount, List.countP_pos_iff]
  simp only [decide_eq_true_eq]
  exact pairs_cover (pairChanges I b S)
    (fun _ _ => pairChanges_symm I b S) (pairChanges_irrefl I b S) rows

def rowContribution (I : Inst A V B W) (rows : List (A → V)) (x : A → V)
    (b : B) (S : A → Bool) : Nat :=
  rows.countP (fun y => decide (pairChanges I b S x y))

theorem supportCount_add_row (I : Inst A V B W) (rows : List (A → V))
    (x : A → V) (b : B) (S : A → Bool) :
    supportCount I (x :: rows) b S = rowContribution I rows x b S + supportCount I rows b S := by
  simp [supportCount, pairs, rowContribution, List.countP_map, Function.comp_def]

theorem supportCount_remove_row (I : Inst A V B W) (rows : List (A → V))
    (x : A → V) (b : B) (S : A → Bool) :
    supportCount I (x :: rows) b S - rowContribution I rows x b S = supportCount I rows b S := by
  rw [supportCount_add_row]
  omega

theorem live_add_row (I : Inst A V B W) (rows : List (A → V)) (x : A → V)
    (b : B) (S : A → Bool) :
    live (withContract I (x :: rows)) b S ↔
      live (withContract I rows) b S ∨ ∃ y ∈ rows, pairChanges I b S x y := by
  rw [← supportCount_positive_iff, supportCount_add_row,
    ← supportCount_positive_iff]
  have hc : 0 < rowContribution I rows x b S ↔ ∃ y ∈ rows, pairChanges I b S x y := by
    simp only [rowContribution, List.countP_pos_iff, decide_eq_true_eq]
  rw [← hc]
  omega

theorem outside_difference_unchanged (I : Inst A V B W) (x y : A → V)
    (b : B) (S : A → Bool) (h : ¬ ∀ a ∈ difference I x y, S a = true) :
    ¬ pairChanges I b S x y := by
  intro hp
  exact h ((difference_iff_agreeoff I x y S).mpr hp.1)

def exactCount (I : Inst A V B W) (rows : List (A → V)) (D : List A) (b : B) : Nat :=
  (pairs rows).countP (fun p => decide
    (difference I p.1 p.2 = D ∧ I.beh p.1 b ≠ I.beh p.2 b))

def occupiedCount (I : Inst A V B W) (rows : List (A → V))
    (b : B) (S : A → Bool) : Nat :=
  (sublists I.axes).countP (fun D => decide
    ((∀ a ∈ D, S a = true) ∧ 0 < exactCount I rows D b))

theorem occupiedCount_positive_iff (I : Inst A V B W) (rows : List (A → V))
    (b : B) (S : A → Bool) :
    0 < occupiedCount I rows b S ↔ live (withContract I rows) b S := by
  rw [← supportCount_positive_iff, supportCount, occupiedCount,
    List.countP_pos_iff, List.countP_pos_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨D, _, hD, hc⟩
    simp only [exactCount, List.countP_pos_iff, decide_eq_true_eq] at hc
    obtain ⟨p, hp, hdiff, hchange⟩ := hc
    exact ⟨p, hp, (difference_iff_agreeoff I p.1 p.2 S).mp (hdiff ▸ hD), hchange⟩
  · rintro ⟨p, hp, hagree, hchange⟩
    refine ⟨difference I p.1 p.2, Hma.filtermemsublists _ _,
      (difference_iff_agreeoff I p.1 p.2 S).mpr hagree, ?_⟩
    apply List.countP_pos_iff.mpr
    refine ⟨p, hp, ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨True.intro, hchange⟩

theorem exactCount_add_row (I : Inst A V B W) (rows : List (A → V))
    (x : A → V) (D : List A) (b : B) :
    exactCount I (x :: rows) D b = exactCount I rows D b +
      rows.countP (fun y => decide (difference I x y = D ∧ I.beh x b ≠ I.beh y b)) := by
  simp [exactCount, pairs, List.countP_map, Function.comp_def, Nat.add_comm]

theorem occupied_ignores_positive_multiplicity (I : Inst A V B W)
    (left right : List (A → V))
    (h : ∀ D b, 0 < exactCount I left D b ↔ 0 < exactCount I right D b)
    (b : B) (S : A → Bool) : occupiedCount I left b S = occupiedCount I right b S := by
  unfold occupiedCount
  apply congrArg (fun p => (sublists I.axes).countP p)
  funext D
  rw [decide_eq_decide, h]

structure Cache (A V B : Type) where
  rows : List (A → V)
  counts : B → (A → Bool) → Nat

def reconstruct (I : Inst A V B W) (rows : List (A → V)) : Cache A V B :=
  ⟨rows, supportCount I rows⟩

def appendRow (I : Inst A V B W) (state : Cache A V B) (x : A → V) : Cache A V B :=
  ⟨x :: state.rows, fun b S => rowContribution I state.rows x b S + state.counts b S⟩

abbrev Valid (I : Inst A V B W) (state : Cache A V B) : Prop :=
  ∀ b S, state.counts b S = supportCount I state.rows b S

theorem reconstruct_valid (I : Inst A V B W) (rows : List (A → V)) :
    Valid I (reconstruct I rows) := by
  intro b S
  rfl

theorem appendRow_valid (I : Inst A V B W) (state : Cache A V B)
    (h : Valid I state) (x : A → V) : Valid I (appendRow I state x) := by
  intro b S
  change rowContribution I state.rows x b S + state.counts b S =
    supportCount I (x :: state.rows) b S
  rw [h, supportCount_add_row]

def replayRows (I : Inst A V B W) (state : Cache A V B) : List (A → V) → Cache A V B
  | [] => state
  | x :: xs => replayRows I (appendRow I state x) xs

theorem replayRows_valid (I : Inst A V B W) (state : Cache A V B)
    (h : Valid I state) (events : List (A → V)) : Valid I (replayRows I state events) := by
  induction events generalizing state with
  | nil => exact h
  | cons x xs ih => exact ih (appendRow I state x) (appendRow_valid I state h x)

theorem every_prefix_exact (I : Inst A V B W) (state : Cache A V B)
    (h : Valid I state) (events : List (A → V)) (n : Nat) (b : B) (S : A → Bool) :
    0 < (replayRows I state (events.take n)).counts b S ↔
      live (withContract I (replayRows I state (events.take n)).rows) b S := by
  rw [replayRows_valid I state h, supportCount_positive_iff]

theorem replayRows_append (I : Inst A V B W) (state : Cache A V B)
    (left right : List (A → V)) :
    replayRows I state (left ++ right) = replayRows I (replayRows I state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons x xs ih => exact ih (appendRow I state x)

theorem valid_reconstruct_eq (I : Inst A V B W) (state : Cache A V B)
    (h : Valid I state) : reconstruct I state.rows = state := by
  cases state with
  | mk rows counts =>
    have heq : supportCount I rows = counts := by
      funext b S
      exact (h b S).symm
    simp only [reconstruct, heq]

theorem checkpoint_replay (I : Inst A V B W) (state : Cache A V B)
    (h : Valid I state) (future : List (A → V)) :
    replayRows I (reconstruct I state.rows) future = replayRows I state future := by
  rw [valid_reconstruct_eq I state h]

theorem pairChanges_decide_symm (I : Inst A V B W) (b : B) (S : A → Bool)
    (x y : A → V) : decide (pairChanges I b S x y) = decide (pairChanges I b S y x) := by
  rw [decide_eq_decide]
  exact ⟨pairChanges_symm I b S, pairChanges_symm I b S⟩

theorem supportCount_remove_middle (I : Inst A V B W) (before after : List (A → V))
    (x : A → V) (b : B) (S : A → Bool) :
    supportCount I (before ++ x :: after) b S =
      rowContribution I (before ++ after) x b S + supportCount I (before ++ after) b S := by
  induction before with
  | nil => exact supportCount_add_row I after x b S
  | cons y ys ih =>
    simp only [List.cons_append, supportCount_add_row]
    rw [ih]
    simp only [rowContribution, List.countP_append, List.countP_cons]
    rw [pairChanges_decide_symm I b S y x]
    omega

def configEq (I : Inst A V B W) (x y : A → V) : Bool :=
  decide (∀ a ∈ I.axes, x a = y a)

theorem configEq_true_iff (I : Inst A V B W) (x y : A → V) : configEq I x y = true ↔ x = y := by
  simp only [configEq, decide_eq_true_eq]
  exact ⟨fun h => funext (fun a => h a (I.axescomplete a)), fun h => by simp [h]⟩

def removeConfig (I : Inst A V B W) (x : A → V) : List (A → V) → Option (List (A → V))
  | [] => none
  | y :: ys => if configEq I x y then some ys else (removeConfig I x ys).map (y :: ·)

theorem removeConfig_decompose (I : Inst A V B W) (x : A → V)
    (rows remaining : List (A → V)) (h : removeConfig I x rows = some remaining) :
    ∃ before after, rows = before ++ x :: after ∧ remaining = before ++ after := by
  induction rows generalizing remaining with
  | nil => simp [removeConfig] at h
  | cons y ys ih =>
    by_cases heq : configEq I x y = true
    · have hxy := (configEq_true_iff I x y).mp heq
      have hr : ys = remaining := by simpa [removeConfig, heq] using h
      subst y
      exact ⟨[], ys, rfl, hr.symm⟩
    · simp only [removeConfig, if_neg heq] at h
      cases hr : removeConfig I x ys with
      | none => simp [hr] at h
      | some tail =>
        have hremain : y :: tail = remaining := by simpa [hr] using h
        obtain ⟨before, after, hrows, htail⟩ := ih tail hr
        exact ⟨y :: before, after, by simp [hrows], by simp [← hremain, htail]⟩

def removeRow (I : Inst A V B W) (state : Cache A V B) (x : A → V) : Option (Cache A V B) :=
  (removeConfig I x state.rows).map (fun rows =>
    ⟨rows, fun b S => state.counts b S - rowContribution I rows x b S⟩)

theorem removeRow_valid (I : Inst A V B W) (state next : Cache A V B)
    (h : Valid I state) (x : A → V) (hstep : removeRow I state x = some next) : Valid I next := by
  unfold removeRow at hstep
  cases hr : removeConfig I x state.rows with
  | none => simp [hr] at hstep
  | some rows =>
    have hn : (⟨rows, fun b S => state.counts b S - rowContribution I rows x b S⟩ : Cache A V B) = next := by
      simpa [hr] using hstep
    subst next
    obtain ⟨before, after, hrows, hremaining⟩ := removeConfig_decompose I x state.rows rows hr
    intro b S
    change state.counts b S - rowContribution I rows x b S = supportCount I rows b S
    rw [h, hrows, hremaining, supportCount_remove_middle]
    omega

inductive RowEvent (A V : Type) where
  | insert : (A → V) → RowEvent A V
  | remove : (A → V) → RowEvent A V

def rowStep (I : Inst A V B W) (state : Cache A V B) : RowEvent A V → Option (Cache A V B)
  | .insert x => some (appendRow I state x)
  | .remove x => removeRow I state x

theorem rowStep_valid (I : Inst A V B W) (state next : Cache A V B)
    (h : Valid I state) (event : RowEvent A V) (hstep : rowStep I state event = some next) : Valid I next := by
  cases event with
  | insert x =>
    have hn : appendRow I state x = next := by simpa [rowStep] using hstep
    rw [← hn]
    exact appendRow_valid I state h x
  | remove x => exact removeRow_valid I state next h x hstep

def replayEvents (I : Inst A V B W) (state : Cache A V B) : List (RowEvent A V) → Option (Cache A V B)
  | [] => some state
  | event :: events => (rowStep I state event).bind (fun next => replayEvents I next events)

theorem replayEvents_valid (I : Inst A V B W) (state next : Cache A V B)
    (h : Valid I state) (events : List (RowEvent A V))
    (hreplay : replayEvents I state events = some next) : Valid I next := by
  induction events generalizing state with
  | nil =>
    have hn : state = next := by simpa [replayEvents] using hreplay
    rw [← hn]
    exact h
  | cons event events ih =>
    cases hs : rowStep I state event with
    | none => simp [replayEvents, hs] at hreplay
    | some mid =>
      apply ih mid (rowStep_valid I state mid h event hs)
      simpa [replayEvents, hs] using hreplay

theorem mixed_every_prefix_exact (I : Inst A V B W) (state next : Cache A V B)
    (h : Valid I state) (events : List (RowEvent A V)) (n : Nat)
    (hreplay : replayEvents I state (events.take n) = some next) (b : B) (S : A → Bool) :
    0 < next.counts b S ↔ live (withContract I next.rows) b S := by
  rw [replayEvents_valid I state next h (events.take n) hreplay,
    supportCount_positive_iff]

theorem checkpoint_mixed_replay (I : Inst A V B W) (state : Cache A V B)
    (h : Valid I state) (future : List (RowEvent A V)) :
    replayEvents I (reconstruct I state.rows) future = replayEvents I state future := by
  rw [valid_reconstruct_eq I state h]

structure StreamState (A V B : Type) where
  nextSeq : Nat
  epoch : Nat
  cache : Cache A V B

def numberedStep (I : Inst A V B W) (state : StreamState A V B)
    (event : Nat × RowEvent A V) : Option (StreamState A V B) :=
  if event.1 = state.nextSeq then
    (rowStep I state.cache event.2).map (fun cache => ⟨state.nextSeq + 1, state.epoch, cache⟩)
  else none

def numberedReplay (I : Inst A V B W) (state : StreamState A V B) :
    List (Nat × RowEvent A V) → Option (StreamState A V B)
  | [] => some state
  | event :: events => (numberedStep I state event).bind (fun next => numberedReplay I next events)

theorem wrong_sequence_rejected (I : Inst A V B W) (state : StreamState A V B)
    (event : Nat × RowEvent A V) (h : event.1 ≠ state.nextSeq) :
    numberedStep I state event = none := by
  simp only [numberedStep, if_neg h]

theorem accepted_sequence_advances (I : Inst A V B W) (state next : StreamState A V B)
    (event : Nat × RowEvent A V) (h : numberedStep I state event = some next) :
    event.1 = state.nextSeq ∧ next.nextSeq = state.nextSeq + 1 ∧ next.epoch = state.epoch := by
  unfold numberedStep at h
  split at h
  · rename_i hseq
    cases hs : rowStep I state.cache event.2 with
    | none => simp [hs] at h
    | some cache =>
      have heq : (⟨state.nextSeq + 1, state.epoch, cache⟩ : StreamState A V B) = next := by
        simpa [hs] using h
      rw [← heq]
      exact ⟨hseq, rfl, rfl⟩
  · simp at h

def streamCheckpoint (I : Inst A V B W) (state : StreamState A V B) : StreamState A V B :=
  ⟨state.nextSeq, state.epoch, reconstruct I state.cache.rows⟩

theorem checkpoint_numbered_replay (I : Inst A V B W) (state : StreamState A V B)
    (h : Valid I state.cache) (future : List (Nat × RowEvent A V)) :
    numberedReplay I (streamCheckpoint I state) future = numberedReplay I state future := by
  have heq : streamCheckpoint I state = state := by
    unfold streamCheckpoint
    rw [valid_reconstruct_eq I state.cache h]
  rw [heq]

/- Current observation equivalence is sufficient for current results. It is
   intentionally not used as the premise of checkpoint_replay. -/

theorem livelist_congr (I : Inst A V B W) (left right : List (A → V))
    (h : ∀ b S, live (withContract I left) b S ↔ live (withContract I right) b S)
    (S : A → Bool) : livelist (withContract I left) S = livelist (withContract I right) S := by
  apply Hma.filtercongr
  intro b _
  rw [decide_eq_decide]
  exact h b S

theorem snapshot_congr (I : Inst A V B W) (left right : List (A → V))
    (h : ∀ b S, live (withContract I left) b S ↔ live (withContract I right) b S)
    (S : A → Bool) : HmaCheck.snapshot (withContract I left) S =
      HmaCheck.snapshot (withContract I right) S := by
  unfold HmaCheck.snapshot
  rw [livelist_congr I left right h S]
  rfl

theorem rho_congr (I : Inst A V B W) (left right : List (A → V))
    (h : ∀ b S, live (withContract I left) b S ↔ live (withContract I right) b S)
    (S : A → Bool) : rho (withContract I left) S = rho (withContract I right) S := by
  rw [← HmaCheck.snapshotMeasure, ← HmaCheck.snapshotMeasure, snapshot_congr I left right h]

theorem sufficient_congr (I : Inst A V B W) (left right : List (A → V))
    (h : ∀ b S, live (withContract I left) b S ↔ live (withContract I right) b S)
    (S : A → Bool) : sufficient (withContract I left) S ↔ sufficient (withContract I right) S := by
  have hmu : ∀ T, mu (withContract I left) T = mu (withContract I right) T :=
    fun T => congrArg Prod.fst (rho_congr I left right h T)
  simp only [sufficient, hmu]

theorem minimal_congr (I : Inst A V B W) (left right : List (A → V))
    (h : ∀ b S, live (withContract I left) b S ↔ live (withContract I right) b S)
    (S : A → Bool) : minimal (withContract I left) S ↔ minimal (withContract I right) S := by
  simp only [minimal, sufficient_congr I left right h]
  rfl

theorem highest_congr (I : Inst A V B W) (left right : List (A → V))
    (h : ∀ b S, live (withContract I left) b S ↔ live (withContract I right) b S)
    (S : A → Bool) : highest (withContract I left) S ↔ highest (withContract I right) S := by
  have hmu : ∀ T, mu (withContract I left) T = mu (withContract I right) T :=
    fun T => congrArg Prod.fst (rho_congr I left right h T)
  have hlam : ∀ T, lam (withContract I left) T = lam (withContract I right) T :=
    fun T => congrArg Prod.snd (rho_congr I left right h T)
  simp only [highest, minimal_congr I left right h, rhole, hmu, hlam]

theorem dead_congr (I : Inst A V B W) (left right : List (A → V))
    (h : ∀ b S, live (withContract I left) b S ↔ live (withContract I right) b S)
    (a : A) : dead (withContract I left) a ↔ dead (withContract I right) a := by
  simp only [dead, livelist_congr I left right h]

end HmaIncremental
