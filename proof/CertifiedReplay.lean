import ExecutableWitness
import CertifiedTable
import HmaGraph

/- The carried value contains a materialized witness table and its invariant.
   Admission checks reconstructible current input, not historical identity. -/

namespace HmaReplay

open Hma HmaIncremental HmaExecutable HmaCertified

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]
  [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B]

abbrev Certified (I : Inst A V B W) := { state : State A V B // Valid I state }

def start (I : Inst A V B W) (hn : I.comps.Nodup) : Certified I :=
  ⟨rebuild I I.contract, rebuild_valid I hn I.contract⟩

def insertRows (I : Inst A V B W) (state : Certified I) :
    List (A → V) → Certified I × Nat
  | [] => (state, 0)
  | x :: xs =>
    let next : Certified I := ⟨HmaExecutable.append I state.val x,
      append_valid I state.val state.property x⟩
    let result := insertRows I next xs
    (result.1, state.val.rows.length + result.2)

def eraseRows (I : Inst A V B W) (state : Certified I) :
    List (A → V) → Option (Certified I × Nat)
  | [] => some (state, 0)
  | x :: xs =>
    match step : HmaExecutable.remove I state.val x with
    | none => none
    | some next =>
      let carried : Certified I := ⟨next, remove_valid I state.val next state.property x step⟩
      (eraseRows I carried xs).map (fun result => (result.1, next.rows.length + result.2))

def insertWork : Nat → Nat → Nat
  | _, 0 => 0
  | n, k + 1 => n + insertWork (n + 1) k

def eraseWork : Nat → Nat → Nat
  | _, 0 => 0
  | n, k + 1 => (n - 1) + eraseWork (n - 1) k

theorem insertRows_length (I : Inst A V B W) (state : Certified I) (xs : List (A → V)) :
    (insertRows I state xs).1.val.rows.length = state.val.rows.length + xs.length := by
  induction xs generalizing state with
  | nil => simp [insertRows]
  | cons x xs ih =>
    let next : Certified I := ⟨HmaExecutable.append I state.val x,
      append_valid I state.val state.property x⟩
    change (insertRows I next xs).1.val.rows.length = state.val.rows.length + (x :: xs).length
    rw [ih]
    change (state.val.rows.length + 1) + xs.length = state.val.rows.length + (xs.length + 1)
    omega

theorem insertRows_work (I : Inst A V B W) (state : Certified I) (xs : List (A → V)) :
    (insertRows I state xs).2 = insertWork state.val.rows.length xs.length := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih =>
    let next : Certified I := ⟨HmaExecutable.append I state.val x,
      append_valid I state.val state.property x⟩
    change state.val.rows.length + (insertRows I next xs).2 =
      insertWork state.val.rows.length (xs.length + 1)
    rw [ih, insertWork]
    rfl

theorem insertWork_closed (n k : Nat) :
    insertWork n k = n * k + cumulativePairs k := by
  induction k generalizing n with
  | zero => simp [insertWork, cumulativePairs]
  | succ k ih =>
    rw [insertWork, ih]
    simp only [cumulativePairs, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem insertRows_cumulative_pairs (I : Inst A V B W) (state : Certified I)
    (xs : List (A → V)) :
    (insertRows I state xs).2 + (pairs state.val.rows).length =
      (pairs (insertRows I state xs).1.val.rows).length := by
  induction xs generalizing state with
  | nil => simp [insertRows]
  | cons x xs ih =>
    let next : Certified I := ⟨HmaExecutable.append I state.val x,
      append_valid I state.val state.property x⟩
    change (state.val.rows.length + (insertRows I next xs).2) + (pairs state.val.rows).length = _
    have h := ih next
    change (insertRows I next xs).2 + (pairs (x :: state.val.rows)).length = _ at h
    simpa only [pairs, List.length_append, List.length_map, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using h

omit [LawfulBEq A] [LawfulBEq B] in
theorem remove_rows_length (I : Inst A V B W) (state next : State A V B)
    (x : A → V) (h : HmaExecutable.remove I state x = some next) :
    next.rows.length + 1 = state.rows.length := by
  unfold HmaExecutable.remove at h
  cases hr : removeConfig I x state.rows with
  | none => simp [hr] at h
  | some rows =>
    have heq : (⟨rows, removeKeys state.hist (rowKeys I x rows)⟩ : State A V B) = next := by
      simpa [hr] using h
    obtain ⟨before, after, hrows, hremaining⟩ := removeConfig_decompose I x state.rows rows hr
    rw [← heq]
    simp only [hrows, hremaining, List.length_append, List.length_cons]
    omega

theorem eraseRows_metrics (I : Inst A V B W) (state next : Certified I)
    (xs : List (A → V)) (work : Nat) (h : eraseRows I state xs = some (next, work)) :
    next.val.rows.length + xs.length = state.val.rows.length ∧
      work = eraseWork state.val.rows.length xs.length := by
  induction xs generalizing state next work with
  | nil =>
    have heq : (state, 0) = (next, work) := Option.some.inj h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact ⟨by simp, rfl⟩
  | cons x xs ih =>
    rw [eraseRows] at h
    split at h
    next hs => cases h
    next mid hs =>
      let carried : Certified I := ⟨mid, remove_valid I state.val mid state.property x hs⟩
      have hn := remove_rows_length I state.val mid x hs
      change (eraseRows I carried xs).map (fun result => (result.1, mid.rows.length + result.2)) =
        some (next, work) at h
      cases ht : eraseRows I carried xs with
      | none => simp [ht] at h
      | some result =>
        obtain ⟨last, tailwork⟩ := result
        have heq : (last, mid.rows.length + tailwork) = (next, work) := by
          simpa [ht] using h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        obtain ⟨hrows, hwork⟩ := ih carried last tailwork ht
        have hsub : state.val.rows.length - 1 = mid.rows.length := by omega
        constructor
        · change last.val.rows.length + xs.length = mid.rows.length at hrows
          simp only [List.length_cons]
          omega
        · change mid.rows.length + tailwork = eraseWork state.val.rows.length (xs.length + 1)
          rw [eraseWork, hsub]
          exact congrArg (mid.rows.length + ·) hwork

theorem insertWork_telescopes (n k : Nat) :
    insertWork n k + cumulativePairs n = cumulativePairs (n + k) := by
  induction k generalizing n with
  | zero => simp [insertWork]
  | succ k ih =>
    have hi := ih (n + 1)
    rw [insertWork]
    have heq : n + (k + 1) = (n + 1) + k := by omega
    rw [heq, ← hi]
    change n + insertWork (n + 1) k + cumulativePairs n =
      insertWork (n + 1) k + (cumulativePairs n + n)
    omega

theorem eraseWork_telescopes (n k : Nat) (h : k ≤ n) :
    eraseWork n k + cumulativePairs (n - k) = cumulativePairs n := by
  induction k generalizing n with
  | zero => simp [eraseWork]
  | succ k ih =>
    cases n with
    | zero => omega
    | succ n =>
      have hi := ih n (Nat.le_of_succ_le_succ h)
      simp only [eraseWork, Nat.add_sub_cancel, Nat.add_sub_add_right, cumulativePairs]
      omega

theorem eraseRows_cumulative_pairs (I : Inst A V B W) (state next : Certified I)
    (xs : List (A → V)) (work : Nat) (h : eraseRows I state xs = some (next, work)) :
    work + (pairs next.val.rows).length = (pairs state.val.rows).length := by
  obtain ⟨hlen, hwork⟩ := eraseRows_metrics I state next xs work h
  have hle : xs.length ≤ state.val.rows.length := by omega
  have hremaining : state.val.rows.length - xs.length = next.val.rows.length := by omega
  rw [hwork, pairs_length, pairs_length]
  simpa only [hremaining] using eraseWork_telescopes state.val.rows.length xs.length hle

def move (old new : Inst A V B W) (state : Certified old) : Option (Certified new) :=
  if h : Compatible old new state.val.rows then
    some ⟨state.val, compatible_valid old new state.val state.property h⟩
  else none

omit [LawfulBEq A] in
theorem move_rows (old new : Inst A V B W) (state : Certified old) (next : Certified new)
    (h : move old new state = some next) : next.val.rows = state.val.rows := by
  unfold move at h
  split at h
  · have heq := Option.some.inj h
    exact (congrArg (fun s : Certified new => s.val.rows) heq).symm
  · simp at h

def present (I : Inst A V B W) (rows : List (A → V)) (x : A → V) : Bool :=
  rows.any (fun y => configEq I x y)

def keep (old new : Inst A V B W) (x : A → V) : Bool :=
  present new new.contract x && decide (∀ b ∈ old.comps, old.beh x b = new.beh x b)

def reconcile (old new : Inst A V B W) (state : Certified old) :
    Option (Certified new × Nat × Nat) := do
  let withdrawn := state.val.rows.filter (fun x => !(keep old new x))
  let (retained, removals) ← eraseRows old state withdrawn
  let transferred ← move old new retained
  let additions := new.contract.filter (fun x => !(present new transferred.val.rows x))
  let (next, insertions) := insertRows new transferred additions
  return (next, insertions, removals)

theorem reconcile_pair_balance (old new : Inst A V B W) (state : Certified old)
    (next : Certified new) (insertions removals : Nat)
    (h : reconcile old new state = some (next, insertions, removals)) :
    (pairs next.val.rows).length + removals =
      (pairs state.val.rows).length + insertions := by
  cases he : eraseRows old state (state.val.rows.filter (fun x => !(keep old new x))) with
  | none => simp [reconcile, he] at h
  | some result =>
    obtain ⟨retained, removed⟩ := result
    cases hm : move old new retained with
    | none => simp [reconcile, he, hm] at h
    | some transferred =>
      let additions := new.contract.filter (fun x => !(present new transferred.val.rows x))
      have hout : ((insertRows new transferred additions).1,
          (insertRows new transferred additions).2, removed) = (next, insertions, removals) := by
        simpa [reconcile, he, hm, additions] using h
      obtain ⟨hnext, hwork⟩ := Prod.mk.inj hout
      obtain ⟨hadded, hremoved⟩ := Prod.mk.inj hwork
      have hi := insertRows_cumulative_pairs new transferred additions
      have hr := eraseRows_cumulative_pairs old state retained
        (state.val.rows.filter (fun x => !(keep old new x))) removed he
      have hs := move_rows old new retained transferred hm
      rw [hnext, hadded, hs] at hi
      rw [hremoved] at hr
      omega

def RowsMatch (I : Inst A V B W) (rows : List (A → V)) : Prop :=
  (∀ x ∈ rows, present I I.contract x = true) ∧
    (∀ x ∈ I.contract, present I rows x = true)

instance rowsMatchDec (I : Inst A V B W) (rows : List (A → V)) :
    Decidable (RowsMatch I rows) := by
  unfold RowsMatch
  infer_instance

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem present_iff (I : Inst A V B W) (rows : List (A → V)) (x : A → V) :
    present I rows x = true ↔ x ∈ rows := by
  simp only [present, List.any_eq_true, configEq_true_iff]
  exact ⟨fun ⟨y, hy, h⟩ => h ▸ hy, fun h => ⟨x, h, rfl⟩⟩

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem rowsMatch_membership (I : Inst A V B W) (rows : List (A → V))
    (h : RowsMatch I rows) (x : A → V) : x ∈ rows ↔ x ∈ I.contract := by
  exact ⟨fun hx => (present_iff I I.contract x).mp (h.1 x hx),
    fun hx => (present_iff I rows x).mp (h.2 x hx)⟩

theorem start_rowsMatch (I : Inst A V B W) (hn : I.comps.Nodup) :
    RowsMatch I (start I hn).val.rows := by
  change RowsMatch I (rebuild I I.contract).rows
  rw [rebuild_rows]
  exact ⟨fun x hx => (present_iff I I.contract x).mpr hx,
    fun x hx => (present_iff I I.contract x).mpr hx⟩

omit [LawfulBEq A] in
theorem matched_liveness (I : Inst A V B W) (state : Certified I)
    (h : RowsMatch I state.val.rows) : Exact I (liveList I state.val) := by
  intro S
  rw [liveList_exact I state.val state.property S]
  apply Hma.filtercongr
  intro b _
  apply decide_eq_decide.mpr
  unfold Hma.live withContract
  simp only [rowsMatch_membership I state.val.rows h]

def occupancy (I : Inst A V B W) (state : State A V B)
    (S : A → Bool) (b : B) : Nat :=
  (sublists I.axes).countP (fun D => decide
    ((∀ a ∈ D, S a = true) ∧ 0 < read state.hist (D, b)))

omit [LawfulBEq A] in
theorem occupancy_exact (I : Inst A V B W) (state : State A V B)
    (h : Valid I state) (S : A → Bool) (b : B) (hb : b ∈ I.comps) :
    occupancy I state S b = HmaIncremental.occupiedCount I state.rows b S := by
  unfold occupancy HmaIncremental.occupiedCount
  apply List.countP_congr
  intro D _
  simp only [h.2.2 D b, hb, if_true]

structure Output (I : Inst A V B W) where
  value : Rendered A B
  correct : RenderCorrect I value

def finish (I : Inst A V B W) (state : Certified I)
    (prefer : List A → List A → Bool) : Option (Output I) :=
  if h : RowsMatch I state.val.rows then
    some ⟨render I (liveList I state.val) prefer,
      render_correct I (liveList I state.val) (matched_liveness I state h) prefer⟩
  else none

def solve (I : Inst A V B W) (hn : I.comps.Nodup)
    (prefer : List A → List A → Bool) : Output I :=
  { value := render I (liveList I (start I hn).val) prefer
    correct := render_correct I _ (matched_liveness I (start I hn) (start_rowsMatch I hn)) prefer }

theorem finish_start (I : Inst A V B W) (hn : I.comps.Nodup)
    (prefer : List A → List A → Bool) :
    finish I (start I hn) prefer = some (solve I hn prefer) := by
  unfold finish
  rw [dif_pos (start_rowsMatch I hn)]
  rfl

omit [LawfulBEq A] in
theorem finish_value (I : Inst A V B W) (state : Certified I)
    (prefer : List A → List A → Bool) (output : Output I)
    (h : finish I state prefer = some output) :
    output.value = render I (liveList I state.val) prefer := by
  unfold finish at h
  split at h
  · exact (congrArg Output.value (Option.some.inj h)).symm
  · simp at h

theorem finish_lex_minimum {n : Nat} (I : Inst (Fin n) V B W) (state : Certified I)
    (output : Output I) (selected : List (Fin n))
    (h : finish I state finLexPrefer = some output)
    (hc : output.value.chosen = some selected) :
    ∀ other ∈ output.value.highest,
      ¬ List.Lex (fun a b : Fin n => a.val < b.val) other selected := by
  have heq := finish_value I state finLexPrefer output h
  rw [heq] at hc ⊢
  exact render_chosen_lex_minimum I (liveList I state.val) selected hc

theorem solve_chosen (I : Inst A V B W) (hn : I.comps.Nodup)
    (prefer : List A → List A → Bool) :
    ∃ l, (solve I hn prefer).value.chosen = some l ∧ Hma.highest I (HmaCheck.axisSet l) :=
  (solve I hn prefer).correct.chosen

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem finish_sound (I : Inst A V B W) (output : Output I) :
    RenderCorrect I output.value := output.correct

omit [LawfulBEq A] in
theorem certified_hypergraph (I : Inst A V B W) (state : Certified I)
    (h : RowsMatch I state.val.rows) (S : A → Bool) (b : B) (hb : b ∈ I.comps) :
    b ∈ liveList I state.val S ↔
      HypergraphIncremental.derives (HmaGraph.graph I S) (.live b) := by
  rw [matched_liveness I state h S, HmaGraph.live_exact I S b]
  simp only [livelist, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun hl => ⟨hb, hl⟩⟩

structure Session (I : Inst A V B W) where
  state : Certified I
  nextSeq : Nat
  epoch : Nat

def advance (old new : Inst A V B W) (session : Session old) (seq epoch : Nat) :
    Option (Session new × Nat × Nat) :=
  if seq = session.nextSeq ∧ epoch = session.epoch then
    (reconcile old new session.state).map (fun (state, work) =>
      (⟨state, session.nextSeq + 1, session.epoch⟩, work))
  else none

def rebase {A' V' B' W' : Type} [DecidableEq A'] [DecidableEq B']
    [DecidableEq V'] [DecidableEq W']
    [BEq A'] [LawfulBEq A'] [Hashable A'] [BEq B'] [LawfulBEq B'] [Hashable B']
    (old : Inst A V B W) (new : Inst A' V' B' W') (hn : new.comps.Nodup)
    (session : Session old) (seq epoch : Nat) : Option (Session new) :=
  if seq = session.nextSeq ∧ epoch = session.epoch then
    some ⟨start new hn, session.nextSeq + 1, session.epoch + 1⟩
  else none

theorem accepted_advance_clock (old new : Inst A V B W) (session : Session old)
    (seq epoch : Nat) (next : Session new) (insertions removals : Nat)
    (h : advance old new session seq epoch = some (next, insertions, removals)) :
    seq = session.nextSeq ∧ epoch = session.epoch ∧
      next.nextSeq = session.nextSeq + 1 ∧ next.epoch = session.epoch := by
  unfold advance at h
  split at h
  · rename_i hclock
    cases hr : reconcile old new session.state with
    | none => simp [hr] at h
    | some result =>
      obtain ⟨carried, work⟩ := result
      have heq : (⟨carried, session.nextSeq + 1, session.epoch⟩, work) =
          (next, insertions, removals) := by simpa [hr] using h
      exact ⟨hclock.1, hclock.2,
        (congrArg (fun x : Session new × Nat × Nat => x.1.nextSeq) heq).symm,
        (congrArg (fun x : Session new × Nat × Nat => x.1.epoch) heq).symm⟩
  · simp at h

omit [LawfulBEq A] in
theorem accepted_rebase_clock {A' V' B' W' : Type} [DecidableEq A'] [DecidableEq B']
    [DecidableEq V'] [DecidableEq W']
    [BEq A'] [LawfulBEq A'] [Hashable A'] [BEq B'] [LawfulBEq B'] [Hashable B']
    (old : Inst A V B W) (new : Inst A' V' B' W') (hn : new.comps.Nodup)
    (session : Session old) (seq epoch : Nat) (next : Session new)
    (h : rebase old new hn session seq epoch = some next) :
    seq = session.nextSeq ∧ epoch = session.epoch ∧
      next.nextSeq = session.nextSeq + 1 ∧ next.epoch = session.epoch + 1 := by
  unfold rebase at h
  split at h
  · rename_i hclock
    have heq : (⟨start new hn, session.nextSeq + 1, session.epoch + 1⟩ : Session new) = next :=
      Option.some.inj h
    exact ⟨hclock.1, hclock.2, (congrArg Session.nextSeq heq).symm,
      (congrArg Session.epoch heq).symm⟩
  · simp at h

theorem stale_sequence_rejected (old new : Inst A V B W) (session : Session old)
    (seq epoch : Nat) (h : seq ≠ session.nextSeq) :
    advance old new session seq epoch = none := by
  simp [advance, h]

theorem stale_epoch_rejected (old new : Inst A V B W) (session : Session old)
    (seq epoch : Nat) (h : epoch ≠ session.epoch) :
    advance old new session seq epoch = none := by
  simp [advance, h]

omit [LawfulBEq A] in
theorem stale_rebase_rejected {A' V' B' W' : Type} [DecidableEq A'] [DecidableEq B']
    [DecidableEq V'] [DecidableEq W']
    [BEq A'] [LawfulBEq A'] [Hashable A'] [BEq B'] [LawfulBEq B'] [Hashable B']
    (old : Inst A V B W) (new : Inst A' V' B' W') (hn : new.comps.Nodup)
    (session : Session old) (seq epoch : Nat)
    (h : seq ≠ session.nextSeq ∨ epoch ≠ session.epoch) :
    rebase old new hn session seq epoch = none := by
  rcases h with h | h <;> simp [rebase, h]

end HmaReplay
