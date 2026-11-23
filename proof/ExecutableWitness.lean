import Incremental
import Std.Data.HashMap.Lemmas

/- Materialized executable witness counts. A state contains active rows and
   a finite hash table of positive multiplicities. Transitions update that
   table directly; they do not store past states or deferred computations. -/

namespace HmaExecutable

open Hma HmaIncremental

section Histogram

variable {K : Type} [DecidableEq K] [BEq K] [LawfulBEq K] [Hashable K]

abbrev Histogram (K : Type) [BEq K] [Hashable K] := Std.HashMap K Nat

def read (h : Histogram K) (key : K) : Nat := h.getD key 0

def increment (h : Histogram K) (key : K) : Histogram K :=
  h.insert key (read h key + 1)

def decrement (h : Histogram K) (key : K) : Histogram K :=
  if read h key ≤ 1 then h.erase key else h.insert key (read h key - 1)

def addKeys (h : Histogram K) : List K → Histogram K
  | [] => h
  | key :: keys => addKeys (increment h key) keys

def removeKeys (h : Histogram K) : List K → Histogram K
  | [] => h
  | key :: keys => removeKeys (decrement h key) keys

def occurrences (keys : List K) (key : K) : Nat :=
  keys.countP (fun k => decide (k = key))

def Sparse (h : Histogram K) : Prop := ∀ key, key ∈ h → 0 < read h key

omit [DecidableEq K] [LawfulBEq K] in
theorem read_empty (key : K) : read (∅ : Histogram K) key = 0 := by
  simp [read]

theorem read_increment (h : Histogram K) (key query : K) :
    read (increment h key) query = read h query + if key = query then 1 else 0 := by
  by_cases heq : key = query
  · subst key
    simp [read, increment]
  · simp [read, increment, Std.HashMap.getD_insert, beq_iff_eq, heq]

theorem read_decrement (h : Histogram K) (key query : K) :
    read (decrement h key) query = read h query - if key = query then 1 else 0 := by
  by_cases hs : read h key ≤ 1
  · rw [decrement, if_pos hs]
    by_cases heq : key = query
    · subst key
      simp only [read, Std.HashMap.getD_erase_self, ite_true]
      change h.getD query 0 ≤ 1 at hs
      omega
    · simp [read, Std.HashMap.getD_erase, beq_iff_eq, heq]
  · rw [decrement, if_neg hs]
    by_cases heq : key = query
    · subst key
      simp [read]
    · simp [read, Std.HashMap.getD_insert, beq_iff_eq, heq]

theorem read_addKeys (h : Histogram K) (keys : List K) (query : K) :
    read (addKeys h keys) query = read h query + occurrences keys query := by
  induction keys generalizing h with
  | nil => simp [addKeys, occurrences]
  | cons key keys ih =>
    rw [addKeys, ih, read_increment]
    simp only [occurrences, List.countP_cons, decide_eq_true_eq]
    split <;> omega

theorem read_removeKeys (h : Histogram K) (keys : List K) (query : K) :
    read (removeKeys h keys) query = read h query - occurrences keys query := by
  induction keys generalizing h with
  | nil => simp [removeKeys, occurrences]
  | cons key keys ih =>
    rw [removeKeys, ih, read_decrement]
    simp only [occurrences, List.countP_cons, decide_eq_true_eq]
    split <;> omega

omit [DecidableEq K] [LawfulBEq K] in
theorem sparse_empty : Sparse (∅ : Histogram K) := by
  intro key h
  simp at h

theorem sparse_increment (h : Histogram K) (hs : Sparse h) (key : K) :
    Sparse (increment h key) := by
  intro query hq
  rw [read_increment]
  by_cases heq : key = query
  · simp [heq]
  · have hm : query ∈ h := by
      simpa [increment, Std.HashMap.mem_insert, beq_iff_eq, heq] using hq
    simp [heq, hs query hm]

theorem sparse_decrement (h : Histogram K) (hs : Sparse h) (key : K) :
    Sparse (decrement h key) := by
  intro query hq
  rw [read_decrement]
  by_cases heq : key = query
  · subst key
    by_cases hsmall : read h query ≤ 1
    · simp [decrement, hsmall] at hq
    · simp only [ite_true]
      omega
  · have hm : query ∈ h := by
      by_cases hsmall : read h key ≤ 1
      · exact Std.HashMap.mem_of_mem_erase (by simpa [decrement, hsmall] using hq)
      · simpa [decrement, hsmall, Std.HashMap.mem_insert, beq_iff_eq, heq] using hq
    simpa [heq] using hs query hm

theorem sparse_addKeys (h : Histogram K) (hs : Sparse h) (keys : List K) : Sparse (addKeys h keys) := by
  induction keys generalizing h with
  | nil => exact hs
  | cons key keys ih => exact ih (increment h key) (sparse_increment h hs key)

theorem sparse_removeKeys (h : Histogram K) (hs : Sparse h) (keys : List K) : Sparse (removeKeys h keys) := by
  induction keys generalizing h with
  | nil => exact hs
  | cons key keys ih => exact ih (decrement h key) (sparse_decrement h hs key)

omit [Hashable K] in
theorem occurrences_nodup (keys : List K) (hn : keys.Nodup) (query : K) :
    occurrences keys query = if query ∈ keys then 1 else 0 := by
  induction keys with
  | nil => simp [occurrences]
  | cons key keys ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    simp only [occurrences, List.countP_cons, decide_eq_true_eq] at *
    rw [ih htail]
    by_cases heq : key = query
    · subst key
      simp [hnot]
    · simp [heq, Ne.symm heq, List.mem_cons]

omit [DecidableEq K] in
theorem sparse_read_equiv (left right : Histogram K) (hl : Sparse left) (hr : Sparse right)
    (hread : ∀ key, read left key = read right key) : left.Equiv right := by
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro key
  by_cases hleft : key ∈ left
  · have hright : key ∈ right := by
      by_cases hm : key ∈ right
      · exact hm
      · have hz : read right key = 0 := Std.HashMap.getD_eq_fallback hm
        have hp := hl key hleft
        rw [hread key, hz] at hp
        omega
    rw [Std.HashMap.getElem?_eq_some_getD (fallback := 0) hleft,
      Std.HashMap.getElem?_eq_some_getD (fallback := 0) hright]
    exact congrArg some (hread key)
  · have hright : ¬key ∈ right := by
      intro hm
      have hz : read left key = 0 := Std.HashMap.getD_eq_fallback hleft
      have hp := hr key hm
      rw [← hread key, hz] at hp
      omega
    rw [Std.HashMap.getElem?_eq_none hleft, Std.HashMap.getElem?_eq_none hright]

omit [DecidableEq K] [Hashable K] in
theorem nodup_subset_length (left right : List K) (hn : left.Nodup)
    (hsub : ∀ key ∈ left, key ∈ right) : left.length ≤ right.length := by
  induction left generalizing right with
  | nil => exact Nat.zero_le _
  | cons key keys ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    have hm : key ∈ right := hsub key (by simp)
    have hsub' : ∀ k ∈ keys, k ∈ right.erase key := by
      intro k hk
      have hne : k ≠ key := by
        intro heq
        subst k
        exact hnot hk
      exact (List.mem_erase_of_ne hne).mpr (hsub k (List.mem_cons_of_mem key hk))
    have hh := ih (right.erase key) htail hsub'
    rw [List.length_erase_of_mem hm] at hh
    have hpos := List.length_pos_of_mem hm
    simp only [List.length_cons]
    omega

def entryValue (entries : List (K × Nat)) (key : K) : Nat :=
  ((entries.find? (fun p => p.1 == key)).map Prod.snd).getD 0

omit [DecidableEq K] in
theorem read_ofList (entries : List (K × Nat))
    (hd : entries.Pairwise (fun p q => (p.1 == q.1) = false)) (key : K) :
    read (Std.HashMap.ofList entries) key = entryValue entries key := by
  cases hf : entries.find? (fun p => p.1 == key) with
  | none =>
    have hn : (entries.map Prod.fst).contains key = false := by
      apply Bool.eq_false_iff.mpr
      intro hc
      obtain ⟨p, hp, hpk⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
      exact (List.find?_eq_none.mp hf) p hp (by simp [hpk])
    have he : (Std.HashMap.ofList entries).getD key 0 = 0 :=
      Std.HashMap.getD_ofList_of_contains_eq_false hn
    simpa [read, entryValue, hf] using he
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hk := List.find?_some hf
    have he : (Std.HashMap.ofList entries).getD key 0 = p.2 :=
      Std.HashMap.getD_ofList_of_mem hk hd hp
    simpa [read, entryValue, hf] using he

omit [DecidableEq K] in
theorem sparse_ofList (entries : List (K × Nat))
    (hd : entries.Pairwise (fun p q => (p.1 == q.1) = false))
    (hp : ∀ p ∈ entries, 0 < p.2) : Sparse (Std.HashMap.ofList entries) := by
  intro key hkey
  obtain ⟨p, hmem, hpk⟩ := List.mem_map.mp
    (List.contains_iff_mem.mp (Std.HashMap.mem_ofList.mp hkey))
  have he : (Std.HashMap.ofList entries).getD key 0 = p.2 :=
    Std.HashMap.getD_ofList_of_mem (show p.1 == key from by simp [hpk]) hd hmem
  change 0 < (Std.HashMap.ofList entries).getD key 0
  rw [he]
  exact hp p hmem

end Histogram

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]
  [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B]

abbrev Key (A B : Type) := List A × B

structure State (A V B : Type) [BEq A] [Hashable A] [BEq B] [Hashable B] where
  rows : List (A → V)
  hist : Histogram (Key A B)

def pairKeys (I : Inst A V B W) (x y : A → V) : List (Key A B) :=
  let diff := difference I x y
  (I.comps.filter (fun b => decide (I.beh x b ≠ I.beh y b))).map (fun b => (diff, b))

def rowKeys (I : Inst A V B W) (x : A → V) (rows : List (A → V)) : List (Key A B) :=
  rows.flatMap (pairKeys I x)

def empty : State A V B := ⟨[], ∅⟩

def append (I : Inst A V B W) (state : State A V B) (x : A → V) : State A V B :=
  ⟨x :: state.rows, addKeys state.hist (rowKeys I x state.rows)⟩

def remove (I : Inst A V B W) (state : State A V B) (x : A → V) : Option (State A V B) :=
  (removeConfig I x state.rows).map (fun rows => ⟨rows, removeKeys state.hist (rowKeys I x rows)⟩)

def rebuild (I : Inst A V B W) : List (A → V) → State A V B
  | [] => empty
  | x :: xs => append I (rebuild I xs) x

def Valid (I : Inst A V B W) (state : State A V B) : Prop :=
  I.comps.Nodup ∧ Sparse state.hist ∧ ∀ D b,
    read state.hist (D, b) = if b ∈ I.comps then exactCount I state.rows D b else 0

def liveList (I : Inst A V B W) (state : State A V B) (S : A → Bool) : List B :=
  I.comps.filter (fun b => (sublists I.axes).any (fun D =>
    decide ((∀ a ∈ D, S a = true) ∧ 0 < read state.hist (D, b))))

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem pairKeys_mem (I : Inst A V B W) (x y : A → V) (D : List A) (b : B) :
    (D, b) ∈ pairKeys I x y ↔ b ∈ I.comps ∧ difference I x y = D ∧ I.beh x b ≠ I.beh y b := by
  simp only [pairKeys, List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨c, ⟨hc, hchange⟩, hdiff, hcb⟩
    subst c
    exact ⟨hc, hdiff, hchange⟩
  · rintro ⟨hb, hd, hchange⟩
    exact ⟨b, ⟨hb, hchange⟩, hd, rfl⟩

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem pairKeys_nodup (I : Inst A V B W) (hn : I.comps.Nodup) (x y : A → V) :
    (pairKeys I x y).Nodup := by
  apply List.pairwise_map.mpr
  have hf := List.Sublist.nodup (List.filter_sublist (p := fun b => decide (I.beh x b ≠ I.beh y b))) hn
  exact hf.imp (fun {_ _} hne heq => hne (Prod.mk.inj heq).2)

omit [Hashable A] [Hashable B] in
theorem rowKeys_occurrences (I : Inst A V B W) (hn : I.comps.Nodup)
    (x : A → V) (rows : List (A → V)) (D : List A) (b : B) :
    occurrences (rowKeys I x rows) (D, b) = if b ∈ I.comps then
      rows.countP (fun y => decide (difference I x y = D ∧ I.beh x b ≠ I.beh y b)) else 0 := by
  induction rows with
  | nil => simp [rowKeys, occurrences]
  | cons y ys ih =>
    change occurrences (pairKeys I x y ++ rowKeys I x ys) (D, b) = _
    rw [show occurrences (pairKeys I x y ++ rowKeys I x ys) (D, b) =
      occurrences (pairKeys I x y) (D, b) + occurrences (rowKeys I x ys) (D, b) from List.countP_append]
    rw [occurrences_nodup _ (pairKeys_nodup I hn x y), ih]
    simp only [pairKeys_mem]
    by_cases hb : b ∈ I.comps <;>
      simp only [hb, if_true, if_false, true_and, false_and, List.countP_cons, decide_eq_true_eq] <;> omega

omit [LawfulBEq A] in
theorem empty_valid (I : Inst A V B W) (hn : I.comps.Nodup) : Valid I (empty : State A V B) := by
  refine ⟨hn, sparse_empty, ?_⟩
  intro D b
  simp [empty, read_empty, exactCount, pairs]

theorem append_valid (I : Inst A V B W) (state : State A V B)
    (h : Valid I state) (x : A → V) : Valid I (append I state x) := by
  refine ⟨h.1, sparse_addKeys state.hist h.2.1 _, ?_⟩
  intro D b
  change read (addKeys state.hist (rowKeys I x state.rows)) (D, b) = _
  rw [read_addKeys, h.2.2 D b, rowKeys_occurrences I h.1]
  by_cases hb : b ∈ I.comps <;> simp [hb, append, exactCount_add_row]

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem difference_symm (I : Inst A V B W) (x y : A → V) : difference I x y = difference I y x := by
  apply Hma.filtercongr
  intro a _
  rw [decide_eq_decide]
  exact ⟨Ne.symm, Ne.symm⟩

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem exactPair_symm (I : Inst A V B W) (D : List A) (b : B) (x y : A → V) :
    decide (difference I x y = D ∧ I.beh x b ≠ I.beh y b) =
      decide (difference I y x = D ∧ I.beh y b ≠ I.beh x b) := by
  rw [difference_symm I x y, decide_eq_decide]
  exact and_congr_right (fun _ => ⟨Ne.symm, Ne.symm⟩)

omit [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem exactCount_remove_middle (I : Inst A V B W) (before after : List (A → V))
    (x : A → V) (D : List A) (b : B) :
    exactCount I (before ++ x :: after) D b = exactCount I (before ++ after) D b +
      (before ++ after).countP (fun y => decide (difference I x y = D ∧ I.beh x b ≠ I.beh y b)) := by
  induction before with
  | nil => exact exactCount_add_row I after x D b
  | cons y ys ih =>
    simp only [List.cons_append, exactCount_add_row]
    rw [ih]
    simp only [List.countP_append, List.countP_cons]
    rw [exactPair_symm I D b y x]
    omega

theorem remove_valid (I : Inst A V B W) (state next : State A V B)
    (h : Valid I state) (x : A → V) (hstep : remove I state x = some next) : Valid I next := by
  unfold remove at hstep
  cases hr : removeConfig I x state.rows with
  | none => simp [hr] at hstep
  | some rows =>
    have hn : (⟨rows, removeKeys state.hist (rowKeys I x rows)⟩ : State A V B) = next := by
      simpa [hr] using hstep
    subst next
    obtain ⟨before, after, hrows, hremaining⟩ := removeConfig_decompose I x state.rows rows hr
    refine ⟨h.1, sparse_removeKeys state.hist h.2.1 _, ?_⟩
    intro D b
    change read (removeKeys state.hist (rowKeys I x rows)) (D, b) = _
    rw [read_removeKeys, h.2.2 D b, rowKeys_occurrences I h.1]
    by_cases hb : b ∈ I.comps
    · simp only [hb, if_true]
      rw [hrows, hremaining, exactCount_remove_middle]
      omega
    · simp [hb]

theorem rebuild_valid (I : Inst A V B W) (hn : I.comps.Nodup) (rows : List (A → V)) :
    Valid I (rebuild I rows) := by
  induction rows with
  | nil => exact empty_valid I hn
  | cons x rows ih => exact append_valid I (rebuild I rows) ih x

omit [LawfulBEq A] [LawfulBEq B] in
theorem rebuild_rows (I : Inst A V B W) (rows : List (A → V)) : (rebuild I rows).rows = rows := by
  induction rows with
  | nil => rfl
  | cons x rows ih => simp only [rebuild, append, ih]

omit [LawfulBEq A] in
theorem liveList_exact (I : Inst A V B W) (state : State A V B)
    (h : Valid I state) (S : A → Bool) :
    liveList I state S = Hma.livelist (withContract I state.rows) S := by
  apply Hma.filtercongr
  intro b hb
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, decide_eq_true_eq]
  have hlookup : ∀ D, read state.hist (D, b) = exactCount I state.rows D b := by
    intro D
    simpa [hb] using h.2.2 D b
  simp only [hlookup]
  have hexact := occupiedCount_positive_iff I state.rows b S
  simpa only [occupiedCount, List.countP_pos_iff, decide_eq_true_eq] using hexact

theorem valid_transport (I : Inst A V B W) (source target : State A V B)
    (h : Valid I source) (hrows : source.rows = target.rows)
    (hmap : source.hist.Equiv target.hist) : Valid I target := by
  refine ⟨h.1, ?_, ?_⟩
  · intro key hkey
    have hread : read source.hist key = read target.hist key := hmap.getD_eq
    rw [← hread]
    exact h.2.1 key (hmap.mem_iff.mpr hkey)
  · intro D b
    have hread : read source.hist (D, b) = read target.hist (D, b) := hmap.getD_eq
    rw [← hread, h.2.2, hrows]

omit [LawfulBEq A] in
theorem valid_transport_read (I : Inst A V B W) (source target : State A V B)
    (h : Valid I source) (hrows : source.rows = target.rows) (hs : Sparse target.hist)
    (hread : ∀ key, read source.hist key = read target.hist key) : Valid I target := by
  refine ⟨h.1, hs, ?_⟩
  intro D b
  rw [← hread (D, b), h.2.2 D b, hrows]

omit [DecidableEq A] [DecidableEq V] [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem pairs_endpoints (rows : List (A → V)) (p : (A → V) × (A → V))
    (h : p ∈ pairs rows) : p.1 ∈ rows ∧ p.2 ∈ rows := by
  induction rows with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact ⟨by simp, by simp [hy]⟩
    · obtain ⟨hleft, hright⟩ := ih h
      exact ⟨List.mem_cons_of_mem x hleft, List.mem_cons_of_mem x hright⟩

def Compatible (old new : Inst A V B W) (rows : List (A → V)) : Prop :=
  old.axes = new.axes ∧ old.comps = new.comps ∧
    ∀ x ∈ rows, ∀ b ∈ old.comps, old.beh x b = new.beh x b

instance compatibleDec (old new : Inst A V B W) (rows : List (A → V)) :
    Decidable (Compatible old new rows) := by
  unfold Compatible
  infer_instance

omit [LawfulBEq A] in
theorem compatible_valid (old new : Inst A V B W) (state : State A V B)
    (h : Valid old state) (hc : Compatible old new state.rows) : Valid new state := by
  refine ⟨hc.2.1 ▸ h.1, h.2.1, ?_⟩
  intro D b
  rw [h.2.2 D b, hc.2.1]
  by_cases hb : b ∈ new.comps
  · simp only [hb, if_true]
    unfold exactCount
    apply List.countP_congr
    intro p hp
    obtain ⟨hl, hr⟩ := pairs_endpoints state.rows p hp
    have hb' : b ∈ old.comps := hc.2.1 ▸ hb
    simp only [difference, hc.1, hc.2.2 p.1 hl b hb', hc.2.2 p.2 hr b hb']
  · simp [hb]

def requalify (old new : Inst A V B W) (state : State A V B) : Option (State A V B) :=
  if Compatible old new state.rows then some state else none

omit [LawfulBEq A] in
theorem requalify_valid (old new : Inst A V B W) (state next : State A V B)
    (h : Valid old state) (hstep : requalify old new state = some next) : Valid new next := by
  unfold requalify at hstep
  split at hstep
  · rename_i hc
    have heq : state = next := Option.some.inj hstep
    rw [← heq]
    exact compatible_valid old new state h hc
  · simp at hstep

def appendBatch (I : Inst A V B W) (state : State A V B) : List (A → V) → State A V B
  | [] => state
  | x :: xs => appendBatch I (append I state x) xs

theorem appendBatch_valid (I : Inst A V B W) (state : State A V B)
    (h : Valid I state) (rows : List (A → V)) : Valid I (appendBatch I state rows) := by
  induction rows generalizing state with
  | nil => exact h
  | cons x xs ih => exact ih (append I state x) (append_valid I state h x)

def removeRows (I : Inst A V B W) (state : State A V B) : List (A → V) → Option (State A V B)
  | [] => some state
  | x :: xs => (remove I state x).bind (fun next => removeRows I next xs)

theorem removeRows_valid (I : Inst A V B W) (state next : State A V B)
    (h : Valid I state) (rows : List (A → V)) (hstep : removeRows I state rows = some next) :
    Valid I next := by
  induction rows generalizing state with
  | nil =>
    have heq : state = next := Option.some.inj hstep
    exact heq ▸ h
  | cons x xs ih =>
    cases hs : remove I state x with
    | none => simp [removeRows, hs] at hstep
    | some mid =>
      apply ih mid (remove_valid I state mid h x hs)
      simpa [removeRows, hs] using hstep

def step (I : Inst A V B W) (state : State A V B) : RowEvent A V → Option (State A V B)
  | .insert x => some (append I state x)
  | .remove x => remove I state x

theorem step_valid (I : Inst A V B W) (state next : State A V B)
    (h : Valid I state) (event : RowEvent A V) (hstep : step I state event = some next) : Valid I next := by
  cases event with
  | insert x =>
    have heq : append I state x = next := Option.some.inj hstep
    exact heq ▸ append_valid I state h x
  | remove x => exact remove_valid I state next h x hstep

def replay (I : Inst A V B W) (state : State A V B) : List (RowEvent A V) → Option (State A V B)
  | [] => some state
  | event :: events => (step I state event).bind (fun next => replay I next events)

theorem replay_valid (I : Inst A V B W) (state next : State A V B)
    (h : Valid I state) (events : List (RowEvent A V)) (hstep : replay I state events = some next) :
    Valid I next := by
  induction events generalizing state with
  | nil =>
    have heq : state = next := Option.some.inj hstep
    exact heq ▸ h
  | cons event events ih =>
    cases hs : step I state event with
    | none => simp [replay, hs] at hstep
    | some mid =>
      apply ih mid (step_valid I state mid h event hs)
      simpa [replay, hs] using hstep

theorem every_prefix_exact (I : Inst A V B W) (state next : State A V B)
    (h : Valid I state) (events : List (RowEvent A V)) (n : Nat)
    (hstep : replay I state (events.take n) = some next) (S : A → Bool) :
    liveList I next S = Hma.livelist (withContract I next.rows) S :=
  liveList_exact I next (replay_valid I state next h (events.take n) hstep) S

def Equivalent (left right : State A V B) : Prop :=
  left.rows = right.rows ∧ left.hist.Equiv right.hist

theorem valid_equivalent (I : Inst A V B W) (left right : State A V B)
    (hl : Valid I left) (hr : Valid I right) (hrows : left.rows = right.rows) : Equivalent left right := by
  refine ⟨hrows, sparse_read_equiv left.hist right.hist hl.2.1 hr.2.1 ?_⟩
  rintro ⟨D, b⟩
  rw [hl.2.2 D b, hr.2.2 D b, hrows]

def checkpoint (I : Inst A V B W) (state : State A V B) : State A V B := rebuild I state.rows

theorem checkpoint_valid (I : Inst A V B W) (state : State A V B) (h : Valid I state) :
    Valid I (checkpoint I state) := rebuild_valid I h.1 state.rows

theorem checkpoint_equivalent (I : Inst A V B W) (state : State A V B) (h : Valid I state) :
    Equivalent (checkpoint I state) state :=
  valid_equivalent I _ _ (checkpoint_valid I state h) h (rebuild_rows I state.rows)

def SameResult (left right : Option (State A V B)) : Prop :=
  match left, right with
  | none, none => True
  | some l, some r => Equivalent l r
  | _, _ => False

theorem step_equivalent (I : Inst A V B W) (left right : State A V B)
    (hl : Valid I left) (hr : Valid I right) (heq : Equivalent left right) (event : RowEvent A V) :
    SameResult (step I left event) (step I right event) := by
  cases event with
  | insert x =>
    apply valid_equivalent I _ _ (append_valid I left hl x) (append_valid I right hr x)
    simp only [append, heq.1]
  | remove x =>
    cases hs : removeConfig I x left.rows with
    | none => simp [step, remove, hs, ← heq.1, SameResult]
    | some rows =>
      have hleft : remove I left x = some ⟨rows, removeKeys left.hist (rowKeys I x rows)⟩ := by
        simp [remove, hs]
      have hright : remove I right x = some ⟨rows, removeKeys right.hist (rowKeys I x rows)⟩ := by
        simp [remove, ← heq.1, hs]
      change SameResult (remove I left x) (remove I right x)
      rw [hleft, hright]
      exact valid_equivalent I _ _ (remove_valid I _ _ hl x hleft) (remove_valid I _ _ hr x hright) rfl

theorem replay_equivalent (I : Inst A V B W) (left right : State A V B)
    (hl : Valid I left) (hr : Valid I right) (heq : Equivalent left right)
    (events : List (RowEvent A V)) : SameResult (replay I left events) (replay I right events) := by
  induction events generalizing left right with
  | nil => exact heq
  | cons event events ih =>
    have hs := step_equivalent I left right hl hr heq event
    cases hleft : step I left event with
    | none =>
      cases hright : step I right event with
      | none => simp [replay, hleft, hright, SameResult]
      | some r => simp [hleft, hright, SameResult] at hs
    | some l =>
      cases hright : step I right event with
      | none => simp [hleft, hright, SameResult] at hs
      | some r =>
        have heq' : Equivalent l r := by simpa [hleft, hright, SameResult] using hs
        simpa [replay, hleft, hright] using
          ih l r (step_valid I _ _ hl event hleft) (step_valid I _ _ hr event hright) heq'

theorem checkpoint_replay (I : Inst A V B W) (state : State A V B)
    (h : Valid I state) (future : List (RowEvent A V)) :
    SameResult (replay I (checkpoint I state) future) (replay I state future) :=
  replay_equivalent I _ _ (checkpoint_valid I state h) h (checkpoint_equivalent I state h) future

omit [LawfulBEq A] in
theorem stored_key_current (I : Inst A V B W) (state : State A V B) (h : Valid I state)
    (D : List A) (b : B) (hm : (D, b) ∈ state.hist) :
    D ∈ sublists I.axes ∧ b ∈ I.comps := by
  have hp := h.2.1 (D, b) hm
  rw [h.2.2 D b] at hp
  by_cases hb : b ∈ I.comps
  · simp only [hb, if_true, exactCount, List.countP_pos_iff, decide_eq_true_eq] at hp
    obtain ⟨p, _, hd, _⟩ := hp
    exact ⟨hd ▸ Hma.filtermemsublists _ I.axes, hb⟩
  · simp [hb] at hp

omit [DecidableEq A] [DecidableEq B] [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B] in
theorem product_keys_length (domains : List (List A)) (components : List B) :
    (domains.flatMap (fun D => components.map (fun b => (D, b)))).length =
      domains.length * components.length := by
  induction domains with
  | nil => simp
  | cons D domains ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih,
      Nat.add_mul, Nat.one_mul]
    omega

theorem stored_cells_bound (I : Inst A V B W) (state : State A V B) (h : Valid I state) :
    state.hist.size ≤ (sublists I.axes).length * I.comps.length := by
  rw [← Std.HashMap.length_keys, ← product_keys_length]
  apply nodup_subset_length
  · exact Std.HashMap.distinct_keys.imp (fun {_ _} hne heq => by simp [heq] at hne)
  · rintro ⟨D, b⟩ hmem
    have hm : (D, b) ∈ state.hist := Std.HashMap.mem_keys.mp hmem
    obtain ⟨hd, hb⟩ := stored_key_current I state h D b hm
    exact List.mem_flatMap.mpr ⟨D, hd, List.mem_map.mpr ⟨b, hb, rfl⟩⟩

end HmaExecutable
