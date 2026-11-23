import ExecutableWitness

/- Finite certificates for serialized histogram deltas. Kernel reduction
   checks list entries and the changed row's contributions. Library lookup
   lemmas connect those checks to the actual materialized hash table. -/

namespace HmaCertificate

open Hma HmaIncremental HmaExecutable

section Entries

variable {K : Type} [DecidableEq K] [BEq K] [LawfulBEq K] [Hashable K]

def deltaSupport (before after : List (K × Nat)) (keys : List K) : List K :=
  before.map Prod.fst ++ keys ++ after.map Prod.fst

def acceptsDelta (before after : List (K × Nat)) (keys : List K) (removing : Bool) : Bool :=
  (deltaSupport before after keys).all (fun key => decide
    (entryValue after key = if removing then
      entryValue before key - occurrences keys key else
      entryValue before key + occurrences keys key))

omit [DecidableEq K] [Hashable K] in
theorem entryValue_zero (entries : List (K × Nat)) (key : K)
    (h : key ∉ entries.map Prod.fst) : entryValue entries key = 0 := by
  have hf : entries.find? (fun p => p.1 == key) = none := by
    apply List.find?_eq_none.mpr
    intro p hp heq
    exact h (List.mem_map.mpr ⟨p, hp, eq_of_beq heq⟩)
  unfold entryValue
  rw [hf]
  rfl

omit [BEq K] [LawfulBEq K] [Hashable K] in
theorem occurrences_zero (keys : List K) (key : K) (h : key ∉ keys) :
    occurrences keys key = 0 := by
  apply List.countP_eq_zero.mpr
  intro other ho heq
  have equal : other = key := of_decide_eq_true heq
  exact h (equal ▸ ho)

omit [Hashable K] in
theorem acceptsDelta_sound (before after : List (K × Nat)) (keys : List K)
    (removing : Bool) (h : acceptsDelta before after keys removing = true) (key : K) :
    entryValue after key = if removing then
      entryValue before key - occurrences keys key else
      entryValue before key + occurrences keys key := by
  by_cases hk : key ∈ deltaSupport before after keys
  · exact of_decide_eq_true (List.all_eq_true.mp h key hk)
  · have hb : key ∉ before.map Prod.fst := by
      intro hm
      exact hk (by simp [deltaSupport, hm])
    have ha : key ∉ after.map Prod.fst := by
      intro hm
      exact hk (by simp [deltaSupport, hm])
    have hd : key ∉ keys := by
      intro hm
      exact hk (by simp [deltaSupport, hm])
    rw [entryValue_zero before key hb, entryValue_zero after key ha,
      occurrences_zero keys key hd]
    cases removing <;> rfl

theorem checked_add (before after : List (K × Nat)) (keys : List K)
    (hb : before.Pairwise (fun p q => (p.1 == q.1) = false))
    (ha : after.Pairwise (fun p q => (p.1 == q.1) = false))
    (accepted : acceptsDelta before after keys false = true) (key : K) :
    read (addKeys (Std.HashMap.ofList before) keys) key =
      read (Std.HashMap.ofList after) key := by
  rw [read_addKeys, read_ofList before hb, read_ofList after ha]
  exact (acceptsDelta_sound before after keys false accepted key).symm

theorem checked_remove (before after : List (K × Nat)) (keys : List K)
    (hb : before.Pairwise (fun p q => (p.1 == q.1) = false))
    (ha : after.Pairwise (fun p q => (p.1 == q.1) = false))
    (accepted : acceptsDelta before after keys true = true) (key : K) :
    read (removeKeys (Std.HashMap.ofList before) keys) key =
      read (Std.HashMap.ofList after) key := by
  rw [read_removeKeys, read_ofList before hb, read_ofList after ha]
  exact (acceptsDelta_sound before after keys true accepted key).symm

end Entries

variable {A V B W : Type} [DecidableEq A] [DecidableEq B]
  [DecidableEq V] [DecidableEq W]
  [BEq A] [LawfulBEq A] [Hashable A] [BEq B] [LawfulBEq B] [Hashable B]

def liveEntries (I : Inst A V B W) (entries : List (Key A B × Nat))
    (S : A → Bool) : List B :=
  I.comps.filter (fun b => (sublists I.axes).any (fun D =>
    decide ((∀ a ∈ D, S a = true) ∧ 0 < entryValue entries (D, b))))

theorem liveEntries_eq (I : Inst A V B W) (state : State A V B)
    (entries : List (Key A B × Nat))
    (hh : state.hist = Std.HashMap.ofList entries)
    (hd : entries.Pairwise (fun p q => (p.1 == q.1) = false)) :
    liveList I state = liveEntries I entries := by
  funext S
  simp only [liveList, liveEntries, hh, read_ofList entries hd]

end HmaCertificate
