import OptimalController

namespace IncrementalControl

variable {P S A O : Type} [DecidableEq S] [DecidableEq A] [DecidableEq O] [Inhabited A]

abbrev Table (S : Type) := List (S × Nat)

def read (table : Table S) (s : S) : Nat := (table.lookup s).getD 0

def materialize (U : List S) (f : S → Nat) : Table S := U.map (fun s => (s, f s))

theorem lookup_materialize (U : List S) (f : S → Nat) (s : S) (hs : s ∈ U) :
    (materialize U f).lookup s = some (f s) := by
  induction U with
  | nil => simp at hs
  | cons a U ih =>
    by_cases h : s = a
    · subst s; simp [materialize, List.lookup]
    · have hm : s ∈ U := (List.mem_cons.mp hs).resolve_left h
      have hb : (s == a) = false := by simp [h]
      simpa [materialize, List.lookup, hb] using ih hm

theorem read_materialize (U : List S) (f : S → Nat) (s : S) (hs : s ∈ U) :
    read (materialize U f) s = f s := by
  simp [read, lookup_materialize U f s hs]

def localSame (M N : OptimalController.Model P S A O) (p q : P) (s : S) : Bool :=
  decide (M.actions s = N.actions s) &&
  (M.actions s).all (fun a =>
    decide (M.outcomes s a = N.outcomes s a) &&
    (M.outcomes s a).all (fun o =>
      decide (M.next s a o = N.next s a o) &&
      decide (M.cost p s a o = N.cost q s a o)))

omit [Inhabited A] in
theorem localSame_exact (M N : OptimalController.Model P S A O) (p q : P) (s : S) :
    localSame M N p q s = true ↔
      M.actions s = N.actions s ∧
      ∀ a, a ∈ M.actions s → M.outcomes s a = N.outcomes s a ∧
        ∀ o, o ∈ M.outcomes s a →
          M.next s a o = N.next s a o ∧ M.cost p s a o = N.cost q s a o := by
  simp [localSame, List.all_eq_true]

def depends (M : OptimalController.Model P S A O) (changed : List S) (s : S) : Bool :=
  (M.actions s).any (fun a =>
    (M.outcomes s a).any (fun o => changed.contains (M.next s a o)))

omit [DecidableEq A] [DecidableEq O] [Inhabited A] in
theorem depends_false (M : OptimalController.Model P S A O) (changed : List S) (s : S)
    (h : depends M changed s = false) :
    ∀ a, a ∈ M.actions s → ∀ o, o ∈ M.outcomes s a → M.next s a o ∉ changed := by
  simpa [depends, List.any_eq_false, List.contains_iff] using h

structure Layer (S : Type) where
  table : Table S
  changed : List S
  recomputed : List S
  deriving Repr

def changes (U : List S) (old new : Table S) : List S :=
  U.filter (fun s => decide (read old s ≠ read new s))

theorem outside_changes (U : List S) (old new : Table S) (s : S)
    (hs : s ∈ U) (h : s ∉ changes U old new) : read old s = read new s := by
  simpa [changes, hs] using h

def base (U : List S) (old : Table S) (N : OptimalController.Model P S A O) (q : P) : Layer S :=
  let table := materialize U (N.terminal q)
  let changed := changes U old table
  ⟨table, changed, changed⟩

def updateLayer (U : List S) (M N : OptimalController.Model P S A O) (p q : P)
    (old : Table S) (lower : Layer S) : Layer S :=
  let dirty := U.filter (fun s => !localSame M N p q s || depends N lower.changed s)
  let table := materialize U (fun s => if dirty.contains s then
    OptimalController.backup N q (read lower.table) s else read old s)
  ⟨table, changes U old table, dirty⟩

def Exact (M : OptimalController.Model P S A O) (p : P) (h : Nat) (table : Table S) : Prop :=
  ∀ s, read table s = OptimalController.value M p h s

omit [DecidableEq A] [DecidableEq O] in
theorem base_exact (U : List S) (complete : ∀ s, s ∈ U) (old : Table S)
    (N : OptimalController.Model P S A O) (q : P) : Exact N q 0 (base U old N q).table := by
  intro s
  exact read_materialize U (N.terminal q) s (complete s)

theorem updateLayer_exact (U : List S) (complete : ∀ s, s ∈ U)
    (M N : OptimalController.Model P S A O) (p q : P) (h : Nat)
    (old oldLower : Table S) (lower : Layer S)
    (oldExact : Exact M p (h + 1) old) (oldLowerExact : Exact M p h oldLower)
    (newLowerExact : Exact N q h lower.table)
    (sameOutside : ∀ s, s ∉ lower.changed → read oldLower s = read lower.table s) :
    Exact N q (h + 1) (updateLayer U M N p q old lower).table := by
  intro s
  unfold updateLayer
  rw [read_materialize U _ s (complete s)]
  split
  next dirty =>
    apply OptimalController.backup_congr
    intro a ha o ho
    exact newLowerExact _
  next clean =>
    have hc : localSame M N p q s = true ∧ depends N lower.changed s = false := by
      simpa [List.contains_iff, List.mem_filter, complete s, Bool.or_eq_true] using clean
    obtain ⟨actions, same⟩ := (localSame_exact M N p q s).mp hc.1
    rw [oldExact s, OptimalController.value_succ, OptimalController.value_succ]
    apply OptimalController.backup_transfer M N p q _ _ s actions
    · exact fun a ha => (same a ha).1
    · exact fun a ha o ho => ((same a ha).2 o ho).2
    · intro a ha o ho
      have hn : M.next s a o = N.next s a o := ((same a ha).2 o ho).1
      have outside : N.next s a o ∉ lower.changed :=
        depends_false N lower.changed s hc.2 a (actions ▸ ha) o ((same a ha).1 ▸ ho)
      rw [hn, ← oldLowerExact, ← newLowerExact]
      exact sameOutside _ outside

inductive Cache (S : Type) : Nat → Type where
  | zero (top : Layer S) : Cache S 0
  | succ {h : Nat} (top : Layer S) (lower : Cache S h) : Cache S (h + 1)

def Cache.top : {h : Nat} → Cache S h → Layer S
  | _, .zero top => top
  | _, .succ top _ => top

def Cache.Valid (M : OptimalController.Model P S A O) (p : P) :
    {h : Nat} → Cache S h → Prop
  | 0, .zero top => Exact M p 0 top.table
  | h + 1, .succ top lower => Exact M p (h + 1) top.table ∧ lower.Valid M p

omit [DecidableEq A] [DecidableEq O] in
theorem Cache.top_exact (M : OptimalController.Model P S A O) (p : P)
    {h : Nat} (cache : Cache S h) (valid : cache.Valid M p) :
    Exact M p h cache.top.table := by
  cases cache with
  | zero top => exact valid
  | succ top lower => exact valid.1

def build (U : List S) (M : OptimalController.Model P S A O) (p : P) :
    (h : Nat) → Cache S h
  | 0 => .zero (base U [] M p)
  | h + 1 =>
    let lower := build U M p h
    let table := materialize U (OptimalController.backup M p (read lower.top.table))
    .succ ⟨table, U, U⟩ lower

omit [DecidableEq A] [DecidableEq O] in
theorem build_valid (U : List S) (complete : ∀ s, s ∈ U)
    (M : OptimalController.Model P S A O) (p : P) (h : Nat) :
    (build U M p h).Valid M p := by
  induction h with
  | zero => exact base_exact U complete [] M p
  | succ h ih =>
    refine ⟨?_, ih⟩
    intro s
    rw [read_materialize U _ s (complete s)]
    apply OptimalController.backup_congr
    intro a ha o ho
    exact Cache.top_exact M p _ ih _

def refresh (U : List S) (M N : OptimalController.Model P S A O) (p q : P) :
    {h : Nat} → Cache S h → Cache S h
  | 0, .zero top => .zero (base U top.table N q)
  | _ + 1, .succ top lower =>
    let nextLower := refresh U M N p q lower
    .succ (updateLayer U M N p q top.table nextLower.top) nextLower

theorem refresh_changes (U : List S) (M N : OptimalController.Model P S A O) (p q : P)
    {h : Nat} (cache : Cache S h) :
    (refresh U M N p q cache).top.changed =
      changes U cache.top.table (refresh U M N p q cache).top.table := by
  cases cache <;> rfl

theorem refresh_valid (U : List S) (complete : ∀ s, s ∈ U)
    (M N : OptimalController.Model P S A O) (p q : P)
    {h : Nat} (cache : Cache S h) (valid : cache.Valid M p) :
    (refresh U M N p q cache).Valid N q := by
  induction cache with
  | zero top => exact base_exact U complete top.table N q
  | succ top lower ih =>
    have hl := ih valid.2
    refine ⟨?_, hl⟩
    apply updateLayer_exact U complete M N p q _ top.table lower.top.table
      (refresh U M N p q lower).top valid.1
      (Cache.top_exact M p lower valid.2) (Cache.top_exact N q _ hl)
    intro s hs
    apply outside_changes U lower.top.table (refresh U M N p q lower).top.table s (complete s)
    simpa only [refresh_changes] using hs

abbrev Certified (M : OptimalController.Model P S A O) (p : P) (h : Nat) :=
  {cache : Cache S h // cache.Valid M p}

def start (U : List S) (complete : ∀ s, s ∈ U)
    (M : OptimalController.Model P S A O) (p : P) (h : Nat) : Certified M p h :=
  ⟨build U M p h, build_valid U complete M p h⟩

def update (U : List S) (complete : ∀ s, s ∈ U)
    (M N : OptimalController.Model P S A O) (p q : P) {h : Nat}
    (old : Certified M p h) : Certified N q h :=
  ⟨refresh U M N p q old.val, refresh_valid U complete M N p q old.val old.property⟩

def value (M : OptimalController.Model P S A O) (p : P) {h : Nat}
    (cache : Certified M p h) (s : S) : Nat := read cache.val.top.table s

omit [DecidableEq A] [DecidableEq O] in
theorem value_exact (M : OptimalController.Model P S A O) (p : P) {h : Nat}
    (cache : Certified M p h) (s : S) :
    value M p cache s = OptimalController.value M p h s :=
  Cache.top_exact M p cache.val cache.property s

omit [DecidableEq A] [DecidableEq O] in
theorem value_optimal (M : OptimalController.Model P S A O) (p : P) {h : Nat}
    (cache : Certified M p h) (s : S) (policy : OptimalController.Policy A O h)
    (admissible : OptimalController.Admissible M s policy) :
    value M p cache s ≤ OptimalController.worst M p s policy := by
  rw [value_exact]
  exact OptimalController.value_optimal M p h s policy admissible

def select (M : OptimalController.Model P S A O) (p : P) {h : Nat}
    (cache : Certified M p (h + 1)) (s : S) : A :=
  match cache.val with
  | .succ _ lower => OptimalController.selectAction M p (read lower.top.table) s

omit [DecidableEq A] [DecidableEq O] in
theorem select_exact (M : OptimalController.Model P S A O) (p : P) {h : Nat}
    (cache : Certified M p (h + 1)) (s : S) :
    select M p cache s = OptimalController.selectAction M p (OptimalController.value M p h) s := by
  rcases cache with ⟨cache, valid⟩
  cases cache with
  | succ top lower =>
    have he : read lower.top.table = OptimalController.value M p h :=
      funext (Cache.top_exact M p lower valid.2)
    exact congrArg (fun f => OptimalController.selectAction M p f s) he

def Cache.cells : {h : Nat} → Cache S h → Nat
  | _, .zero top => top.table.length
  | _, .succ top lower => top.table.length + lower.cells

def Cache.work : {h : Nat} → Cache S h → Nat
  | _, .zero top => top.recomputed.length
  | _, .succ top lower => top.recomputed.length + lower.work

omit [DecidableEq A] [DecidableEq O] in
theorem build_cells (U : List S) (M : OptimalController.Model P S A O) (p : P) (h : Nat) :
    (build U M p h).cells = (h + 1) * U.length := by
  induction h with
  | zero => simp [build, Cache.cells, base, materialize]
  | succ h ih => simp [build, Cache.cells, materialize, ih, Nat.add_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.two_mul]

theorem refresh_cells (U : List S) (M N : OptimalController.Model P S A O) (p q : P)
    {h : Nat} (cache : Cache S h) :
    (refresh U M N p q cache).cells = (h + 1) * U.length := by
  induction cache with
  | zero top => simp [refresh, Cache.cells, base, materialize]
  | succ top lower ih => simp [refresh, Cache.cells, updateLayer, materialize, ih,
      Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.two_mul]

theorem refresh_same_changes (U : List S) (complete : ∀ s, s ∈ U)
    (M : OptimalController.Model P S A O) (p : P) {h : Nat}
    (cache : Cache S h) (valid : cache.Valid M p) :
    (refresh U M M p p cache).top.changed = [] := by
  rw [refresh_changes]
  have nextValid := refresh_valid U complete M M p p cache valid
  apply List.filter_eq_nil_iff.mpr
  intro s _
  simp [Cache.top_exact M p cache valid s,
    Cache.top_exact M p _ nextValid s]

omit [Inhabited A] in
theorem localSame_self (M : OptimalController.Model P S A O) (p : P) (s : S) :
    localSame M M p p s = true := by
  simp [localSame, List.all_eq_true]

theorem refresh_same_work (U : List S) (complete : ∀ s, s ∈ U)
    (M : OptimalController.Model P S A O) (p : P) {h : Nat}
    (cache : Cache S h) (valid : cache.Valid M p) :
    (refresh U M M p p cache).work = 0 := by
  induction cache with
  | zero top =>
    have hc := refresh_same_changes U complete M p (.zero top) valid
    exact congrArg List.length hc
  | succ top lower ih =>
    have hc := refresh_same_changes U complete M p lower valid.2
    simp [refresh, Cache.work, updateLayer, localSame_self, hc, depends, ih valid.2]

theorem refresh_work_bound (U : List S) (M N : OptimalController.Model P S A O)
    (p q : P) {h : Nat} (cache : Cache S h) :
    (refresh U M N p q cache).work ≤ (h + 1) * U.length := by
  induction cache with
  | zero top =>
    simpa [refresh, Cache.work, base, changes] using
      List.length_filter_le (fun s => decide (read top.table s ≠
        read (materialize U (N.terminal q)) s)) U
  | succ top lower ih =>
    have hb := List.length_filter_le
      (fun s => !localSame M N p q s || depends N (refresh U M N p q lower).top.changed s) U
    simpa [refresh, Cache.work, updateLayer, Nat.add_mul, Nat.two_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.add_le_add hb ih

end IncrementalControl
