import Std

namespace OptimalController

def maximum {A : Type} : List A → (A → Nat) → Nat
  | [], _ => 0
  | a :: xs, f => max (f a) (maximum xs f)

theorem maximum_upper {A : Type} (xs : List A) (f : A → Nat) (a : A)
    (ha : a ∈ xs) : f a ≤ maximum xs f := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ha) (Nat.le_max_right _ _)

theorem maximum_mono {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ a, a ∈ xs → f a ≤ g a) : maximum xs f ≤ maximum xs g := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    exact Nat.max_le.mpr ⟨Nat.le_trans (h a List.mem_cons_self) (Nat.le_max_left _ _),
      Nat.le_trans (ih (fun x hx => h x (List.mem_cons_of_mem a hx))) (Nat.le_max_right _ _)⟩

theorem maximum_congr {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ a, a ∈ xs → f a = g a) : maximum xs f = maximum xs g := by
  apply Nat.le_antisymm
  · exact maximum_mono xs f g (fun a ha => Nat.le_of_eq (h a ha))
  · exact maximum_mono xs g f (fun a ha => Nat.le_of_eq (h a ha).symm)

theorem maximum_attained {A : Type} (xs : List A) (f : A → Nat)
    (h : xs ≠ []) : ∃ a, a ∈ xs ∧ maximum xs f = f a := by
  induction xs with
  | nil => contradiction
  | cons a xs ih =>
    cases xs with
    | nil => exact ⟨a, by simp, by simp [maximum]⟩
    | cons b bs =>
      obtain ⟨x, hx, hv⟩ := ih (by simp)
      by_cases hle : f a ≤ maximum (b :: bs) f
      · refine ⟨x, List.mem_cons_of_mem a hx, ?_⟩
        change max (f a) (maximum (b :: bs) f) = f x
        rw [Nat.max_eq_right hle, hv]
      · exact ⟨a, List.mem_cons_self, Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hle))⟩

def argmin {A : Type} : List A → (A → Nat) → Option A
  | [], _ => none
  | a :: xs, f =>
    match argmin xs f with
    | none => some a
    | some b => some (if f a ≤ f b then a else b)

theorem argmin_none_iff {A : Type} (xs : List A) (f : A → Nat) :
    argmin xs f = none ↔ xs = [] := by
  cases xs with
  | nil => simp [argmin]
  | cons a xs => simp [argmin]; cases argmin xs f <;> simp

theorem argmin_exists {A : Type} (xs : List A) (f : A → Nat) (h : xs ≠ []) :
    ∃ a, argmin xs f = some a := by
  cases he : argmin xs f with
  | none => exact False.elim (h ((argmin_none_iff xs f).mp he))
  | some a => exact ⟨a, rfl⟩

theorem argmin_spec {A : Type} (xs : List A) (f : A → Nat) (a : A)
    (h : argmin xs f = some a) : a ∈ xs ∧ ∀ b, b ∈ xs → f a ≤ f b := by
  induction xs generalizing a with
  | nil => simp [argmin] at h
  | cons x xs ih =>
    cases he : argmin xs f with
    | none =>
      have hx : xs = [] := (argmin_none_iff xs f).mp he
      subst xs
      simp only [argmin, Option.some.injEq] at h
      subst a
      simp
    | some y =>
      have hy := ih y he
      simp only [argmin, he, Option.some.injEq] at h
      split at h
      next hle =>
        subst a
        refine ⟨List.mem_cons_self, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Nat.le_refl _
        · exact Nat.le_trans hle (hy.2 b hb)
      next hgt =>
        subst a
        refine ⟨List.mem_cons_of_mem x hy.1, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact Nat.le_of_lt (Nat.lt_of_not_ge hgt)
        · exact hy.2 b hb

theorem argmin_congr {A : Type} (xs : List A) (f g : A → Nat)
    (h : ∀ a, a ∈ xs → f a = g a) : argmin xs f = argmin xs g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [argmin, ht]
    cases he : argmin xs g with
    | none => rfl
    | some b =>
      have hb := (argmin_spec xs g b he).1
      simp only
      rw [h a (List.mem_cons_self), h b (List.mem_cons_of_mem a hb)]

structure Model (P S A O : Type) where
  actions : S → List A
  actionsNonempty : ∀ s, actions s ≠ []
  outcomes : S → A → List O
  outcomesNonempty : ∀ s a, a ∈ actions s → outcomes s a ≠ []
  next : S → A → O → S
  cost : P → S → A → O → Nat
  terminal : P → S → Nat

variable {P S A O : Type} [Inhabited A]

def score (M : Model P S A O) (p : P) (V : S → Nat) (s : S) (a : A) : Nat :=
  maximum (M.outcomes s a) (fun o => M.cost p s a o + V (M.next s a o))

def selectAction (M : Model P S A O) (p : P) (V : S → Nat) (s : S) : A :=
  (argmin (M.actions s) (score M p V s)).getD default

def backup (M : Model P S A O) (p : P) (V : S → Nat) (s : S) : Nat :=
  score M p V s (selectAction M p V s)

theorem selectAction_spec (M : Model P S A O) (p : P) (V : S → Nat) (s : S) :
    selectAction M p V s ∈ M.actions s ∧
      ∀ a, a ∈ M.actions s → backup M p V s ≤ score M p V s a := by
  obtain ⟨a, ha⟩ := argmin_exists (M.actions s) (score M p V s) (M.actionsNonempty s)
  have hs : selectAction M p V s = a := by simp [selectAction, ha]
  simpa [backup, hs] using argmin_spec (M.actions s) (score M p V s) a ha

theorem backup_of_scores_eq (M N : Model P S A O) (p q : P)
    (V W : S → Nat) (s t : S) (ha : M.actions s = N.actions t)
    (hv : ∀ a, a ∈ M.actions s → score M p V s a = score N q W t a) :
    backup M p V s = backup N q W t := by
  have hc : selectAction M p V s = selectAction N q W t := by
    unfold selectAction
    rw [← ha, argmin_congr (M.actions s) _ _ hv]
  unfold backup
  rw [← hc]
  exact hv _ (selectAction_spec M p V s).1

theorem backup_congr (M : Model P S A O) (p : P) (V W : S → Nat) (s : S)
    (h : ∀ a, a ∈ M.actions s → ∀ o, o ∈ M.outcomes s a →
      V (M.next s a o) = W (M.next s a o)) :
    backup M p V s = backup M p W s := by
  apply backup_of_scores_eq M M p p V W s s rfl
  intro a ha
  exact maximum_congr _ _ _ (fun o ho => congrArg (M.cost p s a o + ·) (h a ha o ho))

theorem backup_transfer (M N : Model P S A O) (p q : P) (V W : S → Nat) (s : S)
    (ha : M.actions s = N.actions s)
    (ho : ∀ a, a ∈ M.actions s → M.outcomes s a = N.outcomes s a)
    (hc : ∀ a, a ∈ M.actions s → ∀ o, o ∈ M.outcomes s a →
      M.cost p s a o = N.cost q s a o)
    (hv : ∀ a, a ∈ M.actions s → ∀ o, o ∈ M.outcomes s a →
      V (M.next s a o) = W (N.next s a o)) :
    backup M p V s = backup N q W s := by
  apply backup_of_scores_eq M N p q V W s s ha
  intro a ham
  unfold score
  rw [← ho a ham]
  apply maximum_congr
  intro o hom
  rw [hc a ham o hom, hv a ham o hom]

def value (M : Model P S A O) (p : P) : Nat → S → Nat
  | 0, s => M.terminal p s
  | n + 1, s => backup M p (value M p n) s

theorem value_zero (M : Model P S A O) (p : P) (s : S) :
    value M p 0 s = M.terminal p s := rfl

theorem value_succ (M : Model P S A O) (p : P) (n : Nat) (s : S) :
    value M p (n + 1) s = backup M p (value M p n) s := rfl

inductive Policy (A O : Type) : Nat → Type where
  | stop : Policy A O 0
  | step {n : Nat} (action : A) (after : O → Policy A O n) : Policy A O (n + 1)

def Admissible (M : Model P S A O) : {n : Nat} → S → Policy A O n → Prop
  | 0, _, .stop => True
  | _ + 1, s, .step a after =>
    a ∈ M.actions s ∧ ∀ o, o ∈ M.outcomes s a → Admissible M (M.next s a o) (after o)

def worst (M : Model P S A O) (p : P) : {n : Nat} → S → Policy A O n → Nat
  | 0, s, .stop => M.terminal p s
  | _ + 1, s, .step a after =>
    maximum (M.outcomes s a) (fun o => M.cost p s a o + worst M p (M.next s a o) (after o))

def optimize (M : Model P S A O) (p : P) : (n : Nat) → S → Policy A O n
  | 0, _ => .stop
  | n + 1, s =>
    let a := selectAction M p (value M p n) s
    .step a (fun o => optimize M p n (M.next s a o))

theorem optimize_admissible (M : Model P S A O) (p : P) (n : Nat) (s : S) :
    Admissible M s (optimize M p n s) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    exact ⟨(selectAction_spec M p (value M p n) s).1, fun o _ => ih _⟩

theorem optimize_attains (M : Model P S A O) (p : P) (n : Nat) (s : S) :
    worst M p s (optimize M p n s) = value M p n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold optimize worst value backup score
    apply maximum_congr
    intro o _
    rw [ih]

theorem value_optimal (M : Model P S A O) (p : P) (n : Nat) (s : S)
    (policy : Policy A O n) (valid : Admissible M s policy) :
    value M p n s ≤ worst M p s policy := by
  induction n generalizing s with
  | zero => cases policy; exact Nat.le_refl _
  | succ n ih =>
    cases policy with
    | step a after =>
      have chosen := (selectAction_spec M p (value M p n) s).2 a valid.1
      apply Nat.le_trans chosen
      apply maximum_mono
      intro o ho
      exact Nat.add_le_add_left (ih _ (after o) (valid.2 o ho)) _

theorem policy_optimal (M : Model P S A O) (p : P) (n : Nat) (s : S)
    (policy : Policy A O n) (valid : Admissible M s policy) :
    worst M p s (optimize M p n s) ≤ worst M p s policy := by
  rw [optimize_attains]
  exact value_optimal M p n s policy valid

theorem selected_outcome_bound (M : Model P S A O) (p : P) (n : Nat) (s : S)
    (o : O) (ho : o ∈ M.outcomes s (selectAction M p (value M p n) s)) :
    M.cost p s (selectAction M p (value M p n) s) o +
      value M p n (M.next s (selectAction M p (value M p n) s) o) ≤
      value M p (n + 1) s := by
  exact maximum_upper _
    (fun z => M.cost p s (selectAction M p (value M p n) s) z +
      value M p n (M.next s (selectAction M p (value M p n) s) z)) o ho

theorem selected_worst_attained (M : Model P S A O) (p : P) (n : Nat) (s : S) :
    ∃ o, o ∈ M.outcomes s (selectAction M p (value M p n) s) ∧
      value M p (n + 1) s =
      M.cost p s (selectAction M p (value M p n) s) o +
        value M p n (M.next s (selectAction M p (value M p n) s) o) :=
  maximum_attained _ _ (M.outcomesNonempty s _ (selectAction_spec M p (value M p n) s).1)

def weighted (dimensions : List Nat) (weights costs : Nat → Nat) : Nat :=
  (dimensions.map (fun i => weights i * costs i)).sum

theorem weighted_mono (dimensions : List Nat) (weights left right : Nat → Nat)
    (h : ∀ i, i ∈ dimensions → left i ≤ right i) :
    weighted dimensions weights left ≤ weighted dimensions weights right := by
  induction dimensions with
  | nil => exact Nat.le_refl _
  | cons i is ih =>
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (h i List.mem_cons_self))
      (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

theorem weighted_weights_mono (dimensions : List Nat) (left right costs : Nat → Nat)
    (h : ∀ i, i ∈ dimensions → left i ≤ right i) :
    weighted dimensions left costs ≤ weighted dimensions right costs := by
  induction dimensions with
  | nil => exact Nat.le_refl _
  | cons i is ih =>
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (h i List.mem_cons_self))
      (ih (fun j hj => h j (List.mem_cons_of_mem i hj)))

theorem weighted_add (dimensions : List Nat) (weights left right : Nat → Nat) :
    weighted dimensions weights (fun i => left i + right i) =
      weighted dimensions weights left + weighted dimensions weights right := by
  induction dimensions with
  | nil => rfl
  | cons i is ih =>
    change weights i * (left i + right i) + weighted is weights (fun j => left j + right j) =
      (weights i * left i + weighted is weights left) +
        (weights i * right i + weighted is weights right)
    rw [ih, Nat.mul_add]
    omega

omit [Inhabited A] in
theorem worst_param_mono (M : Model P S A O) (p q : P)
    (hc : ∀ s a o, M.cost p s a o ≤ M.cost q s a o)
    (ht : ∀ s, M.terminal p s ≤ M.terminal q s)
    (n : Nat) (s : S) (policy : Policy A O n) :
    worst M p s policy ≤ worst M q s policy := by
  induction n generalizing s with
  | zero => cases policy; exact ht s
  | succ n ih =>
    cases policy with
    | step a after =>
      exact maximum_mono _ _ _ (fun o _ => Nat.add_le_add (hc s a o) (ih _ (after o)))

theorem value_param_mono (M : Model P S A O) (p q : P)
    (hc : ∀ s a o, M.cost p s a o ≤ M.cost q s a o)
    (ht : ∀ s, M.terminal p s ≤ M.terminal q s) (n : Nat) (s : S) :
    value M p n s ≤ value M q n s := by
  calc
    value M p n s ≤ worst M p s (optimize M q n s) :=
      value_optimal M p n s _ (optimize_admissible M q n s)
    _ ≤ worst M q s (optimize M q n s) := worst_param_mono M p q hc ht n s _
    _ = value M q n s := optimize_attains M q n s

structure Session (S : Type) where
  state : S
  remaining : Nat
  spent : Nat

def advance [DecidableEq O] (M : Model P S A O) (p : P)
    (session : Session S) (observation : O) : Option (Session S) :=
  match session.remaining with
  | 0 => none
  | n + 1 =>
    let a := selectAction M p (value M p n) session.state
    if observation ∈ M.outcomes session.state a then
      some ⟨M.next session.state a observation, n,
        session.spent + M.cost p session.state a observation⟩
    else none

theorem advance_zero [DecidableEq O] (M : Model P S A O) (p : P)
    (session : Session S) (o : O) (h : session.remaining = 0) :
    advance M p session o = none := by simp [advance, h]

theorem advance_exact [DecidableEq O] (M : Model P S A O) (p : P)
    (session : Session S) (o : O) (n : Nat) (hn : session.remaining = n + 1) :
    advance M p session o =
      if o ∈ M.outcomes session.state (selectAction M p (value M p n) session.state) then
        some ⟨M.next session.state (selectAction M p (value M p n) session.state) o,
          n, session.spent + M.cost p session.state (selectAction M p (value M p n) session.state) o⟩
      else none := by simp [advance, hn]

theorem advance_rejects_unsupported [DecidableEq O] (M : Model P S A O) (p : P)
    (session : Session S) (o : O) (n : Nat) (hn : session.remaining = n + 1)
    (ho : o ∉ M.outcomes session.state (selectAction M p (value M p n) session.state)) :
    advance M p session o = none := by simp [advance, hn, ho]

theorem advance_remaining [DecidableEq O] (M : Model P S A O) (p : P)
    (session next : Session S) (o : O) (h : advance M p session o = some next) :
    next.remaining + 1 = session.remaining := by
  cases hn : session.remaining with
  | zero => simp [advance, hn] at h
  | succ n =>
    simp only [advance, hn] at h
    split at h
    next ho => cases h; rfl
    next ho => contradiction

theorem advance_bound [DecidableEq O] (M : Model P S A O) (p : P)
    (session next : Session S) (o : O) (h : advance M p session o = some next) :
    next.spent + value M p next.remaining next.state ≤
      session.spent + value M p session.remaining session.state := by
  cases hn : session.remaining with
  | zero => simp [advance, hn] at h
  | succ n =>
    simp only [advance, hn] at h
    split at h
    next ho =>
      cases h
      simpa [Nat.add_assoc] using Nat.add_le_add_left (selected_outcome_bound M p n session.state o ho) session.spent
    next ho => contradiction

def replay [DecidableEq O] (M : Model P S A O) (p : P) :
    Session S → List O → Option (Session S)
  | session, [] => some session
  | session, o :: os => (advance M p session o).bind (fun next => replay M p next os)

theorem replay_bound [DecidableEq O] (M : Model P S A O) (p : P)
    (session next : Session S) (observations : List O)
    (h : replay M p session observations = some next) :
    next.spent + value M p next.remaining next.state ≤
      session.spent + value M p session.remaining session.state := by
  induction observations generalizing session with
  | nil => cases h; exact Nat.le_refl _
  | cons o os ih =>
    cases hs : advance M p session o with
    | none => simp [replay, hs] at h
    | some middle =>
      have ht : replay M p middle os = some next := by simpa [replay, hs] using h
      exact Nat.le_trans (ih middle ht) (advance_bound M p session middle o hs)

theorem replay_remaining [DecidableEq O] (M : Model P S A O) (p : P)
    (session next : Session S) (observations : List O)
    (h : replay M p session observations = some next) :
    next.remaining + observations.length = session.remaining := by
  induction observations generalizing session with
  | nil => cases h; simp
  | cons o os ih =>
    cases hs : advance M p session o with
    | none => simp [replay, hs] at h
    | some middle =>
      have ht : replay M p middle os = some next := by simpa [replay, hs] using h
      have hm := ih middle ht
      have hc := advance_remaining M p session middle o hs
      simp only [List.length_cons]
      omega

theorem replay_append [DecidableEq O] (M : Model P S A O) (p : P)
    (session : Session S) (left right : List O) :
    replay M p session (left ++ right) =
      (replay M p session left).bind (fun next => replay M p next right) := by
  induction left generalizing session with
  | nil => rfl
  | cons o os ih =>
    simp only [List.cons_append, replay]
    cases hs : advance M p session o with
    | none => rfl
    | some middle => exact ih middle

theorem continuation_optimal [DecidableEq O] (M : Model P S A O) (p : P)
    (session next : Session S) (observations : List O)
    (accepted : replay M p session observations = some next) :
    next.spent + value M p next.remaining next.state ≤
        session.spent + value M p session.remaining session.state ∧
      Admissible M next.state (optimize M p next.remaining next.state) ∧
      ∀ alternative : Policy A O next.remaining, Admissible M next.state alternative →
        worst M p next.state (optimize M p next.remaining next.state) ≤
          worst M p next.state alternative :=
  ⟨replay_bound M p session next observations accepted,
    optimize_admissible M p next.remaining next.state,
    fun alternative valid => policy_optimal M p next.remaining next.state alternative valid⟩

namespace Controls

def futureSensitive : Model Nat Nat Bool Nat where
  actions := fun _ => [false, true]
  actionsNonempty := by intro s; simp
  outcomes := fun _ _ => [0, 1]
  outcomesNonempty := by intro s a ha; simp
  next := fun s a _ => if s = 0 then (if a then 2 else 1) else 2
  cost := fun p s a _ => if s = 0 then (if a then 2 * p else 0) else if s = 1 then 100 else 0
  terminal := fun _ _ => 0

theorem greedy_loses :
    selectAction futureSensitive 1 (value futureSensitive 1 0) 0 = false ∧
    selectAction futureSensitive 1 (value futureSensitive 1 1) 0 = true ∧
    value futureSensitive 1 2 0 = 2 := by decide

theorem parameter_changes_optimum :
    selectAction futureSensitive 100 (value futureSensitive 100 1) 0 = false ∧
    value futureSensitive 100 2 0 = 100 := by decide

theorem supported_observation_advances :
    (advance futureSensitive 1 ⟨0, 2, 0⟩ 0).map (fun s => (s.state, s.remaining, s.spent)) =
      some (2, 1, 2) := by decide

theorem unsupported_observation_rejected :
    (advance futureSensitive 1 ⟨0, 2, 0⟩ 9).isNone = true := by decide

def adaptive : Model Unit Nat Bool Nat where
  actions := fun _ => [false, true]
  actionsNonempty := by intro s; simp
  outcomes := fun _ _ => [0, 1]
  outcomesNonempty := by intro s a ha; simp
  next := fun s _ o => if s = 0 then o + 1 else 3
  cost := fun _ s a _ =>
    if s = 0 then 1 else if s = 1 then (if a then 7 else 0)
    else if s = 2 then (if a then 0 else 7) else 0
  terminal := fun _ _ => 0

def fixedSecond (a : Bool) : Policy Bool Nat 2 :=
  .step false (fun _ => .step a (fun _ => .stop))

theorem adaptation_beats_fixed :
    value adaptive () 2 0 = 1 ∧ ∀ a, worst adaptive () 0 (fixedSecond a) = 8 := by
  constructor
  · decide
  · intro a; cases a <;> decide

end Controls

end OptimalController
