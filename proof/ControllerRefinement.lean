import OnlineController

namespace ControllerRefinement

def addVector (dimension : Nat) (left right : List Nat) : List Nat :=
  (List.range dimension).map (fun i => (left[i]?).getD 0 + (right[i]?).getD 0)

theorem weighted_addVector (weights left right : List Nat) :
    OnlineController.weighted weights (addVector weights.length left right) =
      OnlineController.weighted weights left + OnlineController.weighted weights right := by
  have h : OnlineController.weighted weights (addVector weights.length left right) =
      OptimalController.weighted (List.range weights.length) (fun i => (weights[i]?).getD 0)
        (fun i => (left[i]?).getD 0 + (right[i]?).getD 0) := by
    unfold OnlineController.weighted OptimalController.weighted
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have bound : i < weights.length := List.mem_range.mp hi
    simp [addVector, List.getElem?_map, List.getElem?_range bound]
  rw [h, OptimalController.weighted_add]
  rfl

def projection (packed : OnlineController.Packed) : Nat × Nat × Nat :=
  (packed.state.val, packed.horizon, OnlineController.weighted packed.weights packed.spent)

def initial (packed : OnlineController.Packed) : OptimalController.Session (Fin (packed.n + 1)) :=
  ⟨packed.state, packed.horizon, OnlineController.weighted packed.weights packed.spent⟩

def abstractResult (old : OnlineController.Packed) (out : Fin (old.o + 1)) : Option (Nat × Nat × Nat) :=
  (OptimalController.advance (OnlineController.model old.table) old.weights (initial old) out).map
    (fun next => (next.state.val,next.remaining,next.spent))

theorem acceptOutcome_refines (old : OnlineController.Packed) (out : Fin (old.o + 1)) :
    (OnlineController.acceptOutcome old out).toOption.map projection = abstractResult old out := by
  rcases old with ⟨n,a,o,h,table,weights,cache,state,seq,epoch,spent,work⟩
  cases h with
  | zero => rfl
  | succ h =>
    rcases cache with ⟨cache,valid⟩
    cases cache with
    | succ top lower =>
      have exactLower : IncrementalControl.read lower.top.table =
          OptimalController.value (OnlineController.model table) weights h :=
        funext (IncrementalControl.Cache.top_exact _ _ lower valid.2)
      simp only [OnlineController.acceptOutcome, IncrementalControl.select, abstractResult,
        initial, OptimalController.advance, eq_mp_eq_cast, cast_eq]
      rw [exactLower]
      by_cases supported : out ∈ (OnlineController.model table).outcomes state
          (OptimalController.selectAction (OnlineController.model table) weights
            (OptimalController.value (OnlineController.model table) weights h) state)
      · simp only [supported, not_true_eq_false, if_false, if_true]
        change some (_, h, OnlineController.weighted weights
          (addVector weights.length spent _)) = some (_, h,
          OnlineController.weighted weights spent + OnlineController.weighted weights _)
        rw [weighted_addVector]
      · simp only [supported, not_false_eq_true, if_true, if_false]
        rfl

/-- The cost vector of the actual action chosen from the materialized cache. -/
def chosenCosts (old : OnlineController.Packed) (out : Fin (old.o + 1)) : List Nat :=
  match hh : old.horizon with
  | 0 => []
  | h + 1 =>
    let cache : IncrementalControl.Certified (OnlineController.model old.table) old.weights (h + 1) :=
      Eq.mp (congrArg
        (fun h => IncrementalControl.Certified (OnlineController.model old.table) old.weights h) hh) old.cache
    let action := IncrementalControl.select (OnlineController.model old.table) old.weights cache old.state
    (OnlineController.branch old.table.raw old.state action out).costs

theorem acceptOutcome_spentVector (old next : OnlineController.Packed) (out : Fin (old.o + 1))
    (accepted : OnlineController.acceptOutcome old out = .ok next) :
    next.spent = addVector old.weights.length old.spent (chosenCosts old out) := by
  rcases old with ⟨n,a,o,h,table,weights,cache,state,seq,epoch,spent,work⟩
  cases h with
  | zero => simp [OnlineController.acceptOutcome] at accepted
  | succ h =>
    rcases cache with ⟨cache,valid⟩
    cases cache with
    | succ top lower =>
      simp only [OnlineController.acceptOutcome, IncrementalControl.select, eq_mp_eq_cast, cast_eq] at accepted
      split at accepted
      next unsupported => contradiction
      next supported =>
        cases accepted
        simp [chosenCosts, IncrementalControl.select, addVector, eq_mp_eq_cast, cast_eq]

/-- A later same-width price vector reprices the retained cumulative vector exactly. -/
theorem acceptOutcome_reprice (old next : OnlineController.Packed) (out : Fin (old.o + 1))
    (accepted : OnlineController.acceptOutcome old out = .ok next)
    (prices : List Nat) (width : prices.length = old.weights.length) :
    OnlineController.weighted prices next.spent =
      OnlineController.weighted prices old.spent +
        OnlineController.weighted prices (chosenCosts old out) := by
  rw [acceptOutcome_spentVector old next out accepted, ← width, weighted_addVector]

theorem acceptOutcome_counters (old next : OnlineController.Packed) (out : Fin (old.o + 1))
    (accepted : OnlineController.acceptOutcome old out = .ok next) :
    next.horizon + 1 = old.horizon ∧ next.nextSeq = old.nextSeq + 1 ∧
    next.epoch = old.epoch ∧ next.weights = old.weights ∧
    next.spent.length = old.weights.length ∧ next.cumulativeWork = old.cumulativeWork := by
  rcases old with ⟨n,a,o,h,table,weights,cache,state,seq,epoch,spent,work⟩
  cases h with
  | zero => simp [OnlineController.acceptOutcome] at accepted
  | succ h =>
    rcases cache with ⟨cache,valid⟩
    cases cache with
    | succ top lower =>
      simp only [OnlineController.acceptOutcome, IncrementalControl.select, eq_mp_eq_cast, cast_eq] at accepted
      split at accepted
      next unsupported => contradiction
      next supported =>
        cases accepted
        simp

def budget (packed : OnlineController.Packed) : Nat :=
  OnlineController.weighted packed.weights packed.spent +
    IncrementalControl.value (OnlineController.model packed.table) packed.weights packed.cache packed.state

theorem acceptOutcome_budget (old next : OnlineController.Packed) (out : Fin (old.o + 1))
    (accepted : OnlineController.acceptOutcome old out = .ok next) : budget next ≤ budget old := by
  rcases old with ⟨n,a,o,h,table,weights,cache,state,seq,epoch,spent,work⟩
  cases h with
  | zero => simp [OnlineController.acceptOutcome] at accepted
  | succ h =>
    rcases cache with ⟨cache,valid⟩
    cases cache with
    | succ top lower =>
      have exactLower : IncrementalControl.read lower.top.table =
          OptimalController.value (OnlineController.model table) weights h :=
        funext (IncrementalControl.Cache.top_exact _ _ lower valid.2)
      simp only [OnlineController.acceptOutcome, IncrementalControl.select, eq_mp_eq_cast, cast_eq] at accepted
      rw [exactLower] at accepted
      split at accepted
      next unsupported => contradiction
      next supported =>
        cases accepted
        unfold budget
        rw [IncrementalControl.value_exact, IncrementalControl.value_exact]
        change OnlineController.weighted weights (addVector weights.length spent _) +
          OptimalController.value (OnlineController.model table) weights h _ ≤
          OnlineController.weighted weights spent +
          OptimalController.value (OnlineController.model table) weights (h + 1) state
        rw [weighted_addVector]
        have bound := OptimalController.selected_outcome_bound (OnlineController.model table)
          weights h state out (by simpa using supported)
        simpa [OnlineController.model, Nat.add_assoc] using Nat.add_le_add_left bound
          (OnlineController.weighted weights spent)

/-- Repeated calls to the same executable outcome transition, accepting only typed IDs. -/
def replay : OnlineController.Packed → List Nat → Except String OnlineController.Packed
  | old, [] => .ok old
  | old, raw :: rest =>
    if within : raw < old.o + 1 then
      match OnlineController.acceptOutcome old ⟨raw, within⟩ with
      | .error message => .error message
      | .ok next => replay next rest
    else .error "outcome identifier out of range"

theorem replay_budget (old next : OnlineController.Packed) (outcomes : List Nat)
    (accepted : replay old outcomes = .ok next) : budget next ≤ budget old := by
  induction outcomes generalizing old with
  | nil =>
    cases accepted
    exact Nat.le_refl _
  | cons raw rest ih =>
    simp only [replay] at accepted
    split at accepted
    next within =>
      split at accepted
      next failure => contradiction
      next current transition =>
        exact Nat.le_trans (ih current accepted)
          (acceptOutcome_budget old current ⟨raw, within⟩ transition)
    next outside => contradiction

theorem replay_counters (old next : OnlineController.Packed) (outcomes : List Nat)
    (accepted : replay old outcomes = .ok next) :
    next.horizon + outcomes.length = old.horizon ∧
      next.nextSeq = old.nextSeq + outcomes.length ∧
      next.epoch = old.epoch ∧ next.weights = old.weights ∧
      next.cumulativeWork = old.cumulativeWork := by
  induction outcomes generalizing old with
  | nil =>
    cases accepted
    simp
  | cons raw rest ih =>
    simp only [replay] at accepted
    split at accepted
    next within =>
      split at accepted
      next failure => contradiction
      next current transition =>
        have first := acceptOutcome_counters old current ⟨raw, within⟩ transition
        have tail := ih current accepted
        simp only [List.length_cons]
        rcases first with ⟨fh,fs,fe,fw,_,fc⟩
        rcases tail with ⟨th,ts,te,tw,tc⟩
        exact ⟨by omega, by omega, te.trans fe, tw.trans fw, tc.trans fc⟩
    next outside => contradiction

end ControllerRefinement
