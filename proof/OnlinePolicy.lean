import OnlineController
import ParetoPolicy

namespace OnlinePolicy

open Lean OptimalController ParetoPolicy

def weightOf (weights : List Nat) (i : Nat) : Nat := (weights[i]?).getD 0

def Ledger (dimensions : Nat) (spent budget initial : List Nat) : Prop :=
  ∀ i : Fin dimensions, weightOf spent i.val + weightOf budget i.val = weightOf initial i.val

instance (dimensions : Nat) (spent budget initial : List Nat) : Decidable (Ledger dimensions spent budget initial) := by
  unfold Ledger
  infer_instance

structure Packed where
  n : Nat
  a : Nat
  o : Nat
  horizon : Nat
  table : OnlineController.Table n a o
  weights : List Nat
  budget : List Nat
  initialBound : List Nat
  state : Fin (n + 1)
  records : {rs : List (Record (Fin (n + 1)) (a + 1) (o + 1) horizon) //
    rs = cache (OnlineController.componentModel table) table.raw.dimensions horizon state}
  pareto : ParametricPareto.Certified
  axes : pareto.val.axes = List.range table.raw.dimensions
  catalogue : pareto.val.catalogue = ParetoPolicy.boundedCatalogue
    (OnlineController.componentModel table) table.raw.dimensions horizon state (weightOf budget)
  feasible : pareto.val.catalogue ≠ []
  nextSeq : Nat
  epoch : Nat
  spent : List Nat
  ledger : Ledger table.raw.dimensions spent budget initialBound
  cumulativeProfiles : Nat
  cumulativeComparisons : Nat

def selected (packed : Packed) : Option ParametricPareto.Point :=
  ParametricPareto.selectFrontier packed.pareto.val (weightOf packed.weights)

def selectedRecord (packed : Packed) :
    Option (Record (Fin (packed.n + 1)) (packed.a + 1) (packed.o + 1) packed.horizon) := do
  let p ← selected packed
  packed.records.val.find? (fun r => r.id == p.id)

def policyJson {a o : Nat} : {h : Nat} → Policy (Fin a) (Fin o) h → Json
  | 0, .stop => Json.null
  | _ + 1, .step action after => Json.mkObj [("action", toJson action.val),
      ("after", toJson ((List.finRange o).map (fun out => policyJson (after out))))]

def firstAction {a o : Nat} : {h : Nat} → Policy (Fin a) (Fin o) h → Option Nat
  | 0, .stop => none
  | _ + 1, .step action _ => some action.val

def rootAction {a o : Nat} : {h : Nat} → Policy (Fin a) (Fin o) h → Option (Fin a)
  | 0, .stop => none
  | _ + 1, .step action _ => some action

def sourceJson {n a : Nat} : Source (Fin n) (Fin a) → Json
  | .terminal s => Json.arr #[toJson "terminal", toJson s.val]
  | .branch s a => Json.arr #[toJson "branch", toJson s.val, toJson a.val]

def recordJson {n a o h : Nat} (r : Record (Fin n) a o h) : Json :=
  Json.mkObj [("id", toJson r.id), ("admitted", toJson r.admitted),
    ("profile", toJson r.profile), ("dependencies", toJson (r.dependencies.map sourceJson))]

def pointJson (p : ParametricPareto.Point) : Json :=
  Json.mkObj [("id", toJson p.id), ("profile", toJson p.profile)]

def observe (packed : Packed) (profileIds : List Nat) (reusedProfiles comparisons reusedComparisons : Nat)
    (reset : Bool) : Json :=
  let picked := selected packed
  let record := selectedRecord packed
  Json.mkObj [("objective", toJson "weighted-coordinatewise-worst"),
    ("state", toJson packed.state.val), ("remaining", toJson packed.horizon),
    ("next_seq", toJson packed.nextSeq), ("epoch", toJson packed.epoch),
    ("weights", toJson packed.weights), ("spent", toJson packed.spent),
    ("budget", toJson packed.budget), ("initial_bound", toJson packed.initialBound),
    ("selected", match picked with | none => Json.null | some p => pointJson p),
    ("action", match record with | none => Json.null | some r => toJson (firstAction r.policy)),
    ("policy", match record with | none => Json.null | some r => policyJson r.policy),
    ("weighted_cost", match picked with
      | none => Json.null
      | some p => toJson (ParametricPareto.weighted packed.pareto.val.axes (weightOf packed.weights) p)),
    ("policies", toJson (packed.records.val.map recordJson)),
    ("catalogue", toJson (packed.pareto.val.catalogue.map pointJson)),
    ("frontier", toJson ((ParametricPareto.frontier packed.pareto.val).map pointJson)),
    ("comparisons", toJson (packed.pareto.val.comparisons.map (fun c =>
      Json.arr #[toJson c.left.id, toJson c.right.id, toJson c.value]))),
    ("profiles_needed", toJson profileIds.length), ("profiles_reused", toJson reusedProfiles),
    ("recomputed_ids", toJson profileIds), ("comparisons_needed", toJson comparisons),
    ("comparisons_reused", toJson reusedComparisons),
    ("cumulative_profiles", toJson packed.cumulativeProfiles),
    ("cumulative_comparisons", toJson packed.cumulativeComparisons),
    ("problem_reset", toJson reset)]

def initialPoint (axes : List Nat) (catalogue : List ParametricPareto.Point) (weights : List Nat) :
    ParametricPareto.Point :=
  (ParametricPareto.choose (ParametricPareto.key axes (weightOf weights)) catalogue).getD ⟨0, []⟩

theorem initialPoint_mem (axes : List Nat) (catalogue : List ParametricPareto.Point) (weights : List Nat)
    (hne : catalogue ≠ []) : initialPoint axes catalogue weights ∈ catalogue := by
  cases h : ParametricPareto.choose (ParametricPareto.key axes (weightOf weights)) catalogue with
  | none => exact False.elim (hne ((ParametricPareto.choose_none _ _).mp h))
  | some p => simpa [initialPoint, h] using (ParametricPareto.choose_correct _ _ p h).1

def initialBudget (dimensions : Nat) (p : ParametricPareto.Point) : List Nat :=
  (List.range dimensions).map (fun i => (ParametricPareto.cost p i).toNat)

theorem initialBudget_fits (dimensions : Nat) (p : ParametricPareto.Point) :
    within dimensions (weightOf (initialBudget dimensions p)) p = true := by
  apply (within_exact dimensions _ p).mpr
  intro i hi
  simp only [weightOf, initialBudget, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some]
  change ParametricPareto.cost p i ≤ ((ParametricPareto.cost p i).toNat : Int)
  omega

def start (input : OnlineController.Input) (weights : List Nat) (horizon : Nat)
    (state : Fin (input.n + 1)) : Packed :=
  let records := cache (OnlineController.componentModel input.table) input.table.raw.dimensions horizon state
  let unbounded := cacheCatalogue records
  have fullExact : unbounded = ParetoPolicy.catalogue (OnlineController.componentModel input.table)
      input.table.raw.dimensions horizon state := cache_catalogue_exact _ _ _ _
  have fullNonempty : unbounded ≠ [] := by
    rw [fullExact]
    exact catalogue_nonempty _ _ _ _
  let p := initialPoint (List.range input.table.raw.dimensions) unbounded weights
  let budget := initialBudget input.table.raw.dimensions p
  let catalogue := unbounded.filter (within input.table.raw.dimensions (weightOf budget))
  let pareto := ParametricPareto.start (List.range input.table.raw.dimensions) catalogue
  have catalogueExact : pareto.val.catalogue = boundedCatalogue (OnlineController.componentModel input.table)
      input.table.raw.dimensions horizon state (weightOf budget) := by
    change unbounded.filter _ = _
    rw [fullExact]
    rfl
  have feasible : pareto.val.catalogue ≠ [] := by
    have hp : p ∈ pareto.val.catalogue := List.mem_filter.mpr
      ⟨initialPoint_mem _ _ _ fullNonempty, initialBudget_fits _ p⟩
    intro he
    rw [he] at hp
    simp at hp
  have ledger : Ledger input.table.raw.dimensions (List.replicate input.table.raw.dimensions 0) budget budget := by
    intro i
    simp [weightOf, i.isLt]
  ⟨input.n, input.a, input.o, horizon, input.table, weights, budget, budget, state, ⟨records, rfl⟩,
    pareto, rfl, catalogueExact, feasible, 1, 0,
    List.replicate input.table.raw.dimensions 0, ledger, records.length, catalogue.length * catalogue.length⟩

def revisedIds (old : Packed) (table : OnlineController.Table old.n old.a old.o) : List Nat :=
  (old.records.val.filter (fun r => !(r.dependencies.all
    (sameSource (OnlineController.componentModel old.table) (OnlineController.componentModel table)
      old.table.raw.dimensions)))).map (fun r => r.id)

def revise (old : Packed) (input : OnlineController.Input) (weights : List Nat) : Except String Packed := do
  if hn : input.n = old.n then
    if ha : input.a = old.a then
      if ho : input.o = old.o then
        let table : OnlineController.Table old.n old.a old.o := hn ▸ ha ▸ ho ▸ input.table
        if hd : table.raw.dimensions = old.table.raw.dimensions then
          let records := refreshCache (OnlineController.componentModel old.table)
            (OnlineController.componentModel table) old.table.raw.dimensions old.state old.records.val
          have recordsExact : records = cache (OnlineController.componentModel table)
              table.raw.dimensions old.horizon old.state := by
            dsimp [records]
            rw [old.records.property, refresh_cache_exact, hd]
          let catalogue := (cacheCatalogue records).filter (within table.raw.dimensions (weightOf old.budget))
          if feasible : catalogue ≠ [] then
            let pareto := ParametricPareto.advance old.pareto (List.range table.raw.dimensions) catalogue
            have catalogueExact : pareto.val.catalogue = ParetoPolicy.boundedCatalogue
                (OnlineController.componentModel table) table.raw.dimensions old.horizon old.state (weightOf old.budget) := by
              change (cacheCatalogue records).filter _ = _
              rw [recordsExact, cache_catalogue_exact]
              rfl
            let needed := (revisedIds old table).length
            let comparisons := ParametricPareto.comparisonsNeeded old.pareto.val
              (List.range table.raw.dimensions) catalogue
            have ledger : Ledger table.raw.dimensions old.spent old.budget old.initialBound := by
              rw [hd]
              exact old.ledger
            return ⟨old.n, old.a, old.o, old.horizon, table, weights, old.budget, old.initialBound, old.state,
              ⟨records, recordsExact⟩, pareto, rfl, catalogueExact, feasible,
              old.nextSeq + 1, old.epoch, old.spent, ledger,
              old.cumulativeProfiles + needed, old.cumulativeComparisons + comparisons⟩
          else throw "model revision violates committed outcome budget"
        else throw "dimension change requires rebase"
      else throw "outcome universe change requires rebase"
    else throw "action universe change requires rebase"
  else throw "state universe change requires rebase"

def reconstruct (old : Packed) (horizon : Nat) (state : Fin (old.n + 1))
    (budget spent : List Nat) (advanceClock : Bool) : Except String Packed := do
  let records := cache (OnlineController.componentModel old.table) old.table.raw.dimensions horizon state
  let catalogue := (cacheCatalogue records).filter (within old.table.raw.dimensions (weightOf budget))
  if feasible : catalogue ≠ [] then
    if ledger : Ledger old.table.raw.dimensions spent budget old.initialBound then
      let pareto := ParametricPareto.start (List.range old.table.raw.dimensions) catalogue
      have catalogueExact : pareto.val.catalogue = boundedCatalogue (OnlineController.componentModel old.table)
          old.table.raw.dimensions horizon state (weightOf budget) := by
        change (cacheCatalogue records).filter _ = _
        rw [cache_catalogue_exact]
        rfl
      return ⟨old.n, old.a, old.o, horizon, old.table, old.weights, budget, old.initialBound,
        state, ⟨records, rfl⟩, pareto, rfl, catalogueExact, feasible,
        old.nextSeq + (if advanceClock then 1 else 0), old.epoch, spent, ledger,
        old.cumulativeProfiles + records.length,
        old.cumulativeComparisons + catalogue.length * catalogue.length⟩
    else throw "outcome violates cumulative component budget"
  else throw "no policy fits residual component budget"

def acceptOutcome (old : Packed) (out : Fin (old.o + 1)) : Except String Packed := do
  let some record := selectedRecord old | throw "certified policy lookup failed"
  let some action := rootAction record.policy | throw "no remaining decision horizon"
  if out ∉ (OnlineController.componentModel old.table).outcomes old.state action then
    throw "unsupported empirical outcome"
  let nextState := (OnlineController.componentModel old.table).next old.state action out
  let spent := (List.range old.table.raw.dimensions).map (fun i =>
    (old.spent[i]?).getD 0 + (OnlineController.componentModel old.table).cost i old.state action out)
  let budget := (List.range old.table.raw.dimensions).map (fun i =>
    (old.budget[i]?).getD 0 - (OnlineController.componentModel old.table).cost i old.state action out)
  reconstruct old (old.horizon - 1) nextState budget spent true

def step (old : Option Packed) (request : Json) : Except String (Packed × Json) := do
  let op ← (← request.getObjVal? "op").getStr?
  if op = "start" then
    OnlineHma.keys request ["op", "model", "weights", "horizon", "state"]
    if old.isSome then throw "policy session already started"
    let input ← OnlineController.decode (← request.getObjVal? "model")
    let weights ← OnlineController.costList input.table.raw.dimensions (← request.getObjVal? "weights")
    let horizon ← (← request.getObjVal? "horizon").getNat?
    let state ← OnlineController.bounded (input.n + 1) (← request.getObjVal? "state")
    let next := start input weights horizon state
    return (next, observe next (next.records.val.map (fun r => r.id)) 0
      next.cumulativeComparisons 0 true)
  else
    let some old := old | throw "policy session not started"
    let seq ← (← request.getObjVal? "seq").getNat?
    let epoch ← (← request.getObjVal? "epoch").getNat?
    if seq != old.nextSeq || epoch != old.epoch then throw "stale policy sequence or epoch"
    if op = "parameters" then
      OnlineHma.keys request ["op", "seq", "epoch", "weights"]
      let weights ← OnlineController.costList old.table.raw.dimensions (← request.getObjVal? "weights")
      let next := {old with weights := weights, nextSeq := old.nextSeq + 1}
      return (next, observe next [] next.records.val.length 0 next.pareto.val.comparisons.length false)
    else if op = "revise" then
      OnlineHma.keys request ["op", "seq", "epoch", "model", "weights"]
      let input ← OnlineController.decode (← request.getObjVal? "model")
      let weights ← OnlineController.costList input.table.raw.dimensions (← request.getObjVal? "weights")
      let next ← revise old input weights
      if hn : next.n = old.n then
        if ha : next.a = old.a then
          if ho : next.o = old.o then
            let table : OnlineController.Table old.n old.a old.o := hn ▸ ha ▸ ho ▸ next.table
            let ids := revisedIds old table
            let comparisons := next.cumulativeComparisons - old.cumulativeComparisons
            return (next, observe next ids (old.records.val.length - ids.length) comparisons
              (next.pareto.val.comparisons.length - comparisons) false)
          else throw "internal policy carrier mismatch"
        else throw "internal policy carrier mismatch"
      else throw "internal policy carrier mismatch"
    else if op = "outcome" then
      OnlineHma.keys request ["op", "seq", "epoch", "outcome"]
      let out ← OnlineController.bounded (old.o + 1) (← request.getObjVal? "outcome")
      let next ← acceptOutcome old out
      return (next, observe next (next.records.val.map (fun r => r.id)) 0
        (next.cumulativeComparisons - old.cumulativeComparisons) 0 true)
    else if op = "rebase" then
      OnlineHma.keys request ["op", "seq", "epoch", "model", "weights", "horizon", "state"]
      let input ← OnlineController.decode (← request.getObjVal? "model")
      let weights ← OnlineController.costList input.table.raw.dimensions (← request.getObjVal? "weights")
      let horizon ← (← request.getObjVal? "horizon").getNat?
      let state ← OnlineController.bounded (input.n + 1) (← request.getObjVal? "state")
      let next := start input weights horizon state
      let work := next.cumulativeComparisons
      let next := {next with
        nextSeq := old.nextSeq + 1
        epoch := old.epoch + 1
        cumulativeProfiles := old.cumulativeProfiles + next.cumulativeProfiles
        cumulativeComparisons := old.cumulativeComparisons + work}
      return (next, observe next (next.records.val.map (fun r => r.id)) 0 work 0 true)
    else if op = "inspect" || op = "checkpoint" then
      OnlineHma.keys request ["op", "seq", "epoch"]
      if op = "inspect" then
        return (old, observe old [] old.records.val.length 0 old.pareto.val.comparisons.length false)
      let next ← reconstruct old old.horizon old.state old.budget old.spent false
      let work := next.cumulativeComparisons - old.cumulativeComparisons
      return (next, observe next (next.records.val.map (fun r => r.id)) 0 work 0 true)
    else throw "unknown policy operation"

theorem selected_catalogue (packed : Packed) (p : ParametricPareto.Point)
    (h : selected packed = some p) : p ∈ ParetoPolicy.catalogue
      (OnlineController.componentModel packed.table) packed.table.raw.dimensions packed.horizon packed.state := by
  have hp := ParametricPareto.frontier_selected_optimal packed.pareto.val packed.pareto.property
    (weightOf packed.weights) p h
  have hm := (ParametricPareto.frontier_exact packed.pareto.val packed.pareto.property p).mp hp.1
  rw [packed.catalogue] at hm
  exact (List.mem_filter.mp hm.1).1

theorem selected_bounded (packed : Packed) (p : ParametricPareto.Point)
    (h : selected packed = some p) : p ∈ ParetoPolicy.boundedCatalogue
      (OnlineController.componentModel packed.table) packed.table.raw.dimensions packed.horizon packed.state
        (weightOf packed.budget) := by
  have hp := ParametricPareto.frontier_selected_optimal packed.pareto.val packed.pareto.property
    (weightOf packed.weights) p h
  have hm := (ParametricPareto.frontier_exact packed.pareto.val packed.pareto.property p).mp hp.1
  rw [packed.catalogue] at hm
  exact hm.1

theorem selected_policy_global (packed : Packed) (p : ParametricPareto.Point)
    (h : selected packed = some p) :
    (∀ policy : Policy (Fin (packed.a + 1)) (Fin (packed.o + 1)) packed.horizon,
      BudgetAdmissible (OnlineController.componentModel packed.table) packed.table.raw.dimensions
        (weightOf packed.budget) packed.state policy →
      ParametricPareto.weighted (List.range packed.table.raw.dimensions) (weightOf packed.weights) p ≤
        ParametricPareto.weighted (List.range packed.table.raw.dimensions) (weightOf packed.weights)
          (point (OnlineController.componentModel packed.table) packed.table.raw.dimensions 0 packed.state policy)) ∧
    (∀ policy : Policy (Fin (packed.a + 1)) (Fin (packed.o + 1)) packed.horizon,
      Admissible (OnlineController.componentModel packed.table) packed.state policy →
      ParametricPareto.dominates (List.range packed.table.raw.dimensions)
        (point (OnlineController.componentModel packed.table) packed.table.raw.dimensions 0 packed.state policy) p = false) := by
  have hp := ParametricPareto.frontier_selected_optimal packed.pareto.val packed.pareto.property
    (weightOf packed.weights) p h
  have hf := (ParametricPareto.frontier_exact packed.pareto.val packed.pareto.property p).mp hp.1
  constructor
  · intro policy valid
    obtain ⟨id, hid⟩ := bounded_catalogue_complete (OnlineController.componentModel packed.table)
      packed.table.raw.dimensions packed.horizon packed.state (weightOf packed.budget) policy valid
    have hm : point (OnlineController.componentModel packed.table) packed.table.raw.dimensions id packed.state policy
        ∈ packed.pareto.val.catalogue := by rw [packed.catalogue]; exact hid
    have hh := hp.2 _ hm
    rw [packed.axes] at hh
    exact hh
  · intro policy valid
    have hfront := (ParametricPareto.frontier_original packed.pareto.val packed.pareto.property p).mp hp.1
    change p ∈ FiniteFrontier.frontier packed.pareto.val.catalogue
      (ParametricPareto.dominates packed.pareto.val.axes) at hfront
    rw [packed.catalogue, packed.axes] at hfront
    exact bounded_frontier_nondominated (OnlineController.componentModel packed.table)
      packed.table.raw.dimensions packed.horizon packed.state (weightOf packed.budget) p hfront policy valid

theorem selectedRecord_corresponds (packed : Packed)
    (record : Record (Fin (packed.n + 1)) (packed.a + 1) (packed.o + 1) packed.horizon)
    (h : selectedRecord packed = some record) :
    BudgetAdmissible (OnlineController.componentModel packed.table) packed.table.raw.dimensions
      (weightOf packed.budget) packed.state record.policy ∧
      ∃ p, selected packed = some p ∧
        p = point (OnlineController.componentModel packed.table) packed.table.raw.dimensions
          record.id packed.state record.policy := by
  cases hp : selected packed with
  | none => simp [selectedRecord, hp] at h
  | some p =>
    have hr : packed.records.val.find? (fun r => r.id == p.id) = some record := by
      simpa [selectedRecord, hp] using h
    have hrid : record.id = p.id := by simpa using List.find?_some hr
    have hrmem := List.mem_of_find?_eq_some hr
    rw [packed.records.property] at hrmem
    have lookupRecord := (cache_record_lookup (OnlineController.componentModel packed.table)
      packed.table.raw.dimensions packed.horizon packed.state record hrmem).1
    obtain ⟨policy, lookupPolicy, valid, he⟩ := catalogue_lookup (OnlineController.componentModel packed.table)
      packed.table.raw.dimensions packed.horizon packed.state p (selected_catalogue packed p hp)
    rw [hrid, lookupPolicy] at lookupRecord
    have hpolicy : policy = record.policy := Option.some.inj lookupRecord
    rw [hpolicy] at valid he
    have hw := (List.mem_filter.mp (selected_bounded packed p hp)).2
    rw [he] at hw
    have hb := (point_within (OnlineController.componentModel packed.table) packed.table.raw.dimensions
      p.id (weightOf packed.budget) packed.state record.policy).mp hw
    exact ⟨⟨valid, hb⟩, p, rfl, by simpa [hrid] using he⟩

theorem selected_prefix_bound (packed : Packed)
    (record : Record (Fin (packed.n + 1)) (packed.a + 1) (packed.o + 1) packed.horizon)
    (h : selectedRecord packed = some record) :
    ∀ i : Fin packed.table.raw.dimensions,
      weightOf packed.spent i.val + worst (OnlineController.componentModel packed.table) i.val packed.state record.policy ≤
        weightOf packed.initialBound i.val := by
  intro i
  have bound := (selectedRecord_corresponds packed record h).1.2 i.val i.isLt
  have ledger := packed.ledger i
  omega

theorem root_outcome_feasible (M : Model Nat S (Fin a) (Fin o)) (dimensions horizon : Nat)
    (budget : Nat → Nat) (state : S) (policy : Policy (Fin a) (Fin o) horizon)
    (action : Fin a) (ha : rootAction policy = some action)
    (valid : BudgetAdmissible M dimensions budget state policy)
    (out : Fin o) (supported : out ∈ M.outcomes state action) :
    (∀ i, i < dimensions → M.cost i state action out ≤ budget i) ∧
      boundedCatalogue M dimensions (horizon - 1) (M.next state action out)
        (fun i => budget i - M.cost i state action out) ≠ [] := by
  cases horizon with
  | zero => cases policy; simp [rootAction] at ha
  | succ h =>
    cases policy with
    | step act after =>
      have he : act = action := by simpa [rootAction] using ha
      subst action
      exact ⟨(budget_continuation M dimensions h budget state act after valid out supported).1,
        budget_continuation_exists M dimensions h budget state act after valid out supported⟩

theorem mapped_value (dimensions : Nat) (f : Nat → Nat) (i : Nat) (hi : i < dimensions) :
    weightOf ((List.range dimensions).map f) i = f i := by
  simp only [weightOf, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem within_budget_congr (dimensions : Nat) (left right : Nat → Nat)
    (same : ∀ i, i < dimensions → left i = right i) (p : ParametricPareto.Point) :
    within dimensions left p = within dimensions right p := by
  apply all_congr
  intro i hi
  rw [same i (List.mem_range.mp hi)]

theorem bounded_budget_congr (M : Model Nat S (Fin a) (Fin o)) (dimensions horizon : Nat)
    (state : S) (left right : Nat → Nat) (same : ∀ i, i < dimensions → left i = right i) :
    boundedCatalogue M dimensions horizon state left = boundedCatalogue M dimensions horizon state right := by
  unfold boundedCatalogue
  have he : within dimensions left = within dimensions right := by
    funext p
    exact within_budget_congr dimensions left right same p
  rw [he]

theorem reconstruct_accepts (old : Packed) (horizon : Nat) (state : Fin (old.n + 1))
    (budget spent : List Nat) (advanceClock : Bool)
    (feasible : boundedCatalogue (OnlineController.componentModel old.table) old.table.raw.dimensions
      horizon state (weightOf budget) ≠ [])
    (ledger : Ledger old.table.raw.dimensions spent budget old.initialBound) :
    ∃ next, reconstruct old horizon state budget spent advanceClock = .ok next := by
  unfold reconstruct
  have hf : (cacheCatalogue (cache (OnlineController.componentModel old.table)
        old.table.raw.dimensions horizon state)).filter
      (within old.table.raw.dimensions (weightOf budget)) ≠ [] := by
    rw [cache_catalogue_exact]
    exact feasible
  dsimp only
  rw [dif_pos hf, dif_pos ledger]
  exact ⟨_, rfl⟩

theorem selected_outcome_accepts (old : Packed)
    (record : Record (Fin (old.n + 1)) (old.a + 1) (old.o + 1) old.horizon)
    (recordFound : selectedRecord old = some record) (action : Fin (old.a + 1))
    (actionFound : rootAction record.policy = some action) (out : Fin (old.o + 1))
    (supported : out ∈ (OnlineController.componentModel old.table).outcomes old.state action) :
    ∃ next, acceptOutcome old out = .ok next := by
  have valid := (selectedRecord_corresponds old record recordFound).1
  have bound := root_outcome_feasible (OnlineController.componentModel old.table)
    old.table.raw.dimensions old.horizon (weightOf old.budget) old.state record.policy
    action actionFound valid out supported
  let spent := (List.range old.table.raw.dimensions).map (fun i =>
    weightOf old.spent i + (OnlineController.componentModel old.table).cost i old.state action out)
  let budget := (List.range old.table.raw.dimensions).map (fun i =>
    weightOf old.budget i - (OnlineController.componentModel old.table).cost i old.state action out)
  have budgetValues : ∀ i, i < old.table.raw.dimensions → weightOf budget i =
      weightOf old.budget i - (OnlineController.componentModel old.table).cost i old.state action out := by
    intro i hi
    exact mapped_value _ _ i hi
  have feasible : boundedCatalogue (OnlineController.componentModel old.table) old.table.raw.dimensions
      (old.horizon - 1) ((OnlineController.componentModel old.table).next old.state action out)
      (weightOf budget) ≠ [] := by
    rw [bounded_budget_congr _ _ _ _ _ _ budgetValues]
    exact bound.2
  have ledger : Ledger old.table.raw.dimensions spent budget old.initialBound := by
    intro i
    change weightOf spent i.val + weightOf budget i.val = _
    rw [mapped_value _ _ i.val i.isLt, budgetValues i.val i.isLt]
    exact budget_ledger_step _ _ _ _ (old.ledger i) (bound.1 i.val i.isLt)
  obtain ⟨next, hn⟩ := reconstruct_accepts old (old.horizon - 1)
    ((OnlineController.componentModel old.table).next old.state action out) budget spent true feasible ledger
  refine ⟨next, ?_⟩
  simpa [acceptOutcome, recordFound, actionFound, supported, budget, spent, weightOf] using hn

theorem selectedRecord_exists (packed : Packed) :
    ∃ record, selectedRecord packed = some record := by
  obtain ⟨p, hp⟩ := ParametricPareto.nonempty_frontier_selects packed.pareto.val packed.pareto.property
    (weightOf packed.weights) packed.feasible
  have hc := selected_catalogue packed p hp
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hc
  let record := materialize (OnlineController.componentModel packed.table) packed.table.raw.dimensions
    i.val packed.state ((policies (packed.a + 1) (packed.o + 1) packed.horizon).get i)
  have hm : record ∈ packed.records.val := by
    rw [packed.records.property]
    exact List.mem_map.mpr ⟨i, (List.mem_filter.mp hi).1, rfl⟩
  have hid : record.id = p.id := congrArg ParametricPareto.Point.id he
  have existsRecord : ∃ r, r ∈ packed.records.val ∧ (r.id == p.id) = true :=
    ⟨record, hm, by simp [hid]⟩
  cases hf : packed.records.val.find? (fun r => r.id == p.id) with
  | none =>
    have some := List.find?_isSome.mpr existsRecord
    simp [hf] at some
  | some result =>
    exact ⟨result, by simp [selectedRecord, selected, hp, hf]⟩

theorem rootAction_exists {a o h : Nat} (policy : Policy (Fin a) (Fin o) h) (positive : 0 < h) :
    ∃ action, rootAction policy = some action := by
  cases h with
  | zero => omega
  | succ h => cases policy with | step a after => exact ⟨a, rfl⟩

theorem positive_session_total (packed : Packed) (positive : 0 < packed.horizon) :
    ∃ record action, selectedRecord packed = some record ∧ rootAction record.policy = some action ∧
      ∀ out, out ∈ (OnlineController.componentModel packed.table).outcomes packed.state action →
        ∃ next, acceptOutcome packed out = .ok next := by
  obtain ⟨record, hr⟩ := selectedRecord_exists packed
  obtain ⟨action, ha⟩ := rootAction_exists record.policy positive
  exact ⟨record, action, hr, ha, fun out ho => selected_outcome_accepts packed record hr action ha out ho⟩

def run : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut state : Option Packed := none
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := do
      let request ← Json.parse line
      step state request
    match result with
    | .error message =>
      output.putStrLn (Json.compress (Json.mkObj [("ok", toJson false), ("error", toJson message)]))
    | .ok (next, observation) =>
      state := some next
      output.putStrLn (Json.compress (Json.mkObj [("ok", toJson true), ("observation", observation)]))
    output.flush

end OnlinePolicy
