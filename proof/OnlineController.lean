import IncrementalControl
import OnlineHma
import Lean.Data.Json

namespace OnlineController

open Lean

structure Branch (n o : Nat) where
  id : Fin (o + 1)
  next : Fin (n + 1)
  costs : List Nat
  deriving DecidableEq, Repr

structure Action (n a o : Nat) where
  id : Fin (a + 1)
  branches : List (Branch n o)
  deriving DecidableEq, Repr

structure Row (n a o : Nat) where
  terminal : List Nat
  actions : List (Action n a o)
  deriving DecidableEq, Repr

structure Raw (n a o : Nat) where
  dimensions : Nat
  rows : Array (Row n a o)

def row {n a o : Nat} (raw : Raw n a o) (s : Fin (n + 1)) : Row n a o :=
  (raw.rows[s.val]?).getD ⟨[], []⟩

def action {n a o : Nat} (raw : Raw n a o) (s : Fin (n + 1)) (act : Fin (a + 1)) :
    Option (Action n a o) := (row raw s).actions.find? (fun item => item.id == act)

def branches {n a o : Nat} (raw : Raw n a o) (s : Fin (n + 1)) (act : Fin (a + 1)) :
    List (Branch n o) := ((action raw s act).map Action.branches).getD []

def branch {n a o : Nat} (raw : Raw n a o) (s : Fin (n + 1)) (act : Fin (a + 1))
    (out : Fin (o + 1)) : Branch n o :=
  ((branches raw s act).find? (fun item => item.id == out)).getD ⟨0, 0, []⟩

def actions {n a o : Nat} (raw : Raw n a o) (s : Fin (n + 1)) : List (Fin (a + 1)) :=
  (row raw s).actions.map Action.id

def outcomes {n a o : Nat} (raw : Raw n a o) (s : Fin (n + 1)) (act : Fin (a + 1)) :
    List (Fin (o + 1)) := (branches raw s act).map Branch.id

def Admitted {n a o : Nat} (raw : Raw n a o) : Prop :=
  ∀ s, actions raw s ≠ [] ∧ ∀ act ∈ actions raw s, outcomes raw s act ≠ []

instance {n a o : Nat} (raw : Raw n a o) : Decidable (Admitted raw) := by
  unfold Admitted
  infer_instance

structure Table (n a o : Nat) where
  raw : Raw n a o
  admitted : Admitted raw

def weighted (weights costs : List Nat) : Nat :=
  ((List.range weights.length).map (fun i => (weights[i]?).getD 0 * (costs[i]?).getD 0)).sum

def model {n a o : Nat} (table : Table n a o) :
    OptimalController.Model (List Nat) (Fin (n + 1)) (Fin (a + 1)) (Fin (o + 1)) where
  actions := actions table.raw
  actionsNonempty := fun s => (table.admitted s).1
  outcomes := outcomes table.raw
  outcomesNonempty := fun s act ha => (table.admitted s).2 act ha
  next := fun s act out => (branch table.raw s act out).next
  cost := fun p s act out => weighted p (branch table.raw s act out).costs
  terminal := fun p s => weighted p (row table.raw s).terminal

def componentModel {n a o : Nat} (table : Table n a o) :
    OptimalController.Model Nat (Fin (n + 1)) (Fin (a + 1)) (Fin (o + 1)) where
  actions := actions table.raw
  actionsNonempty := fun s => (table.admitted s).1
  outcomes := outcomes table.raw
  outcomesNonempty := fun s act ha => (table.admitted s).2 act ha
  next := fun s act out => (branch table.raw s act out).next
  cost := fun i s act out => ((branch table.raw s act out).costs[i]?).getD 0
  terminal := fun i s => ((row table.raw s).terminal[i]?).getD 0

def natList (j : Json) : Except String (List Nat) := do
  (← j.getArr?).toList.mapM Json.getNat?

def bounded (bound : Nat) (j : Json) : Except String (Fin bound) := do
  let i ← j.getNat?
  if h : i < bound then return ⟨i, h⟩ else throw "finite identifier out of range"

def costList (d : Nat) (j : Json) : Except String (List Nat) := do
  let xs ← natList j
  if xs.length != d then throw "cost/parameter dimension mismatch"
  return xs

structure Input where
  n : Nat
  a : Nat
  o : Nat
  table : Table n a o

def decode (j : Json) : Except String Input := do
  OnlineHma.keys j ["actions", "outcomes", "dimensions", "states"]
  let actionCount ← (← j.getObjVal? "actions").getNat?
  let outcomeCount ← (← j.getObjVal? "outcomes").getNat?
  let d ← (← j.getObjVal? "dimensions").getNat?
  let states ← (← j.getObjVal? "states").getArr?
  if actionCount = 0 || outcomeCount = 0 || states.size = 0 then
    throw "controller carriers must be nonempty"
  let n := states.size - 1
  let a := actionCount - 1
  let o := outcomeCount - 1
  let rows ← states.mapM (fun state => do
    OnlineHma.keys state ["terminal", "actions"]
    let terminal ← costList d (← state.getObjVal? "terminal")
    let acts ← (← (← state.getObjVal? "actions").getArr?).toList.mapM (fun act => do
      OnlineHma.keys act ["id", "outcomes"]
      let id ← bounded (a + 1) (← act.getObjVal? "id")
      let outs ← (← (← act.getObjVal? "outcomes").getArr?).toList.mapM (fun out => do
        OnlineHma.keys out ["id", "next", "costs"]
        let id ← bounded (o + 1) (← out.getObjVal? "id")
        let next ← bounded (n + 1) (← out.getObjVal? "next")
        let costs ← costList d (← out.getObjVal? "costs")
        return (⟨id, next, costs⟩ : Branch n o))
      if outs.isEmpty || !(outs.map Branch.id).Nodup then
        throw "empty or duplicate supported outcomes"
      return (⟨id, outs⟩ : Action n a o))
    if acts.isEmpty || !(acts.map Action.id).Nodup then
      throw "empty or duplicate admitted actions"
    return (⟨terminal, acts⟩ : Row n a o))
  let raw : Raw n a o := ⟨d, rows⟩
  if h : Admitted raw then return ⟨n, a, o, ⟨raw, h⟩⟩
  else throw "model lacks an action or outcome for a finite state"

structure Packed where
  n : Nat
  a : Nat
  o : Nat
  horizon : Nat
  table : Table n a o
  weights : List Nat
  cache : IncrementalControl.Certified (model table) weights horizon
  state : Fin (n + 1)
  nextSeq : Nat
  epoch : Nat
  spent : List Nat
  cumulativeWork : Nat

def layerJson {S : Type} (encode : S → Json) (layer : IncrementalControl.Layer S) : Json :=
  Json.mkObj [("values", toJson (layer.table.map (fun (s,v) => Json.arr #[encode s, toJson v]))),
    ("changed", toJson (layer.changed.map encode)), ("recomputed", toJson (layer.recomputed.map encode))]

def cacheJson {n : Nat} : {h : Nat} → IncrementalControl.Cache (Fin (n + 1)) h → List Json
  | _, .zero top => [layerJson (fun s => toJson s.val) top]
  | _, .succ top lower => cacheJson lower ++ [layerJson (fun s => toJson s.val) top]

def chosen (packed : Packed) : Option Nat :=
  match h : packed.horizon with
  | 0 => none
  | k + 1 =>
    let cache : IncrementalControl.Certified (model packed.table) packed.weights (k + 1) :=
      Eq.mp (congrArg (fun h => IncrementalControl.Certified (model packed.table) packed.weights h) h) packed.cache
    some (IncrementalControl.select (model packed.table) packed.weights cache packed.state).val

def observe (packed : Packed) (work : Nat) : Json :=
  Json.mkObj [("state", toJson packed.state.val), ("remaining", toJson packed.horizon),
    ("next_seq", toJson packed.nextSeq), ("epoch", toJson packed.epoch),
    ("chosen", toJson (chosen packed)), ("spent", toJson (weighted packed.weights packed.spent)),
    ("spent_vector", toJson packed.spent),
    ("value", toJson (IncrementalControl.value (model packed.table) packed.weights packed.cache packed.state)),
    ("recomputed_cells", toJson work), ("cumulative_cells", toJson packed.cumulativeWork),
    ("stored_cells", toJson packed.cache.val.cells), ("layers", toJson (cacheJson packed.cache.val))]

def start (input : Input) (weights : List Nat) (horizon : Nat)
    (state : Fin (input.n + 1)) : Packed :=
  let cache := IncrementalControl.start (List.finRange (input.n + 1))
    (OnlineHma.finRange_complete _) (model input.table) weights horizon
  ⟨input.n, input.a, input.o, horizon, input.table, weights, cache, state, 1, 0,
    List.replicate input.table.raw.dimensions 0, cache.val.work⟩

def revise (old : Packed) (input : Input) (weights : List Nat) : Except String Packed := do
  if hn : input.n = old.n then
    if ha : input.a = old.a then
      if ho : input.o = old.o then
        let table : Table old.n old.a old.o := hn ▸ ha ▸ ho ▸ input.table
        if table.raw.dimensions != old.table.raw.dimensions then throw "dimension change requires rebase"
        let cache := IncrementalControl.update (List.finRange (old.n + 1))
          (OnlineHma.finRange_complete _) (model old.table) (model table) old.weights weights old.cache
        return ⟨old.n, old.a, old.o, old.horizon, table, weights, cache, old.state,
          old.nextSeq + 1, old.epoch, old.spent, old.cumulativeWork + cache.val.work⟩
      else throw "outcome universe change requires rebase"
    else throw "action universe change requires rebase"
  else throw "state universe change requires rebase"

def acceptOutcome (old : Packed) (out : Fin (old.o + 1)) : Except String Packed := do
  match hh : old.horizon with
  | 0 => throw "no remaining decision horizon"
  | h + 1 =>
    let cache : IncrementalControl.Certified (model old.table) old.weights (h + 1) :=
      Eq.mp (congrArg (fun h => IncrementalControl.Certified (model old.table) old.weights h) hh) old.cache
    let act := IncrementalControl.select (model old.table) old.weights cache old.state
    if out ∉ (model old.table).outcomes old.state act then throw "unsupported empirical outcome"
    let next := (model old.table).next old.state act out
    match cache.val, cache.property with
    | .succ _ lower, valid =>
      return ⟨old.n, old.a, old.o, h, old.table, old.weights, ⟨lower, valid.2⟩, next,
        old.nextSeq + 1, old.epoch,
        (List.range old.weights.length).map (fun i => (old.spent[i]?).getD 0 +
          ((branch old.table.raw old.state act out).costs[i]?).getD 0), old.cumulativeWork⟩

def step (old : Option Packed) (request : Json) : Except String (Packed × Json) := do
  let op ← (← request.getObjVal? "op").getStr?
  if op = "start" then
    OnlineHma.keys request ["op", "model", "weights", "horizon", "state"]
    if old.isSome then throw "controller already started"
    let input ← decode (← request.getObjVal? "model")
    let weights ← costList input.table.raw.dimensions (← request.getObjVal? "weights")
    let horizon ← (← request.getObjVal? "horizon").getNat?
    let state ← bounded (input.n + 1) (← request.getObjVal? "state")
    let next := start input weights horizon state
    return (next, observe next next.cache.val.work)
  else
    let some old := old | throw "controller not started"
    let seq ← (← request.getObjVal? "seq").getNat?
    let epoch ← (← request.getObjVal? "epoch").getNat?
    if seq != old.nextSeq || epoch != old.epoch then throw "stale controller sequence or epoch"
    if op = "revise" then
      OnlineHma.keys request ["op", "seq", "epoch", "model", "weights"]
      let input ← decode (← request.getObjVal? "model")
      let weights ← costList input.table.raw.dimensions (← request.getObjVal? "weights")
      let next ← revise old input weights
      return (next, observe next next.cache.val.work)
    else if op = "parameters" then
      OnlineHma.keys request ["op", "seq", "epoch", "weights"]
      let weights ← costList old.table.raw.dimensions (← request.getObjVal? "weights")
      let next ← revise old ⟨old.n, old.a, old.o, old.table⟩ weights
      return (next, observe next next.cache.val.work)
    else if op = "outcome" then
      OnlineHma.keys request ["op", "seq", "epoch", "outcome"]
      let out ← bounded (old.o + 1) (← request.getObjVal? "outcome")
      let next ← acceptOutcome old out
      return (next, observe next 0)
    else if op = "rebase" then
      OnlineHma.keys request ["op", "seq", "epoch", "model", "weights", "horizon", "state"]
      let input ← decode (← request.getObjVal? "model")
      let weights ← costList input.table.raw.dimensions (← request.getObjVal? "weights")
      let horizon ← (← request.getObjVal? "horizon").getNat?
      let state ← bounded (input.n + 1) (← request.getObjVal? "state")
      let next := start input weights horizon state
      let next := { next with
        nextSeq := old.nextSeq + 1
        epoch := old.epoch + 1
        cumulativeWork := old.cumulativeWork + next.cache.val.work }
      return (next, observe next next.cache.val.work)
    else if op = "checkpoint" || op = "inspect" then
      OnlineHma.keys request ["op", "seq", "epoch"]
      if op = "inspect" then return (old, observe old 0)
      let cache := IncrementalControl.start (List.finRange (old.n + 1))
        (OnlineHma.finRange_complete _) (model old.table) old.weights old.horizon
      let next := {old with cache := cache, cumulativeWork := old.cumulativeWork + cache.val.work}
      return (next, observe next next.cache.val.work)
    else throw "unknown controller operation"

theorem carried_optimal (packed : Packed)
    (policy : OptimalController.Policy (Fin (packed.a + 1)) (Fin (packed.o + 1)) packed.horizon)
    (admissible : OptimalController.Admissible (model packed.table) packed.state policy) :
    IncrementalControl.value (model packed.table) packed.weights packed.cache packed.state ≤
      OptimalController.worst (model packed.table) packed.weights packed.state policy :=
  IncrementalControl.value_optimal _ _ _ _ policy admissible

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

end OnlineController
