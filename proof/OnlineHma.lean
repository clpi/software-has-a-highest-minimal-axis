import CertifiedReplay
import Exponential
import Lean.Data.Json

namespace OnlineHma

open Lean

theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup :=
  HmaExponential.ofFn_nodup n id (fun _ _ h => h)

theorem finRange_complete (n : Nat) (a : Fin n) : a ∈ List.finRange n :=
  List.mem_ofFn.mpr ⟨a, rfl⟩

structure Table (n m : Nat) where
  scope : String
  domains : Array (Array String)
  rows : Array (Array String × Array String)
  edges : List (List (Fin m) × Nat)

def instanceOf {n m : Nat} (table : Table n m) : Hma.Inst (Fin n) String (Fin m) String :=
  let observations := Std.HashMap.ofList (table.rows.toList.map (fun r => (r.1.toList, r.2)))
  { axes := List.finRange n
    axesnodup := finRange_nodup n
    axescomplete := finRange_complete n
    comps := List.finRange m
    contract := table.rows.toList.map (fun r a => (r.1[a.val]?).getD "")
    beh := fun x b => ((observations.getD (List.ofFn x) #[])[b.val]?).getD ""
    edges := table.edges.map Prod.fst
    weight := fun e =>
      let raw := ((table.edges.find? (fun item => decide (item.1 = e))).map Prod.snd).getD 0
      if 2 ≤ e.length then raw + 1 else raw
    weightpos := by intro e he hs; simp only [hs, if_true]; exact Nat.zero_lt_succ _ }

structure Input where
  n : Nat
  m : Nat
  table : Table n m

structure Packed where
  n : Nat
  m : Nat
  table : Table n m
  session : HmaReplay.Session (instanceOf table)

def keys (j : Json) (names : List String) : Except String Unit := do
  let obj ← j.getObj?
  let actual := obj.fold (fun acc name _ => name :: acc) []
  if actual.length = names.length && actual.all names.contains then return ()
  else throw "unexpected or missing object fields"

def stringArray (j : Json) : Except String (Array String) := do
  (← j.getArr?).mapM Json.getStr?

def finList (m : Nat) (j : Json) : Except String (List (Fin m)) := do
  let values ← (← j.getArr?).toList.mapM Json.getNat?
  if !(values.Pairwise (fun a b => a < b)) then throw "edge members must be strictly ordered"
  let result ← values.mapM (fun i => if h : i < m then pure (⟨i, h⟩ : Fin m)
    else throw "component out of range")
  if result.Nodup then return result else throw "duplicate edge component"

def decode (j : Json) : Except String Input := do
  keys j ["axes", "components", "scope", "domains", "rows", "edges"]
  let n ← (← j.getObjVal? "axes").getNat?
  let m ← (← j.getObjVal? "components").getNat?
  let scope ← (← j.getObjVal? "scope").getStr?
  let domains ← (← (← j.getObjVal? "domains").getArr?).mapM stringArray
  if domains.size != n then throw "wrong domain dimensions"
  if !(domains.all (fun values => decide values.toList.Nodup)) then throw "duplicate domain value"
  let rows ← (← (← j.getObjVal? "rows").getArr?).mapM (fun row => do
    let parts ← row.getArr?
    if parts.size != 2 then throw "row must contain axes and observations"
    let x ← stringArray (← row.getArrVal? 0)
    let y ← stringArray (← row.getArrVal? 1)
    if x.size != n || y.size != m then throw "wrong row dimensions"
    if !((List.finRange n).all (fun i => ((domains[i.val]?).getD #[]).contains
        ((x[i.val]?).getD ""))) then throw "configuration outside declared domains"
    pure (x,y))
  if !(rows.toList.map (fun r => r.1.toList)).Nodup then throw "duplicate configuration"
  let edges ← (← (← j.getObjVal? "edges").getArr?).toList.mapM (fun edge => do
    let parts ← edge.getArr?
    if parts.size != 2 then throw "edge must contain members and weight"
    let members ← finList m (← edge.getArrVal? 0)
    let weight ← (← edge.getArrVal? 1).getNat?
    if 2 ≤ members.length && weight = 0 then throw "interacting edge weight must be positive"
    pure (members, if 2 ≤ members.length then weight - 1 else weight))
  if !(edges.map Prod.fst).Nodup then throw "duplicate edge"
  return ⟨n, m, ⟨scope, domains, rows, edges⟩⟩

def numbers (xs : List Nat) : Json := toJson xs
def groups (xs : List (List Nat)) : Json := toJson xs

def snapshotJson {m : Nat} (s : HmaCheck.Snapshot (Fin m)) : Json :=
  Json.mkObj [("live", numbers (s.live.map Fin.val)),
    ("edges", groups (s.edges.map (fun e => e.map Fin.val))),
    ("rho", numbers [s.measure.1, s.measure.2])]

def rowJson {n m : Nat} (r : HmaCertified.Classified (Fin n) (Fin m)) : Json :=
  Json.mkObj [("axes", numbers (r.axes.map Fin.val)), ("live", numbers (r.value.live.map Fin.val)),
    ("edges", groups (r.value.edges.map (fun e => e.map Fin.val))),
    ("rho", numbers [r.value.measure.1, r.value.measure.2]),
    ("sufficient", toJson r.sufficient), ("minimal", toJson r.minimal), ("highest", toJson r.highest)]

def dispositionJson {n : Nat} (d : HmaCertified.Disposition (Fin n)) : Json :=
  let tag := match d.membership with
    | .chosen => "chosen" | .alternative => "alternative" | .none => "none"
  Json.mkObj [("axis", toJson d.axis.val), ("membership", toJson tag),
    ("emergent_dead", toJson d.emergentDead)]

def resultJson {n m : Nat} (r : HmaCertified.Rendered (Fin n) (Fin m)) : Json :=
  Json.mkObj [("full", snapshotJson r.full), ("subsets", toJson (r.subsets.map rowJson)),
    ("minimal", groups (r.minimal.map (fun xs => xs.map Fin.val))),
    ("highest", groups (r.highest.map (fun xs => xs.map Fin.val))),
    ("chosen", match r.chosen with | none => Json.null | some xs => numbers (xs.map Fin.val)),
    ("dispositions", toJson (r.dispositions.map dispositionJson))]

def qualifiedRows {n m : Nat} (r : HmaCertified.Rendered (Fin n) (Fin m)) :
    List (HmaCertified.Classified (Fin n) (Fin m)) := r.subsets.filter (·.minimal)

theorem qualifiedRows_exact {n m : Nat} (I : Hma.Inst (Fin n) String (Fin m) String)
    (output : HmaReplay.Output I) (r : HmaCertified.Classified (Fin n) (Fin m)) :
    r ∈ qualifiedRows output.value ↔
      r ∈ output.value.subsets ∧ Hma.minimal I (HmaCheck.axisSet r.axes) := by
  simp only [qualifiedRows, List.mem_filter]
  constructor
  · intro h
    exact ⟨h.1, ((output.correct.subsets r h.1).2.2.2.1).mp h.2⟩
  · intro h
    exact ⟨h.1, ((output.correct.subsets r h.1).2.2.2.1).mpr h.2⟩

theorem qualifiedRows_cover {n m : Nat} (I : Hma.Inst (Fin n) String (Fin m) String)
    (output : HmaReplay.Output I) (S : Fin n → Bool) (h : Hma.minimal I S) :
    ∃ r ∈ qualifiedRows output.value, HmaCheck.axisSet r.axes = S := by
  obtain ⟨r, hr, heq⟩ := output.correct.coverage S
  refine ⟨r, (qualifiedRows_exact I output r).mpr ⟨hr, ?_⟩, heq⟩
  simpa only [heq] using h

def minimalRowJson {n m : Nat} (r : HmaCertified.Classified (Fin n) (Fin m)) : Json :=
  Json.mkObj [("axes", numbers (r.axes.map Fin.val)),
    ("rho", numbers [r.value.measure.1, r.value.measure.2])]

def observe (packed : Packed) (additions removals : Nat) : Except String Json := do
  let I := instanceOf packed.table
  let some output := HmaReplay.finish I packed.session.state HmaCertified.finLexPrefer
    | throw "carried rows do not match requested input"
  let mut cells : List Json := []
  for D in Hma.sublists I.axes do
    for b in I.comps do
      let count := HmaExecutable.read packed.session.state.val.hist (D,b)
      if count > 0 then
        cells := Json.arr #[numbers (D.map Fin.val), toJson b.val, toJson count] :: cells
  let rows := (packed.session.state.val.rows.map (fun x =>
    Json.arr #[toJson (List.ofFn x), toJson (List.ofFn (I.beh x))])).mergeSort
      (fun left right => left.compress ≤ right.compress)
  let support := (Hma.sublists I.axes).map (fun S =>
    Json.arr #[numbers (S.map Fin.val), numbers (I.comps.map (fun b =>
      HmaReplay.occupancy I packed.session.state.val (HmaCheck.axisSet S) b))])
  let profiles := (qualifiedRows output.value).map minimalRowJson
  return Json.mkObj [("next_seq", toJson packed.session.nextSeq), ("epoch", toJson packed.session.epoch),
    ("pair_additions", toJson additions), ("pair_removals", toJson removals),
    ("rows", toJson rows), ("cells", toJson cells.reverse), ("support", toJson support),
    ("result", resultJson output.value), ("minimal_rows", toJson profiles)]

def start (input : Input) : Packed :=
  ⟨input.n, input.m, input.table,
    ⟨HmaReplay.start (instanceOf input.table) (finRange_nodup input.m), 1, 0⟩⟩

def advance (old : Packed) (input : Input) (seq epoch : Nat) : Except String (Packed × Nat × Nat) := do
  if old.table.scope != input.table.scope then throw "schema scope changed without rebase"
  if old.table.domains != input.table.domains then throw "domains changed without rebase"
  if hn : input.n = old.n then
    if hm : input.m = old.m then
      let table : Table old.n old.m := hn ▸ hm ▸ input.table
      let some (session, additions, removals) := HmaReplay.advance (instanceOf old.table)
        (instanceOf table) old.session seq epoch | throw "rejected incremental transition"
      return (⟨old.n, old.m, table, session⟩, additions, removals)
    else throw "component dimensions changed without rebase"
  else throw "axis dimensions changed without rebase"

def rebase (old : Packed) (input : Input) (seq epoch : Nat) : Except String Packed := do
  let some session := HmaReplay.rebase (instanceOf old.table) (instanceOf input.table)
    (finRange_nodup input.m) old.session seq epoch | throw "rejected rebase clock"
  return ⟨input.n, input.m, input.table, session⟩

def checkpoint (old : Packed) : Packed :=
  ⟨old.n, old.m, old.table,
    ⟨HmaReplay.start (instanceOf old.table) (finRange_nodup old.m),
      old.session.nextSeq, old.session.epoch⟩⟩

def step (old : Option Packed) (request : Json) : Except String (Packed × Json) := do
  let op ← (← request.getObjVal? "op").getStr?
  if op = "start" then
    keys request ["op", "input"]
    if old.isSome then throw "session already started"
    let input ← decode (← request.getObjVal? "input")
    let next := start input
    let work := input.table.rows.size * (input.table.rows.size - 1) / 2
    return (next, ← observe next work 0)
  else
    let some old := old | throw "session not started"
    let seq ← (← request.getObjVal? "seq").getNat?
    let epoch ← (← request.getObjVal? "epoch").getNat?
    if seq != old.session.nextSeq || epoch != old.session.epoch then throw "stale sequence or epoch"
    if op = "advance" || op = "rebase" then
      keys request ["op", "seq", "epoch", "input"]
      let input ← decode (← request.getObjVal? "input")
      if op = "advance" then
        let (next, additions, removals) ← advance old input seq epoch
        return (next, ← observe next additions removals)
      else
        let next ← rebase old input seq epoch
        let work := input.table.rows.size * (input.table.rows.size - 1) / 2
        return (next, ← observe next work 0)
    else if op = "checkpoint" || op = "inspect" then
      keys request ["op", "seq", "epoch"]
      let next := if op = "checkpoint" then checkpoint old else old
      let work := if op = "checkpoint" then old.table.rows.size * (old.table.rows.size - 1) / 2 else 0
      return (next, ← observe next work 0)
    else throw "unknown operation"

theorem carried_valid (packed : Packed) :
    HmaExecutable.Valid (instanceOf packed.table) packed.session.state.val :=
  packed.session.state.property

theorem checkpoint_clock (packed : Packed) :
    (checkpoint packed).session.nextSeq = packed.session.nextSeq ∧
      (checkpoint packed).session.epoch = packed.session.epoch := ⟨rfl, rfl⟩

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

end OnlineHma
