import OnlineHma
import HmaPareto

namespace OnlinePareto

open Lean ParametricPareto

structure HmaContext where
  packed : OnlineHma.Packed
  output : HmaReplay.Output (OnlineHma.instanceOf packed.table)
  resources : Array Int

structure Session where
  state : Certified
  weights : Array Nat
  nextSeq : Nat
  epoch : Nat
  cumulativeComparisons : Nat
  hma : Option HmaContext
  parameterRegions : List Region
  parameterRegionsExact : parameterRegions = regions state.val

def mask {n : Nat} (axes : List (Fin n)) : Nat :=
  (axes.map (fun a => 2 ^ a.val)).sum

def resourceOf {n : Nat} (values : Array Int) (a : Fin n) : Int :=
  (values[a.val]?).getD 0

def weightOf (values : Array Nat) (i : Nat) : Nat := (values[i]?).getD 0

def intArray (value : Json) : Except String (Array Int) := do
  (← value.getArr?).mapM Json.getInt?

def natArray (value : Json) : Except String (Array Nat) := do
  (← value.getArr?).mapM Json.getNat?

def decodeWeights (n : Nat) (value : Json) : Except String (Array Nat) := do
  let result ← natArray value
  if result.size != n then throw "wrong parameter dimensions"
  return result

def decodeResources (n : Nat) (value : Json) : Except String (Array Int) := do
  let result ← intArray value
  if result.size != n then throw "wrong resource dimensions"
  return result

def decodeCatalogue (n : Nat) (value : Json) : Except String (List Point) := do
  let points ← (← value.getArr?).toList.mapM (fun item => do
    OnlineHma.keys item ["id","profile"]
    let id ← (← item.getObjVal? "id").getNat?
    let profile ← intArray (← item.getObjVal? "profile")
    if profile.size != n then throw "wrong profile dimensions"
    pure (⟨id,profile.toList⟩ : Point))
  if !((points.map Point.id).Pairwise (fun a b => a < b)) then
    throw "candidate identities must be unique and strictly ordered"
  return points

def pointJson (p : Point) : Json :=
  Json.mkObj [("id",toJson p.id),("profile",toJson p.profile)]

def cellJson (c : Cell) : Json :=
  Json.arr #[toJson c.left.id,toJson c.right.id,toJson c.value]

def regionJson (r : Region) : Json :=
  Json.mkObj [("point",toJson r.point.id),("inequalities",toJson (r.inequalities.map (fun row =>
    Json.mkObj [("against",toJson row.against.id),
      ("coefficients",toJson (row.terms.map Prod.snd))])))]

def selectCurrent (session : Session) : Option Point :=
  choose (key session.state.val.axes (weightOf session.weights))
    (session.parameterRegions.map Region.point)

theorem selectCurrent_eq (session : Session) :
    selectCurrent session = selectFrontier session.state.val (weightOf session.weights) := by
  unfold selectCurrent selectFrontier
  rw [session.parameterRegionsExact, region_points]

def observation (session : Session) (needed reused : Nat)
    (hmaObservation : Json := Json.null) : Json :=
  let current := session.state.val
  let chosen := selectCurrent session
  Json.mkObj [("next_seq",toJson session.nextSeq),("epoch",toJson session.epoch),
    ("dimensions",toJson current.axes.length),("weights",toJson session.weights),
    ("catalogue",toJson (current.catalogue.map pointJson)),
    ("frontier",toJson ((session.parameterRegions.map Region.point).map pointJson)),
    ("regions",toJson (session.parameterRegions.map regionJson)),
    ("active_regions",toJson ((session.parameterRegions.filter
      (acceptsParameters (weightOf session.weights))).map (fun r => r.point.id))),
    ("selected",match chosen with | none => Json.null | some p => pointJson p),
    ("weighted_cost",match chosen with | none => Json.null | some p => toJson (weighted current.axes (weightOf session.weights) p)),
    ("comparisons",toJson (current.comparisons.map cellJson)),
    ("comparisons_needed",toJson needed),("comparisons_reused",toJson reused),
    ("cumulative_comparisons",toJson session.cumulativeComparisons),
    ("hma_result",match session.hma with | none => Json.null | some h => OnlineHma.resultJson h.output.value),
    ("resources",match session.hma with | none => Json.null | some h => toJson h.resources),
    ("hma_observation",hmaObservation)]

def finishHma (packed : OnlineHma.Packed) (resources : Array Int) : Except String HmaContext := do
  let some output := HmaReplay.finish (OnlineHma.instanceOf packed.table)
    packed.session.state HmaCertified.finLexPrefer
    | throw "HMA current input did not certify"
  let points := HmaPareto.candidates output mask (resourceOf resources)
  if !(points.map Point.id).Nodup then throw "HMA subset identity collision"
  return ⟨packed,output,resources⟩

def fromHma (hma : HmaContext) : Certified :=
  HmaPareto.start hma.output mask (resourceOf hma.resources)

def updateHma (old : Certified) (hma : HmaContext) : Certified :=
  HmaPareto.advance old hma.output mask (resourceOf hma.resources)

def internalRequest (old : OnlineHma.Packed) (op : String) (input : Json) : Json :=
  Json.mkObj [("op",toJson op),("seq",toJson old.session.nextSeq),
    ("epoch",toJson old.session.epoch),("input",input)]

def step (old : Option Session) (request : Json) : Except String (Session × Json) := do
  let op ← (← request.getObjVal? "op").getStr?
  if op = "start" then
    OnlineHma.keys request ["op","dimensions","catalogue","weights"]
    if old.isSome then throw "session already started"
    let n ← (← request.getObjVal? "dimensions").getNat?
    let points ← decodeCatalogue n (← request.getObjVal? "catalogue")
    let weights ← decodeWeights n (← request.getObjVal? "weights")
    let work := points.length * points.length
    let state := ParametricPareto.start (List.range n) points
    let next : Session := ⟨state,weights,1,0,work,none,regions state.val,rfl⟩
    return (next,observation next work 0)
  else if op = "hma_start" then
    OnlineHma.keys request ["op","input","resources","weights"]
    if old.isSome then throw "session already started"
    let input ← request.getObjVal? "input"
    let command := Json.mkObj [("op",toJson "start"),("input",input)]
    let (packed,receipt) ← OnlineHma.step none command
    let resources ← decodeResources packed.n (← request.getObjVal? "resources")
    let weights ← decodeWeights 3 (← request.getObjVal? "weights")
    let hma ← finishHma packed resources
    let state := fromHma hma
    let work := state.val.catalogue.length * state.val.catalogue.length
    let next : Session := ⟨state,weights,1,0,work,some hma,regions state.val,rfl⟩
    return (next,observation next work 0 receipt)
  else
    let some old := old | throw "session not started"
    let seq ← (← request.getObjVal? "seq").getNat?
    let epoch ← (← request.getObjVal? "epoch").getNat?
    if seq != old.nextSeq || epoch != old.epoch then throw "stale sequence or epoch"
    if op = "weights" then
      OnlineHma.keys request ["op","seq","epoch","weights"]
      let weights ← decodeWeights old.state.val.axes.length (← request.getObjVal? "weights")
      let next := {old with weights := weights, nextSeq := old.nextSeq + 1}
      return (next,observation next 0 0)
    else if op = "inspect" then
      OnlineHma.keys request ["op","seq","epoch"]
      return (old,observation old 0 0)
    else if op = "reconcile" || op = "rebase" then
      if old.hma.isSome then throw "generic catalogue update in HMA mode"
      let rebase := op = "rebase"
      OnlineHma.keys request (if rebase then
        ["op","seq","epoch","dimensions","catalogue","weights"] else
        ["op","seq","epoch","catalogue"])
      let n ← if rebase then (← request.getObjVal? "dimensions").getNat?
        else pure old.state.val.axes.length
      let points ← decodeCatalogue n (← request.getObjVal? "catalogue")
      let weights ← if rebase then decodeWeights n (← request.getObjVal? "weights") else pure old.weights
      let axes := List.range n
      let work := if rebase then points.length * points.length
        else comparisonsNeeded old.state.val axes points
      let reused := if rebase then 0 else comparisonsReused old.state.val axes points
      let state := if rebase then ParametricPareto.start axes points
        else ParametricPareto.advance old.state axes points
      let next : Session := ⟨state,weights,old.nextSeq+1,
        old.epoch+(if rebase then 1 else 0),old.cumulativeComparisons+work,none,regions state.val,rfl⟩
      return (next,observation next work reused)
    else if op = "hma_advance" || op = "hma_rebase" then
      OnlineHma.keys request ["op","seq","epoch","input","resources"]
      let some context := old.hma | throw "HMA update in generic catalogue mode"
      let rebase := op = "hma_rebase"
      let input ← request.getObjVal? "input"
      let command := internalRequest context.packed (if rebase then "rebase" else "advance") input
      let (packed,receipt) ← OnlineHma.step (some context.packed) command
      let resources ← decodeResources packed.n (← request.getObjVal? "resources")
      let hma ← finishHma packed resources
      let points := HmaPareto.candidates hma.output mask (resourceOf resources)
      let work := if rebase then points.length * points.length
        else comparisonsNeeded old.state.val [0,1,2] points
      let reused := if rebase then 0 else comparisonsReused old.state.val [0,1,2] points
      let state := if rebase then fromHma hma else updateHma old.state hma
      let next : Session := ⟨state,old.weights,old.nextSeq+1,
        old.epoch+(if rebase then 1 else 0),old.cumulativeComparisons+work,some hma,regions state.val,rfl⟩
      return (next,observation next work reused receipt)
    else if op = "resources" then
      OnlineHma.keys request ["op","seq","epoch","resources"]
      let some context := old.hma | throw "resources need an HMA session"
      let resources ← decodeResources context.packed.n (← request.getObjVal? "resources")
      let hma := {context with resources := resources}
      let points := HmaPareto.candidates hma.output mask (resourceOf resources)
      let work := comparisonsNeeded old.state.val [0,1,2] points
      let reused := comparisonsReused old.state.val [0,1,2] points
      let state := updateHma old.state hma
      let next : Session := ⟨state,old.weights,old.nextSeq+1,old.epoch,
        old.cumulativeComparisons+work,some hma,regions state.val,rfl⟩
      return (next,observation next work reused)
    else throw "unknown operation"

theorem carried_valid (session : Session) : Valid session.state.val := session.state.property

theorem selection_globally_optimal (session : Session) (p : Point)
    (h : selectCurrent session = some p) :
    p ∈ frontier session.state.val ∧ ∀ q ∈ session.state.val.catalogue,
      weighted session.state.val.axes (weightOf session.weights) p ≤
      weighted session.state.val.axes (weightOf session.weights) q :=
  certified_selection session.state (weightOf session.weights) p ((selectCurrent_eq session).symm.trans h)

theorem cached_regions_exact (session : Session) (r : Region)
    (hr : r ∈ session.parameterRegions) (weights : Nat → Nat) :
    r.point ∈ frontier session.state.val ∧
      (acceptsParameters weights r = true ↔
        ∀ q ∈ session.state.val.catalogue,
          weighted session.state.val.axes weights r.point ≤ weighted session.state.val.axes weights q) := by
  rw [session.parameterRegionsExact] at hr
  exact region_member_exact session.state.val r hr weights

theorem hma_start_qualified (hma : HmaContext) (p : Point)
    (hp : p ∈ (fromHma hma).val.catalogue) :
    ∃ axes, axes ∈ Hma.sublists (OnlineHma.instanceOf hma.packed.table).axes ∧
      Hma.minimal (OnlineHma.instanceOf hma.packed.table) (HmaCheck.axisSet axes) ∧
      p = HmaPareto.idealPoint (OnlineHma.instanceOf hma.packed.table) mask
        (resourceOf hma.resources) axes :=
  (HmaPareto.candidates_exact _ hma.output mask (resourceOf hma.resources) p).mp hp

theorem hma_update_qualified (old : Certified) (hma : HmaContext) (p : Point)
    (hp : p ∈ (updateHma old hma).val.catalogue) :
    ∃ axes, axes ∈ Hma.sublists (OnlineHma.instanceOf hma.packed.table).axes ∧
      Hma.minimal (OnlineHma.instanceOf hma.packed.table) (HmaCheck.axisSet axes) ∧
      p = HmaPareto.idealPoint (OnlineHma.instanceOf hma.packed.table) mask
        (resourceOf hma.resources) axes :=
  (HmaPareto.candidates_exact _ hma.output mask (resourceOf hma.resources) p).mp hp

def run : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  let mut state : Option Session := none
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := do
      let request ← Json.parse line
      step state request
    match result with
    | .error message =>
      output.putStrLn (Json.compress (Json.mkObj [("ok",toJson false),("error",toJson message)]))
    | .ok (next,receipt) =>
      state := some next
      output.putStrLn (Json.compress (Json.mkObj [("ok",toJson true),("observation",receipt)]))
    output.flush

end OnlinePareto
