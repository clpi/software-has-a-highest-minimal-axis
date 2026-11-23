import HmaPareto
import Controls
import IncrementalControl
import ParetoPolicy

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace ReasoningControls

def xOutput : HmaReplay.Output Ctl.instx :=
  ⟨HmaCertified.render Ctl.instx (Hma.livelist Ctl.instx) HmaCertified.finLexPrefer,
    HmaCertified.render_correct Ctl.instx (Hma.livelist Ctl.instx) (fun _ => rfl)
      HmaCertified.finLexPrefer⟩

def mask (axes : List (Fin 3)) : Nat := (axes.map (fun a => 2 ^ a.val)).sum

def resource (a : Fin 3) : Int := if a.val = 0 then 10 else 0

def xPareto := HmaPareto.start xOutput mask resource

theorem original_x_choice_preserved : xOutput.value.chosen = some [0] := by decide

theorem x_complete_parametric_frontier :
    (ParametricPareto.frontier xPareto.val).map (fun p => (p.id, p.profile)) =
      [(4, [1, -2, 0]), (1, [1, -3, 10])] := by decide

theorem x_liveness_parameter :
    (ParametricPareto.selectFrontier xPareto.val (fun i => if i = 1 then 1 else 0)).map (·.id) =
      some 1 := by decide

theorem x_resource_parameter :
    (ParametricPareto.selectFrontier xPareto.val (fun i => if i = 0 then 0 else 1)).map (·.id) =
      some 4 := by decide

def points : List ParametricPareto.Point :=
  [⟨0, [0, 3]⟩, ⟨1, [1, 1]⟩, ⟨2, [3, 0]⟩, ⟨3, [2, 2]⟩, ⟨4, [1, 1]⟩]

def pointCache := ParametricPareto.start [0,1] points

theorem equal_profiles_keep_identities :
    (ParametricPareto.frontier pointCache.val).map (·.id) = [0,1,2,4] := by decide

theorem zero_parameters_stay_pareto :
    (ParametricPareto.selectFrontier pointCache.val (fun _ => 0)).map (·.id) = some 1 := by decide

def withdrawn := ParametricPareto.advance pointCache [0,1] (points.filter (fun p => p.id != 1 && p.id != 4))

theorem withdrawn_dominators_resurrect :
    (ParametricPareto.frontier withdrawn.val).map (·.id) = [0,2,3] := by decide

theorem withdrawal_reuses_all_comparisons :
    ParametricPareto.comparisonsNeeded pointCache.val [0,1] withdrawn.val.catalogue = 0 := by decide

def chain : OptimalController.Model Nat (Fin 4) (Fin 1) (Fin 1) where
  actions := fun _ => [0]
  actionsNonempty := by intro s; simp
  outcomes := fun _ _ => [0]
  outcomesNonempty := by intro s a ha; simp
  next := fun s _ _ => if s.val = 0 then 1 else if s.val = 1 then 2 else s
  cost := fun _ _ _ _ => 0
  terminal := fun p s => if s.val = 2 then p else 0

def chainCache := IncrementalControl.start (List.finRange 4)
  (fun a => List.mem_ofFn.mpr ⟨a, rfl⟩) chain 1 3

def changedChain := IncrementalControl.update (List.finRange 4)
  (fun a => List.mem_ofFn.mpr ⟨a, rfl⟩) chain chain 1 2 chainCache

theorem chain_value : IncrementalControl.value chain 1 chainCache 0 = 1 := by decide

theorem changed_chain_value : IncrementalControl.value chain 2 changedChain 0 = 2 := by decide

theorem dependency_cone_cells : changedChain.val.work = 9 ∧ changedChain.val.cells = 16 := by decide

theorem unchanged_chain_zero_work :
    (IncrementalControl.update (List.finRange 4)
      (fun a => List.mem_ofFn.mpr ⟨a, rfl⟩) chain chain 1 1 chainCache).val.work = 0 := by decide

def vectorModel : OptimalController.Model Nat Unit (Fin 2) (Fin 2) where
  actions := fun _ => [0,1]
  actionsNonempty := by intro s; simp
  outcomes := fun _ _ => [0,1]
  outcomesNonempty := by intro s a ha; simp
  next := fun _ _ _ => ()
  cost := fun i _ a o => if a.val = 0 then (if i = o.val then 8 else 0) else 5
  terminal := fun _ _ => 0

def scalarModel : OptimalController.Model Unit Unit (Fin 2) (Fin 2) where
  actions := vectorModel.actions
  actionsNonempty := vectorModel.actionsNonempty
  outcomes := vectorModel.outcomes
  outcomesNonempty := vectorModel.outcomesNonempty
  next := vectorModel.next
  cost := fun _ s a o => vectorModel.cost 0 s a o + vectorModel.cost 1 s a o
  terminal := fun _ _ => 0

theorem scalar_worst_prefers_zero :
    OptimalController.selectAction scalarModel () (OptimalController.value scalarModel () 0) () = 0 ∧
      OptimalController.value scalarModel () 1 () = 8 := by decide

theorem vector_worst_prefers_one :
    (ParametricPareto.frontier (ParetoPolicy.state vectorModel 2 1 ())).map (·.id) = [1] := by decide

theorem all_adaptive_tree_count :
    (ParetoPolicy.policies 2 2 3).length = 128 := by decide

end ReasoningControls
