module

import KFOL.Rounds.SequentialExistence
import KFOL.Rounds.InformationFibers
import KFOL.Rounds.Values
import KFOL.Rounds.ProductBeliefs
import KFOL.Rounds.TerminalErasure
import Mathlib.Logic.Equiv.Bool

namespace KFOLTest.RoundTrees
open KFOL.Rounds GameTheory.Protocol
open GameTheory.Languages.Bridges.FOSGToEFG

/-- The first round has two actions for false and one for true; the next has
one for false and three for true. Equal continuation trees are separate copies. -/
private def second : Game Bool := .round (fun i => if i then 2 else 0) (fun _ => .leaf false)
private def changing : Game Bool := .round (fun i => if i then 0 else 1) (fun _ => second)
private def firstTuple (x : Fin 2) (i : Bool) : Fin ((if i then 0 else 1) + 1) :=
  match i with | false => x | true => 0
private def afterFirst (x : Fin 2) : Game.Position changing := .down (firstTuple x) .root
private def order : ExplicitOrder Bool := ⟨2,finTwoEquiv⟩

example : (afterFirst 0).current = second := rfl
example : changing.execution.available (afterFirst 0) true = Set.Iic 2 := rfl
example : ¬ 1 ∈ changing.execution.available (afterFirst 0) false := by decide
example : afterFirst 0 ≠ afterFirst 1 := by
  intro he
  have hh := congrArg (fun p => p.path.map (fun a => a false)) he
  simp only [afterFirst,firstTuple,Game.Position.path,List.map_cons,List.map_nil] at hh
  cases hh

example : Finite changing.execution.History := inferInstance
example : Finite (changing.serialized order).execution.History := inferInstance
example : changing.information.PerfectRecall := changing.perfect_recall
example : (changing.serialized order).information.DecisionRecall := changing.serial_decision_recall order
example : changing.execution.Reachable (afterFirst 1) := changing.reachable_position _

example (payoff : Bool → (changing.serialized order).execution.History → ℝ) :
    ∃ assessment : (changing.serialized order).information.BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (changing.serial_decision_recall order).decisionInformationAntichain
        (changing.serial_well_founded_histories order) payoff :=
  changing.serial_exists_sequential_equilibrium order payoff

example (h : changing.execution.History) (ht : ¬ changing.execution.terminal h.state) (i : Bool) :
    Nonempty ((changing.serialized order).information.InformationHistory i
      (scheduledView changing.toFOSG i (changing.information.infoOf i h.trace)) ≃
        Prefix changing.toFOSG order h (order.player.symm i).val) :=
  ⟨changing.informationHistoryEquivPrefix order h ht i⟩

example : (Game.leaf false).sequentialValues order = {PMF.pure false} :=
  Game.sequentialValues_leaf false order

end KFOLTest.RoundTrees

#print axioms KFOL.Rounds.Serialization.decisionRecall_of_perfectRecall
#print axioms KFOL.Rounds.Game.serial_exists_sequential_equilibrium
#print axioms KFOL.Rounds.Game.informationHistoryEquivPrefix

#print axioms KFOL.Rounds.Game.consistent_belief_eq_product
#print axioms KFOL.Rounds.Game.exists_consistent_product_assessment
#print axioms KFOL.Rounds.Game.erase_terminal_continuation
