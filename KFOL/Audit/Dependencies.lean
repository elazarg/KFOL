module

import GameTheory.Languages.EFG.Zermelo
import GameTheory.Analysis.Nash
import GameTheory.Analysis.Minimax
import GameTheory.Analysis.Protocol.EFGExistence
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-! # Selected strategic and analytic dependency gate

Compile the exact canonical interfaces planned for the paper bridges and
check their transitive axiom dependencies. This gate does not assert any
KFOL adequacy or round correspondence theorem.
-/

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``GameTheory.IsNash,
    ``GameTheory.Protocol.InformationModel.IsSubgamePerfect,
    ``GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentialEquilibrium,
    ``GameTheory.Languages.EFG.Game.exists_isSubgamePerfect,
    ``GameTheory.exists_isNash_mixed,
    ``GameTheory.exists_value,
    ``GameTheory.Languages.EFG.Game.exists_isSequentialEquilibrium]
  for declaration in declarations do
    for axiomName in (← collectAxioms declaration) do
      unless allowed.contains axiomName do
        throwError "Dependency audit: {declaration} depends on {axiomName}"
