module

public import KFOL.Rounds.SerializationFinite
public import KFOL.Rounds.SerializationRecall
public import GameTheory.Analysis.Protocol.SequentialExistence

/-! # Canonical sequential-equilibrium foundations for every finite round tree -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u}

/-- Public prefixes remember all play; hidden current commitments are forgotten
only while the corresponding player is inactive. -/
theorem serial_decision_recall [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) : (game.serialized order).information.DecisionRecall :=
  Serialization.decisionRecall_of_perfectRecall game.toFOSG order game.perfect_recall

private def fallback (game : Game Role) (i : Role) : game.information.Policy i := by
  classical
  intro p
  by_cases ht : p.current.Terminal
  · exact ⟨none,by exact fun hn => hn ht⟩
  · exact ⟨some 0,ht,Nat.zero_le _⟩

private def serialFallback [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) (i : Role) : (game.serialized order).information.Policy i := by
  classical
  intro view
  cases hphase : view.phase with
  | resolve => exact ⟨none,by simp [menu,hphase]⟩
  | select owner =>
    by_cases hi : i = owner
    · exact ⟨(game.fallback i view.source).val,by
        simpa only [menu,hphase,hi,ite_true] using (game.fallback i view.source).property⟩
    · exact ⟨none,by simp [menu,hphase,hi]⟩

/-- The existing independent finite SE theorem applies to the actual serial
implementation, for arbitrary terminal utilities and all off-path decisions. -/
theorem serial_exists_sequential_equilibrium [Fintype Role] [DecidableEq Role]
    (game : Game Role) (order : ExplicitOrder Role)
    (payoff : Role → (game.serialized order).execution.History → ℝ) :
    ∃ assessment : (game.serialized order).information.BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (game.serial_decision_recall order).decisionInformationAntichain
        (game.serial_well_founded_histories order) payoff := by
  exact (game.serialized order).information.exists_sequentialEquilibrium
    (game.serial_decision_recall order) (game.serialFallback order) payoff
    (game.serial_well_founded_histories order)

end KFOL.Rounds.Game
