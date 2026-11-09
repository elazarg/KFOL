module

public import KFOL.Rounds.Observed.Optimality
public import KFOL.Rounds.TerminalErasure
public import GameTheory.Languages.Bridges.FOSGToEFGStrategic

/-! # Whole-policy deviations and terminal observed continuation optimality -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

omit [Fintype Role] in
/-- Every complete source unilateral replacement is the projection of a
complete serial unilateral replacement of the same player. -/
theorem lift_source_deviation (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (who : Role) (alternative : game.information.BehavioralPolicy who) :
    ∃ replacement : (game.serialized order).information.BehavioralPolicy who,
      projectBehavioral game.toFOSG order
        (Profile.update (sig := (game.serialized order).information.behavioralSignature)
          profile who replacement) =
      Profile.update (sig := game.information.behavioralSignature)
        (projectBehavioral game.toFOSG order profile) who alternative := by
  refine ⟨translateBehavioral game.toFOSG order
    (Profile.update (sig := game.information.behavioralSignature)
      (projectBehavioral game.toFOSG order profile) who alternative) who,?_⟩
  rw [← translateBehavioral_project_update game.toFOSG order profile who alternative,
    project_translate_profile]

/-- Certified finite and complete terminal continuations give the same
canonical public SPE comparisons at every legal history. -/
theorem subgamePerfect_iff_terminal_coordinates (game : Game Role)
    {bound : ℕ} (bounded : game.execution.BoundedHorizon bound)
    (profile : (i : Role) → game.information.BehavioralPolicy i) :
    game.information.IsBehavioralSubgamePerfect bounded profile
      (fun h i => winnerPayoff game.winner i h) ↔
    ∀ (h : game.execution.History) (who : Role)
      (alternative : game.information.BehavioralPolicy who),
      (((game.information.runBehavioralTerminalFrom game.well_founded_histories
        (Profile.update (sig := game.information.behavioralSignature) profile who alternative) h).map
          game.winner) who).toReal ≤
      (((game.information.runBehavioralTerminalFrom game.well_founded_histories profile h).map
        game.winner) who).toReal := by
  simpa only [game.information.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      game.well_founded_histories bounded] using
    Observed.subgamePerfect_iff_winner_coordinates game bounded profile

/-- Terminal public histories impose an automatic, strategy-independent
comparison; genuine serial sites cover every other history. -/
theorem terminal_comparison (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i)
    (h : game.execution.History) (ht : game.execution.terminal h.state)
    (who : Role) (alternative : game.information.BehavioralPolicy who) :
    (((game.information.runBehavioralTerminalFrom game.well_founded_histories
      (Profile.update (sig := game.information.behavioralSignature) profile who alternative) h).map
        game.winner) who).toReal ≤
    (((game.information.runBehavioralTerminalFrom game.well_founded_histories profile h).map
      game.winner) who).toReal := by
  have he (strategy : (i : Role) → game.information.BehavioralPolicy i) :
      game.information.runBehavioralTerminalFrom game.well_founded_histories strategy h = PMF.pure h :=
    game.execution.randomizedBackwardLaw_of_terminal ht
  rw [he,he]

end KFOL.Rounds.Game
