module

public import KFOL.Rounds.ProductBeliefs
public import KFOL.Rounds.Values
public import GameTheory.Core.Utility

/-! # Sequential rationality compares actual terminal winner coordinates -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Finite Role]

/-- All whole-policy deviations have bounded indicator payoffs. Canonical
sequential rationality therefore compares their actual winner probabilities,
with no integrability premise left to the caller. -/
theorem serial_rationality_iff_winner_coordinates (game : Game Role) (order : ExplicitOrder Role)
    (assessment : (game.serialized order).information.BehavioralAssessment) :
    assessment.IsSequentiallyRational (game.serial_well_founded_histories order)
      (winnerPayoff (game.serialWinner order)) ↔
    ∀ (who : Role) (site : (game.serialized order).information.InformationSite who)
      (alternative : (game.serialized order).information.BehavioralPolicy who),
      ((((assessment.belief who site).bind fun x =>
        (game.serialized order).information.runBehavioralTerminalFrom
          (game.serial_well_founded_histories order)
          (Profile.update (sig := (game.serialized order).information.behavioralSignature)
            assessment.strategy who alternative) x.val).map (game.serialWinner order)) who).toReal ≤
      ((((assessment.belief who site).bind fun x =>
        (game.serialized order).information.runBehavioralTerminalFrom
          (game.serial_well_founded_histories order) assessment.strategy x.val).map
            (game.serialWinner order)) who).toReal := by
  change (∀ who site,
    (assessment.continuationContext (game.serial_well_founded_histories order) site
      (winnerPayoff (game.serialWinner order) who)).IsLocallyOptimal Set.univ (assessment.strategy who)) ↔ _
  apply forall_congr'
  intro who
  apply forall_congr'
  intro site
  have hi (alternative : (game.serialized order).information.BehavioralPolicy who) :=
    assessment.continuationContext_integrable_of_bounded_terminal
      (game.serial_well_founded_histories order) site
      (winnerPayoff (game.serialWinner order) who) 1
      (fun x _ => winnerPayoff_abs_le_one _ who x) alternative
  rw [Context.isLocallyOptimal_iff_of_integrable (hi _) (fun alternative _ => hi alternative)]
  simp only [Set.mem_univ,forall_const,InformationModel.BehavioralAssessment.continuationContext_value,
    expect_winnerPayoff,Profile.update_eq_self]

/-- It suffices to check exactly the canonical site for each role at every
nonterminal public source history; these cover all actual serial decisions. -/
theorem serial_rationality_iff_public_coordinates (game : Game Role) (order : ExplicitOrder Role)
    (assessment : (game.serialized order).information.BehavioralAssessment) :
    assessment.IsSequentiallyRational (game.serial_well_founded_histories order)
      (winnerPayoff (game.serialWinner order)) ↔
    ∀ (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
      (who : Role) (alternative : (game.serialized order).information.BehavioralPolicy who),
      ((((assessment.belief who (game.serialSite order h ht who)).bind fun x =>
        (game.serialized order).information.runBehavioralTerminalFrom
          (game.serial_well_founded_histories order)
          (Profile.update (sig := (game.serialized order).information.behavioralSignature)
            assessment.strategy who alternative) x.val).map (game.serialWinner order)) who).toReal ≤
      ((((assessment.belief who (game.serialSite order h ht who)).bind fun x =>
        (game.serialized order).information.runBehavioralTerminalFrom
          (game.serial_well_founded_histories order) assessment.strategy x.val).map
            (game.serialWinner order)) who).toReal := by
  rw [serial_rationality_iff_winner_coordinates]
  constructor
  · intro h hroot hterm who alternative
    exact h who (game.serialSite order hroot hterm who) alternative
  · intro h who site alternative
    obtain ⟨hroot,hterm,rfl⟩ := game.serialSite_surjective order who site
    exact h hroot hterm who alternative

end KFOL.Rounds.Game
