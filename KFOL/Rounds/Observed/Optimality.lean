module

public import KFOL.Rounds.Observed.History
public import KFOL.Rounds.Values
public import GameTheory.Core.Utility

/-! # Canonical Nash and SPE compare actual winner-law coordinates -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe u v

variable {Role : Type u} [DecidableEq Role]

/-- Bounded indicator utilities make canonical stochastic Nash exactly the
coordinate inequalities of the actual winner law. No integrability premise
is left for the caller. -/
theorem isNash_iff_winner_coordinates (F : GameForm.{u,v,u} Role)
    (label : F.sig.Outcome → Role) (profile : Profile F.sig) :
    IsNash F (euPreference (fun out i => winnerPayoff label i out)) profile ↔
      ∀ who alternative,
        (((F.play (Profile.update profile who alternative)).map label) who).toReal ≤
          (((F.play profile).map label) who).toReal := by
  have hi : F.HasIntegrableDeviations (fun out i => winnerPayoff label i out) profile :=
    fun who alternative => payoffIntegrable_of_bounded _ _ (winnerPayoff_abs_le_one label who)
  rw [hi.isNash_iff]
  simp only [expectedUtility,expect_winnerPayoff]

/-- In a finite stage, canonical mixed Nash is exactly the winner-mass
comparison for every replacement law on the actual action menu. -/
theorem stage_nash_iff [Fintype Role] (sizes : Role → ℕ)
    (p : ((i : Role) → Fin (sizes i + 1)) → PMF Role)
    (profile : (i : Role) → PMF (Fin (sizes i + 1))) :
    IsNash (stageForm sizes p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile ↔
    ∀ who alternative,
      (((independentProduct (Profile.update
        (sig := { Strategy := fun i => PMF (Fin (sizes i+1)), Outcome := Role })
        profile who alternative)).bind p) who).toReal ≤
      (((independentProduct profile).bind p) who).toReal := by
  have h := isNash_iff_winner_coordinates (stageForm sizes p).mixed (id : Role → Role) profile
  simpa only [stageForm,GameForm.mixed_play,PMF.map_id] using h

/-- Since every actual public prefix is a proper subgame, canonical observed
SPE is exactly resistance to every whole-policy deviation at every actual
history, measured by its canonical winner-law coordinate. -/
theorem subgamePerfect_iff_winner_coordinates [Fintype Role] (game : Game Role)
    {bound : Nat} (bounded : game.execution.BoundedHorizon bound)
    (profile : (i : Role) → game.information.BehavioralPolicy i) :
    game.information.IsBehavioralSubgamePerfect bounded profile
      (fun h i => winnerPayoff game.winner i h) ↔
    ∀ h : game.execution.History, ∀ who alternative,
      (((game.information.runBehavioralFrom (Profile.update (sig := game.information.behavioralSignature) profile who alternative) bound h).map game.winner) who).toReal ≤
        (((game.information.runBehavioralFrom profile bound h).map game.winner) who).toReal := by
  change (∀ h, game.information.IsSubgameRoot h →
    IsNash (game.information.toBehavioralContinuationGameForm bound h)
      (euPreference (fun h i => winnerPayoff game.winner i h)) profile) ↔ _
  constructor
  · intro h hroot
    exact (isNash_iff_winner_coordinates (game.information.toBehavioralContinuationGameForm bound hroot) game.winner profile).mp
      (h hroot (game.every_history_subgame_root hroot))
  · intro h hroot _
    exact (isNash_iff_winner_coordinates (game.information.toBehavioralContinuationGameForm bound hroot) game.winner profile).mpr (h hroot)

end KFOL.Rounds.Game.Observed
