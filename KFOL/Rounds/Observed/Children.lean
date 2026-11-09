module

public import KFOL.Rounds.Observed.Profiles
public import KFOL.Rounds.Observed.Transport
public import KFOL.Rounds.Observed.Optimality

/-! # Every observed SPE induces SPE in every actual continuation -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol

universe u

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

/-- Every child's whole-policy equilibrium follows by lifting a deviation
only inside that child occurrence. No positive root-reach probability is
assumed; the parent SPE is tested at the actual off-path subgame root. -/
theorem subgamePerfect_child_sameFuel (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    {bound : Nat} (bounded : (Game.round sizes next).execution.BoundedHorizon bound)
    (profile : Profile (Game.round sizes next).information.behavioralSignature)
    (perfect : (Game.round sizes next).information.IsBehavioralSubgamePerfect bounded profile
      (fun h i => winnerPayoff (Game.round sizes next).winner i h))
    (a : (i : Role) → Fin (sizes i + 1))
    (childBound : (next a).execution.BoundedHorizon bound) :
    (next a).information.IsBehavioralSubgamePerfect childBound
      (childProfile sizes next profile a) (fun h i => winnerPayoff (next a).winner i h) := by
  classical
  apply (subgamePerfect_iff_winner_coordinates (next a) childBound _).mpr
  intro h who alternative
  let parentAlternative := assemblePolicy sizes next who (rootLaw sizes next who (profile who))
    (Function.update (restrictChild sizes next who (profile who)) a alternative)
  have ha : restrictChild sizes next who parentAlternative a = alternative := by
    rw [restrictChild_assemblePolicy]
    exact Function.update_self _ _ _
  have hp := (subgamePerfect_iff_winner_coordinates (.round sizes next) bounded profile).mp perfect
    (historyDown sizes next a h) who parentAlternative
  rw [child_run_winner,child_run_winner] at hp
  change
    ((((next a).information.runBehavioralFrom
      (childProfile sizes next (Profile.update profile who parentAlternative) a) bound h).map (next a).winner) who).toReal ≤
    ((((next a).information.runBehavioralFrom (childProfile sizes next profile a) bound h).map (next a).winner) who).toReal at hp
  rw [childProfile_update,ha] at hp
  exact hp

/-- The exact child horizon is one less than the round horizon, and the
canonical SPE predicate is independent of the chosen certified fuel. -/
theorem subgamePerfect_child (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    {bound : Nat} (bounded : (Game.round sizes next).execution.BoundedHorizon bound)
    (profile : Profile (Game.round sizes next).information.behavioralSignature)
    (perfect : (Game.round sizes next).information.IsBehavioralSubgamePerfect bounded profile
      (fun h i => winnerPayoff (Game.round sizes next).winner i h))
    (a : (i : Role) → Fin (sizes i + 1)) :
    (next a).information.IsBehavioralSubgamePerfect (child_bounded_horizon sizes next bounded a)
      (childProfile sizes next profile a) (fun h i => winnerPayoff (next a).winner i h) := by
  have childBound : (next a).execution.BoundedHorizon bound := by
    intro p trace hlo
    exact child_bounded_horizon sizes next bounded a p trace ((Nat.sub_le bound 1).trans hlo)
  exact ((next a).information.isBehavioralSubgamePerfect_bound_iff childBound
    (child_bounded_horizon sizes next bounded a) _ _).mp
      (subgamePerfect_child_sameFuel sizes next bounded profile perfect a childBound)

end KFOL.Rounds.Game.Observed
