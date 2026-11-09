module

public import KFOL.Rounds.Observed.Children
public import KFOL.Rounds.Observed.RootLaw

/-! # A canonical observed SPE induces a canonical mixed Nash root stage -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe u

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

/-- Root-only deviations lift to full policies while keeping every off-path
child policy fixed. Canonical whole-policy SPE therefore implies canonical
mixed Nash of the actual finite stage with those continuation winner laws. -/
theorem subgamePerfect_root_nash (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    {bound : Nat} (bounded : (Game.round sizes next).execution.BoundedHorizon bound)
    (profile : Profile (Game.round sizes next).information.behavioralSignature)
    (perfect : (Game.round sizes next).information.IsBehavioralSubgamePerfect bounded profile
      (fun h i => winnerPayoff (Game.round sizes next).winner i h)) :
    IsNash (stageForm sizes (fun a =>
      ((next a).information.runBehavioralFrom (childProfile sizes next profile a)
        (bound-1) (next a).execution.initHistory).map (next a).winner)).mixed
      (euPreference (fun winner i => winnerPayoff id i winner))
      (rootProfile sizes next profile) := by
  classical
  apply (stage_nash_iff sizes _ (rootProfile sizes next profile)).mpr
  intro who alternative
  let parentAlternative := assemblePolicy sizes next who alternative
    (fun a => restrictChild sizes next who (profile who) a)
  have childAgree (a : (i : Role) → Fin (sizes i + 1)) :
      childProfile sizes next (Profile.update profile who parentAlternative) a =
        childProfile sizes next profile a := by
    rw [childProfile_update]
    dsimp only [parentAlternative]
    rw [restrictChild_assemblePolicy]
    exact Profile.update_eq_self _ _
  have rootChanged : rootProfile sizes next (Profile.update profile who parentAlternative) =
      Profile.update (sig := { Strategy := fun i => PMF (Fin (sizes i + 1)), Outcome := Role })
        (rootProfile sizes next profile) who alternative := by
    rw [rootProfile_update]
    dsimp only [parentAlternative]
    rw [rootLaw_assemblePolicy]
  have optimal := (subgamePerfect_iff_winner_coordinates (.round sizes next) bounded profile).mp perfect
    (Game.round sizes next).execution.initHistory who parentAlternative
  have positive := round_bound_positive sizes next bounded
  have hb : bound = (bound-1)+1 := by omega
  rw [hb,runBehavioral_round_winner,runBehavioral_round_winner] at optimal
  change
    (((independentProduct (rootProfile sizes next (Profile.update profile who parentAlternative))).bind
      (fun a => ((next a).information.runBehavioralFrom
        (childProfile sizes next (Profile.update profile who parentAlternative) a)
        (bound-1) (next a).execution.initHistory).map (next a).winner)) who).toReal ≤
    (((independentProduct (rootProfile sizes next profile)).bind
      (fun a => ((next a).information.runBehavioralFrom (childProfile sizes next profile a)
        (bound-1) (next a).execution.initHistory).map (next a).winner)) who).toReal at optimal
  simp only [childAgree,rootChanged] at optimal
  exact optimal

/-- Every actual observed SPE value satisfies the selected-continuation
mixed-stage equation, with one equilibrium witness in every off-path child. -/
theorem observedValues_round_subset (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) :
    (Game.round sizes next).observedValues ⊆ roundOperator sizes (fun a => (next a).observedValues) := by
  intro value hvalue
  obtain ⟨bound,bounded,profile,perfect,hvalue⟩ := hvalue
  let p := fun a => ((next a).information.runBehavioralFrom
    (childProfile sizes next profile a) (bound-1) (next a).execution.initHistory).map (next a).winner
  refine ⟨p,?_,rootProfile sizes next profile,subgamePerfect_root_nash sizes next bounded profile perfect,?_⟩
  · intro a
    exact ⟨bound-1,child_bounded_horizon sizes next bounded a,childProfile sizes next profile a,
      subgamePerfect_child sizes next bounded profile perfect a,rfl⟩
  · have positive := round_bound_positive sizes next bounded
    have hb : bound = (bound-1)+1 := by omega
    rw [hvalue,hb,runBehavioral_round_winner]
    rfl

end KFOL.Rounds.Game.Observed
