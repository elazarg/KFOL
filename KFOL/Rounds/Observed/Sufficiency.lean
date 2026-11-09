module

public import KFOL.Rounds.Observed.StageNecessity
public import KFOL.Rounds.Observed.Bounds

/-! # Child SPE and local mixed Nash defeat every whole-policy deviation -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe u

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

/-- Assemble every independently selected child SPE and a mixed Nash root
stage. Child optimality bounds all future parts of an arbitrary whole-policy
deviation; root Nash then bounds its independently mixed first action. -/
theorem assemble_subgamePerfect (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    {bound : Nat} (bounded : (Game.round sizes next).execution.BoundedHorizon bound)
    (root : (i : Role) → PMF (Fin (sizes i+1)))
    (children : (a : (i : Role) → Fin (sizes i+1)) → Profile (next a).information.behavioralSignature)
    (perfect : ∀ a, (next a).information.IsBehavioralSubgamePerfect
      (child_bounded_horizon sizes next bounded a) (children a)
      (fun h i => winnerPayoff (next a).winner i h))
    (p : ((i : Role) → Fin (sizes i+1)) → PMF Role)
    (values : ∀ a, ((next a).information.runBehavioralFrom (children a) (bound-1)
      (next a).execution.initHistory).map (next a).winner = p a)
    (nash : IsNash (stageForm sizes p).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) root) :
    (Game.round sizes next).information.IsBehavioralSubgamePerfect bounded
      (assembleProfile sizes next root children)
      (fun h i => winnerPayoff (Game.round sizes next).winner i h) := by
  classical
  let profile := assembleProfile sizes next root children
  have hroot : rootProfile sizes next profile = root := rootProfile_assemble sizes next root children
  have hchild (a) : childProfile sizes next profile a = children a := childProfile_assemble sizes next root children a
  have positive := round_bound_positive sizes next bounded
  have hb : bound = (bound-1)+1 := by omega
  have hbase : ((Game.round sizes next).information.runBehavioralFrom profile bound
      (Game.round sizes next).execution.initHistory).map (Game.round sizes next).winner =
      (independentProduct root).bind p := by
    rw [hb,runBehavioral_round_winner]
    change ((independentProduct (rootProfile sizes next profile)).bind fun a =>
      ((next a).information.runBehavioralFrom (childProfile sizes next profile a) (bound-1)
        (next a).execution.initHistory).map (next a).winner) = _
    simp only [hroot,hchild,values]
  apply (subgamePerfect_iff_winner_coordinates (.round sizes next) bounded profile).mpr
  intro history who alternative
  obtain ⟨position,rfl⟩ := (Game.round sizes next).historyEquivPosition.symm.surjective history
  change (((Game.round sizes next).information.runBehavioralFrom
    (Profile.update (sig := (Game.round sizes next).information.behavioralSignature) profile who alternative) bound
    (historyAt (.round sizes next) position)).map (Game.round sizes next).winner who).toReal ≤
    (((Game.round sizes next).information.runBehavioralFrom profile bound
    (historyAt (.round sizes next) position)).map (Game.round sizes next).winner who).toReal
  cases position with
  | root =>
    have hinit : historyAt (.round sizes next) Position.root = (Game.round sizes next).execution.initHistory := by
      apply (Game.round sizes next).historyEquivPosition.injective
      rfl
    rw [hinit,hbase]
    let changed := Profile.update (sig := (Game.round sizes next).information.behavioralSignature) profile who alternative
    let q := fun a => ((next a).information.runBehavioralFrom
      (childProfile sizes next changed a) (bound-1) (next a).execution.initHistory).map (next a).winner
    have hchanged : ((Game.round sizes next).information.runBehavioralFrom changed bound
        (Game.round sizes next).execution.initHistory).map (Game.round sizes next).winner =
        (independentProduct (rootProfile sizes next changed)).bind q := by
      rw [hb,runBehavioral_round_winner]
    have hq (a) : ((q a) who).toReal ≤ ((p a) who).toReal := by
      have hc := (subgamePerfect_iff_winner_coordinates (next a)
        (child_bounded_horizon sizes next bounded a) (children a)).mp (perfect a)
          (next a).execution.initHistory who (restrictChild sizes next who alternative a)
      rw [values a] at hc
      change ((((next a).information.runBehavioralFrom
        (childProfile sizes next (Profile.update profile who alternative) a) (bound-1)
        (next a).execution.initHistory).map (next a).winner) who).toReal ≤ _
      rw [childProfile_update,hchild]
      exact hc
    change (((Game.round sizes next).information.runBehavioralFrom changed bound
      (Game.round sizes next).execution.initHistory).map (Game.round sizes next).winner who).toReal ≤ _
    rw [hchanged]
    calc
      _ ≤ (((independentProduct (rootProfile sizes next changed)).bind p) who).toReal :=
        bind_winner_coordinate_mono _ q p who hq
      _ ≤ (((independentProduct root).bind p) who).toReal := by
        have hr : rootProfile sizes next changed =
            Profile.update (sig := { Strategy := fun i => PMF (Fin (sizes i+1)), Outcome := Role })
              root who (rootLaw sizes next who alternative) := by
          rw [rootProfile_update,hroot]
        rw [hr]
        exact (stage_nash_iff sizes p root).mp nash who (rootLaw sizes next who alternative)
  | down a position =>
    have hh : historyAt (.round sizes next) (.down a position) =
        historyDown sizes next a (historyAt (next a) position) := by
      unfold historyDown
      rw [historyAt_state]
    rw [hh,child_run_winner,child_run_winner]
    change ((((next a).information.runBehavioralFrom
      (childProfile sizes next (Profile.update profile who alternative) a) bound
      (historyAt (next a) position)).map (next a).winner) who).toReal ≤
      ((((next a).information.runBehavioralFrom (childProfile sizes next profile a) bound
      (historyAt (next a) position)).map (next a).winner) who).toReal
    rw [childProfile_update,hchild]
    rw [runBehavioral_eq_of_bound (next a) (child_bounded_horizon sizes next bounded a) _ _ bound (Nat.sub_le _ _),
      runBehavioral_eq_of_bound (next a) (child_bounded_horizon sizes next bounded a) _ _ bound (Nat.sub_le _ _)]
    exact (subgamePerfect_iff_winner_coordinates (next a)
      (child_bounded_horizon sizes next bounded a) (children a)).mp (perfect a)
        (historyAt (next a) position) who (restrictChild sizes next who alternative a)

end KFOL.Rounds.Game.Observed
