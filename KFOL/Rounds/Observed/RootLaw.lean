module

public import KFOL.Rounds.Observed.Transport

/-! # Exact first-round recursion of canonical winner distributions -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory.Protocol GameTheory.Math.Probability

universe u

variable {Role : Type u} [Fintype Role]

/-- A root step is the independent product of the actual finite-menu laws. -/
theorem root_kernel (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : (i : Role) → (Game.round sizes next).information.BehavioralPolicy i) :
    positionKernel (.round sizes next) profile Position.root =
      (independentProduct (fun i => rootLaw sizes next i (profile i))).map
        (fun a => Position.down a Position.root) := by
  classical
  rw [positionKernel]
  rw [dite_eq_right (show ¬(Position.root : Position (.round sizes next)).current.Terminal from id)]
  change (independentProduct (fun i => profile i Position.root)).map _ =
    (independentProduct (fun i => (profile i Position.root).map (rootChoiceEquiv sizes next i))).map _
  rw [← independentProduct_map,PMF.map_comp]
  apply congrArg (fun f => (independentProduct (fun i => profile i Position.root)).map f)
  funext choices
  rfl

/-- The finite-run kernel law can be read with its first transition first. -/
theorem positionRun_succ_head (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i) (fuel : Nat) (p : Position game) :
    positionRun game profile (fuel+1) p =
      (positionKernel game profile p).bind (positionRun game profile fuel) := by
  induction fuel with
  | zero => rw [positionRun_succ,positionRun_zero,PMF.pure_bind]; exact (PMF.bind_pure _).symm
  | succ fuel ih =>
    rw [positionRun_succ,ih,PMF.bind_bind]
    apply congrArg ((positionKernel game profile p).bind)
    funext q
    exact (positionRun_succ game profile fuel q).symm

/-- The canonical observed winner law at a round is the independent product
of its root marginals followed by the actual continuation law in each child.
The equality covers every fuel and every actual joint tuple. -/
theorem runBehavioral_round_winner (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : (i : Role) → (Game.round sizes next).information.BehavioralPolicy i)
    (fuel : Nat) :
    ((Game.round sizes next).information.runBehavioralFrom profile (fuel+1)
      (Game.round sizes next).execution.initHistory).map (Game.round sizes next).winner =
    (independentProduct (fun i => rootLaw sizes next i (profile i))).bind fun a =>
      ((next a).information.runBehavioralFrom
        (fun i => restrictChild sizes next i (profile i) a) fuel
        (next a).execution.initHistory).map (next a).winner := by
  rw [runBehavioral_winner_eq_positionRun]
  change (positionRun (.round sizes next) profile (fuel+1) Position.root).map _ = _
  rw [positionRun_succ_head,root_kernel,PMF.bind_map,PMF.map_bind]
  apply congrArg ((independentProduct (fun i => rootLaw sizes next i (profile i))).bind)
  funext a
  rw [runBehavioral_winner_eq_positionRun]
  change (positionRun (.round sizes next) profile fuel (.down a Position.root)).map _ = _
  rw [← child_positionRun_map,PMF.map_comp]
  rfl

end KFOL.Rounds.Game.Observed
