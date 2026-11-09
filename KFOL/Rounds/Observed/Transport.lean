module

public import KFOL.Rounds.Observed.Kernel

/-! # Exact canonical winner-law transport into every child occurrence -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory.Protocol GameTheory.Math.Probability

universe u

variable {Role : Type u} [Fintype Role]

/-- Restricting to a child occurrence commutes with the complete public-state
kernel, including its independent local randomization. -/
theorem child_kernel_map (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : (i : Role) → (Game.round sizes next).information.BehavioralPolicy i)
    (a : (i : Role) → Fin (sizes i + 1)) (p : Position (next a)) :
    (positionKernel (next a) (fun i => restrictChild sizes next i (profile i) a) p).map
      (Position.down a) = positionKernel (.round sizes next) profile (.down a p) := by
  classical
  by_cases stopped : p.current.Terminal
  · have parentStopped : ((Position.down a p) : Position (.round sizes next)).current.Terminal := by
      simpa only [Position.current] using stopped
    rw [positionKernel,positionKernel,dite_eq_left stopped,dite_eq_left parentStopped,PMF.pure_map]
  · have parentRunning : ¬((Position.down a p) : Position (.round sizes next)).current.Terminal := by
      simpa only [Position.current] using stopped
    rw [positionKernel,positionKernel,dite_eq_right stopped,dite_eq_right parentRunning]
    change (((independentProduct (fun i =>
      (profile i (.down a p)).map (childChoiceEquiv sizes next i a p))).map _).map _) = _
    rw [← independentProduct_map,PMF.map_comp,PMF.map_comp]
    apply congrArg (fun f => (independentProduct (fun i => profile i (.down a p))).map f)
    funext choices
    rfl

@[simp] theorem positionRun_zero (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i) (p : Position game) :
    positionRun game profile 0 p = PMF.pure p := rfl

theorem positionRun_succ (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i) (fuel : Nat) (p : Position game) :
    positionRun game profile (fuel+1) p =
      (positionRun game profile fuel p).bind (positionKernel game profile) := by
  exact Function.iterate_succ_apply' _ _ _

/-- Iterating the actual public-state kernel commutes with each child embedding. -/
theorem child_positionRun_map (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : (i : Role) → (Game.round sizes next).information.BehavioralPolicy i)
    (a : (i : Role) → Fin (sizes i + 1)) (fuel : Nat) (p : Position (next a)) :
    (positionRun (next a) (fun i => restrictChild sizes next i (profile i) a) fuel p).map
      (Position.down a) = positionRun (.round sizes next) profile fuel (.down a p) := by
  induction fuel with
  | zero => simp only [positionRun_zero,PMF.pure_map]
  | succ fuel ih =>
    rw [positionRun_succ,positionRun_succ,PMF.map_bind]
    simp_rw [child_kernel_map]
    calc
      _ = ((positionRun (next a) (fun i => restrictChild sizes next i (profile i) a) fuel p).map (Position.down a)).bind
          (positionKernel (.round sizes next) profile) := (PMF.bind_map _ _ _).symm
      _ = _ := by rw [ih]

/-- The canonical history winner law is the proved position law read at the
actual continuation label. This equality holds for every evaluation fuel. -/
theorem runBehavioral_winner_eq_positionRun (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i)
    (fuel : Nat) (h : game.execution.History) :
    (game.information.runBehavioralFrom profile fuel h).map game.winner =
      (positionRun game profile fuel h.state).map (fun p => p.current.defaultWinner) := by
  rw [← runBehavioral_map_state,PMF.map_comp]
  rfl

/-- Actual canonical winner distributions in a child are precisely the parent
continuation distributions at that occurrence, even for off-path histories. -/
theorem child_run_winner (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (profile : (i : Role) → (Game.round sizes next).information.BehavioralPolicy i)
    (a : (i : Role) → Fin (sizes i + 1)) (fuel : Nat) (h : (next a).execution.History) :
    ((Game.round sizes next).information.runBehavioralFrom profile fuel (historyDown sizes next a h)).map
        (Game.round sizes next).winner =
      ((next a).information.runBehavioralFrom
        (fun i => restrictChild sizes next i (profile i) a) fuel h).map (next a).winner := by
  rw [runBehavioral_winner_eq_positionRun,runBehavioral_winner_eq_positionRun,historyDown_state,
    ← child_positionRun_map,PMF.map_comp]
  rfl

end KFOL.Rounds.Game.Observed
