module

public import KFOL.Rounds.Observed.History
public import GameTheory.Protocol.StateKernel

/-! # The canonical observed runner has an exact public-position kernel -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory.Protocol GameTheory.Math.Probability

universe u

variable {Role : Type u}

/-- One pure tuple of actual information-local choices extends its current
public position by the same actual option values. -/
def successor (game : Game Role) (p : Position game) (running : ¬ p.current.Terminal)
    (choices : (i : Role) → game.information.Choice i p) : Position game :=
  p.append (fun i => (choices i).val.getD 0) (by
    intro i
    have h := (choices i).property
    change LegalOption game.execution p i (choices i).val at h
    cases hc : (choices i).val with
    | none => rw [hc] at h; exact False.elim (h running)
    | some n => rw [hc] at h; exact h.2) running

/-- A state retains the complete information consulted by this profile. The
kernel draws independently from the actual menus, then appends the tuple. -/
def positionKernel [Fintype Role] (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i) (p : Position game) : PMF (Position game) := by
  classical
  exact if stopped : p.current.Terminal then PMF.pure p
    else (independentProduct (fun i => profile i p)).map (successor game p stopped)

/-- The one-step kernel is exactly the actual canonical behavioral chooser
and execution step at every legal complete history, including off-path ones. -/
theorem chooser_step_eq_kernel [Fintype Role] (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i)
    (h : game.execution.History) (running : ¬ game.execution.terminal h.state) :
    ((game.information.randomizedChooser profile) h running).bind (game.execution.step h.state) =
      positionKernel game profile h.state := by
  classical
  change (game.information.behavioralJoint profile h.trace running).bind _ = _
  rw [game.information.behavioralJoint_eq_independentProduct,PMF.bind_map]
  rcases h with ⟨p,trace⟩
  cases trace
  all_goals simp only [positionKernel,dite_eq_right running]
  all_goals rfl

/-- Position laws are iterations of the proved one-step kernel. No new
strategy or equilibrium semantics is introduced. -/
def positionRun [Fintype Role] (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i)
    (fuel : Nat) (p : Position game) : PMF (Position game) :=
  (fun law => law.bind (positionKernel game profile))^[fuel] (PMF.pure p)

/-- The position kernel is connected to the canonical history runner, rather
than serving as an independent unproved evaluator. -/
theorem runBehavioral_map_state [Fintype Role] (game : Game Role)
    (profile : (i : Role) → game.information.BehavioralPolicy i)
    (fuel : Nat) (h : game.execution.History) :
    (game.information.runBehavioralFrom profile fuel h).map ExecutionProtocol.History.state =
      positionRun game profile fuel h.state := by
  classical
  apply game.execution.runRandomizedFor_map_state
    (game.information.randomizedChooser profile) (positionKernel game profile)
  · intro p stopped
    simp only [positionKernel,dite_eq_left stopped]
  · exact chooser_step_eq_kernel game profile

end KFOL.Rounds.Game.Observed
