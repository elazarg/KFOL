module

public import KFOL.Definitions.Rounds

/-! # Hidden commitments at every public history

These are operational/information gates. No equilibrium correspondence or
Bayes-consistency conclusion is claimed here.
-/

@[expose] public section

namespace KFOL.Rounds

open GameTheory.Languages GameTheory.Protocol
open Bridges.FOSGToEFG

universe u

/-- Earlier commitments are hidden at every public history, including histories
having probability zero under a proposed strategy. No reach-probability
hypothesis occurs in this exact canonical information-state equality. -/
theorem hidden_prefix {Role : Type u} [DecidableEq Role] (horizon : ℕ)
    (order : ExplicitOrder Role)
    (history : (observed Role horizon).execution.History) (count : ℕ)
    (first second : Prefix (observed Role horizon) order history count) (i : Role) :
    viewOfState (observed Role horizon) order i (.stage history count first) =
      viewOfState (observed Role horizon) order i (.stage history count second) := by
  classical
  simp only [viewOfState, phaseOfState, scheduledPlayer, State.history]

/-- On actual canonical histories the accepted information model has exactly
that view. This connects the hidden-prefix statement to policies, rather than
only to a projected execution record. -/
theorem serial_information {Role : Type u} [DecidableEq Role] (horizon : ℕ)
    (order : ExplicitOrder Role) (i : Role)
    {state : State (observed Role horizon) order}
    (trace : (serial horizon order).execution.Trace state) :
    (serial horizon order).information.infoOf i trace =
      viewOfState (observed Role horizon) order i state :=
  infoOf_eq_viewOfState (observed Role horizon) order i trace

/-- Simultaneous bits are legal at every pre-boundary source history. -/
theorem public_joint_legal {Role : Type u} (horizon : ℕ)
    (history : (observed Role horizon).execution.History) (actions : Role → Bool)
    (before : history.state.length < horizon) :
    (observed Role horizon).execution.Legal history.state (fun i => some (actions i)) := by
  refine ⟨Nat.not_le_of_gt before, fun i => ?_⟩
  exact ⟨before, Set.mem_univ _⟩

/-- The resolver publishes exactly the complete chosen tuple, with no chance
or extra private payload. -/
theorem public_step {Role : Type u} (horizon : ℕ)
    (history : (observed Role horizon).execution.History) (actions : Role → Bool)
    (before : history.state.length < horizon) :
    (observed Role horizon).execution.step history.state
      ⟨(fun i => some (actions i)), public_joint_legal horizon history actions before⟩ =
    PMF.pure ((bitDisclosure Role horizon).appendRound history.state actions
      (some actions, fun _ => ())) := by
  rw [(bitDisclosure Role horizon).execution_step_some]
  simp only [MultiRound.MonitoringGame.nextLaw, bitDisclosure, PMF.pure_map]

/-- A reached public continuation, independent of any proposed strategy or
positive-probability assumption about that strategy. -/
noncomputable def appendPublicHistory {Role : Type u} (horizon : ℕ)
    (history : (observed Role horizon).execution.History) (actions : Role → Bool)
    (before : history.state.length < horizon) :
    (observed Role horizon).execution.History :=
  history.extend (target := (bitDisclosure Role horizon).appendRound history.state actions
    (some actions, fun _ => ()))
    (public_joint_legal horizon history actions before) (by
    rw [public_step horizon history actions before]
    simp)

@[simp] theorem appendPublicHistory_length {Role : Type u} (horizon : ℕ)
    (history : (observed Role horizon).execution.History) (actions : Role → Bool)
    (before : history.state.length < horizon) :
    (appendPublicHistory horizon history actions before).state.length = history.state.length + 1 := by
  unfold appendPublicHistory
  exact (bitDisclosure Role horizon).length_appendRound _ _ _

end KFOL.Rounds
