module

public import KFOL.Rounds.SerialRun.Choice

/-! # The actual canonical hidden-slot transition has the scheduled local law -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.SerialRun

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u

variable {Role : Type u} [DecidableEq Role] [Finite Role]

/-- Forgetting the history after one canonical behavioral step is exactly
sampling its canonical joint and following the actual execution transition. -/
theorem run_one_map_state (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : (game.serialized order).execution.History)
    (ht : ¬(game.serialized order).execution.terminal h.state) :
    ((game.serialized order).information.runBehavioralFrom profile 1 h).map ExecutionProtocol.History.state =
      ((game.serialized order).information.behavioralJoint profile h.trace ht).bind
        ((game.serialized order).execution.step h.state) := by
  rw [(game.serialized order).information.runBehavioralFrom_succ_of_not_terminal profile 0 ht,PMF.map_bind]
  apply bind_congr_on_support
  intro joint _
  rw [map_bindOnSupport]
  calc
    _ = ((game.serialized order).execution.step h.state joint).bind PMF.pure := by
      apply bindOnSupport_eq_bind_of_eq_on_support
      intro target realized
      change (PMF.pure (h.extend joint.property realized)).map ExecutionProtocol.History.state = PMF.pure target
      rw [PMF.pure_map]
      rfl
    _ = _ := PMF.bind_pure _

omit [Finite Role] in
set_option backward.isDefEq.respectTransparency false in
/-- Every selected joint advances by exactly its actual scheduled choice. -/
theorem step_selectedJointOfInfoChoice (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    {n : Nat} (p : Prefix game.toFOSG order h n) (hn : n < order.slots)
    (view : (game.serialized order).information.InfoState (order.player ⟨n,hn⟩))
    (he : view = scheduledView game.toFOSG (order.player ⟨n,hn⟩)
      (game.information.infoOf (order.player ⟨n,hn⟩) h.trace))
    (c : (game.serialized order).information.Choice (order.player ⟨n,hn⟩) view) :
    (game.serialized order).execution.step (.stage h n p)
      (selectedJointOfInfoChoice game order h ht p hn view he c) =
      PMF.pure (.stage h (n+1) (p.advance hn
        (choiceAtOfInfoEq game order h (order.player ⟨n,hn⟩) view he c))) := by
  have hc : choiceOfJoint game.toFOSG order p hn
      (selectedJointOfInfoChoice game order h ht p hn view he c).val
      (selectedJointOfInfoChoice game order h ht p hn view he c).property.2 =
      choiceAtOfInfoEq game order h (order.player ⟨n,hn⟩) view he c := by
    apply Subtype.ext
    simp only [choiceOfJoint,selectedJointOfInfoChoice,selectedJoint,scheduledPlayer,
      ExecutionProtocol.singletonJoint,dite_true,choiceAtOfInfoEq_val]
  rw [step_select game.toFOSG order p hn]
  rw [hc]

set_option backward.isDefEq.respectTransparency false in
/-- The exact one-hidden-slot state law, under every whole target profile and
at every legal prefix history. -/
theorem prefix_run_one_map_state (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    {n : Nat} (p : Prefix game.toFOSG order h n) (hn : n < order.slots)
    (trace : (game.serialized order).execution.Trace (.stage h n p)) :
    ((game.serialized order).information.runBehavioralFrom profile 1 ⟨.stage h n p,trace⟩).map
      ExecutionProtocol.History.state =
      (Serialization.currentLaw game.toFOSG order profile h (order.player ⟨n,hn⟩)).map
        (fun c => .stage h (n+1) (p.advance hn c)) := by
  rw [run_one_map_state game order profile ⟨.stage h n p,trace⟩ ht,behavioralJoint_select game order profile h ht p hn trace,PMF.bind_map]
  let view := (game.serialized order).information.infoOf (order.player ⟨n,hn⟩) trace
  have he : view = scheduledView game.toFOSG (order.player ⟨n,hn⟩)
      (game.information.infoOf (order.player ⟨n,hn⟩) h.trace) := game.serial_scheduled_info order h p hn trace
  calc
    _ = (profile (order.player ⟨n,hn⟩) view).bind (fun c => PMF.pure
        (State.stage (G := game.toFOSG) (order := order) h (n+1) (p.advance hn
          (choiceAtOfInfoEq game order h (order.player ⟨n,hn⟩) view he c)))) := by
      apply congrArg ((profile (order.player ⟨n,hn⟩) view).bind)
      funext c
      exact step_selectedJointOfInfoChoice game order h ht p hn view he c
    _ = _ := by
      change (profile (order.player ⟨n,hn⟩) view).map
        (fun c => State.stage (G := game.toFOSG) (order := order) h (n+1) (p.advance hn (choiceAtOfInfoEq game order h
          (order.player ⟨n,hn⟩) view he c))) = _
      rw [← map_choiceAtOfInfoEq game order profile h (order.player ⟨n,hn⟩) view he,PMF.map_comp]
      rfl

end KFOL.Rounds.Game.SerialRun
