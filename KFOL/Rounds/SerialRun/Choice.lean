module

public import KFOL.Rounds.SelectionMass

/-! # Scheduled serial menu laws at actual prefix histories -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.SerialRun

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u

variable {Role : Type u} [DecidableEq Role]

/-- Read an actual target information-local choice at a scheduled source view.
Only its legality proof changes; its option value is preserved literally. -/
def choiceAtOfInfoEq (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (who : Role)
    (view : (game.serialized order).information.InfoState who)
    (he : view = scheduledView game.toFOSG who (game.information.infoOf who h.trace))
    (c : (game.serialized order).information.Choice who view) : ChoiceAt game.toFOSG h who := by
  subst view
  exact (Serialization.choiceAtEquiv game.toFOSG h who)
    ((choiceEquiv game.toFOSG order who (game.information.infoOf who h.trace)) c)

@[simp] theorem choiceAtOfInfoEq_val (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (who : Role)
    (view : (game.serialized order).information.InfoState who)
    (he : view = scheduledView game.toFOSG who (game.information.infoOf who h.trace))
    (c : (game.serialized order).information.Choice who view) :
    (choiceAtOfInfoEq game order h who view he c).val = c.val := by
  subst view
  rfl

/-- Its mapped local PMF is exactly the independent scheduled law used in the
prefix product. -/
theorem map_choiceAtOfInfoEq (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (who : Role)
    (view : (game.serialized order).information.InfoState who)
    (he : view = scheduledView game.toFOSG who (game.information.infoOf who h.trace)) :
    (profile who view).map (choiceAtOfInfoEq game order h who view he) =
      Serialization.currentLaw game.toFOSG order profile h who := by
  subst view
  rfl

/-- Embed one scheduled choice into the only possibly active joint coordinate. -/
def selectedJointOfInfoChoice (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    {n : Nat} (p : Prefix game.toFOSG order h n) (hn : n < order.slots)
    (view : (game.serialized order).information.InfoState (order.player ⟨n,hn⟩))
    (he : view = scheduledView game.toFOSG (order.player ⟨n,hn⟩)
      (game.information.infoOf (order.player ⟨n,hn⟩) h.trace))
    (c : (game.serialized order).information.Choice (order.player ⟨n,hn⟩) view) :
    {joint : (i : Role) → Option ℕ // (game.serialized order).execution.Legal (.stage h n p) joint} :=
  ⟨selectedJoint game.toFOSG (order.player ⟨n,hn⟩) c.val,by
    change (GameTheory.Languages.Bridges.FOSGToEFG.execution game.toFOSG order).Legal (.stage h n p) _
    unfold ExecutionProtocol.Legal
    dsimp only [GameTheory.Languages.Bridges.FOSGToEFG.execution]
    simpa only [choiceAtOfInfoEq_val,scheduledPlayer,State.history] using selectedJoint_legal game.toFOSG order p hn ht
      (choiceAtOfInfoEq game order h (order.player ⟨n,hn⟩) view he c)⟩

/-- The canonical behavioral joint at a hidden slot samples exactly the
scheduled local law, including one-action menus and inactive source roles. -/
theorem behavioralJoint_select [Finite Role] (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    {n : Nat} (p : Prefix game.toFOSG order h n) (hn : n < order.slots)
    (trace : (game.serialized order).execution.Trace (.stage h n p)) :
    (game.serialized order).information.behavioralJoint profile trace ht =
      (profile (order.player ⟨n,hn⟩)
        ((game.serialized order).information.infoOf (order.player ⟨n,hn⟩) trace)).map
        (selectedJointOfInfoChoice game order h ht p hn _
          (game.serial_scheduled_info order h p hn trace)) := by
  rw [(game.serialized order).information.behavioralJoint_eq_map_of_at_most_one_active
    profile trace ht (order.player ⟨n,hn⟩) (by
      intro i hi
      exact hi.2.1)]
  apply congrArg (fun f => (profile (order.player ⟨n,hn⟩)
    ((game.serialized order).information.infoOf (order.player ⟨n,hn⟩) trace)).map f)
  funext c
  apply Subtype.ext
  rfl

end KFOL.Rounds.Game.SerialRun
