module

public import KFOL.Rounds.PrefixLaw

/-! # Earlier commitments are unchanged by the scheduled player's deviation -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.SerialRun

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u

variable {Role : Type u} [DecidableEq Role]

theorem currentLaw_update_of_ne (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (who : Role) (alternative : (game.serialized order).information.BehavioralPolicy who)
    (h : game.execution.History) (earlier : Role) (hne : earlier ≠ who) :
    Serialization.currentLaw game.toFOSG order (Profile.update profile who alternative) h earlier =
      Serialization.currentLaw game.toFOSG order profile h earlier := by
  unfold Serialization.currentLaw
  rw [Profile.update_of_ne profile alternative hne]

/-- Replacing a whole policy cannot affect commitments made before that
player's slot. This is exact PMF equality, with no reach-probability premise. -/
theorem prefixLaw_update_before (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (who : Role) (alternative : (game.serialized order).information.BehavioralPolicy who)
    (h : game.execution.History) (n : Nat) (hn : n ≤ (order.player.symm who).val) :
    Serialization.prefixLaw game.toFOSG order (Profile.update profile who alternative) h n
        (Nat.le_trans hn (Nat.le_of_lt (order.player.symm who).isLt)) =
      Serialization.prefixLaw game.toFOSG order profile h n
        (Nat.le_trans hn (Nat.le_of_lt (order.player.symm who).isLt)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnprev : n ≤ (order.player.symm who).val := by omega
    have hslot : n < order.slots := by have := (order.player.symm who).isLt; omega
    have hne : order.player ⟨n,hslot⟩ ≠ who := by
      intro he
      have hi := congrArg (fun r => (order.player.symm r).val) he
      simp only [Equiv.symm_apply_apply] at hi
      omega
    simp only [Serialization.prefixLaw]
    rw [ih hnprev,currentLaw_update_of_ne game order profile who alternative h _ hne]

end KFOL.Rounds.Game.SerialRun
