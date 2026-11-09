module

import KFOL.Rounds.SerialRun.Terminal

namespace KFOL.ObservedSerialRunRegression

open Rounds Rounds.Game Rounds.Game.SerialRun GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u

/-- Complete finite-prefix law on actual serialized canonical histories. -/
theorem actual_prefix {Role : Type u} [Fintype Role] [DecidableEq Role]
    (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    (n : Nat) (hn : n ≤ order.slots) :
    (game.serialized order).information.runBehavioralFrom profile n (boundaryHistory game order h) =
      (Serialization.prefixLaw game.toFOSG order profile h n hn).map
        (Serialization.historyAtPrefix game.toFOSG order h ht n) :=
  run_prefix game order profile h ht n hn

/-- Complete product-belief/whole-policy-deviation terminal bridge. -/
theorem actual_terminal_deviation {Role : Type u} [Fintype Role] [DecidableEq Role]
    (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (who : Role) (alternative : (game.serialized order).information.BehavioralPolicy who)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) :
    ((game.productBelief order profile h ht who).bind fun x =>
      (game.serialized order).information.runBehavioralTerminalFrom
        (game.serial_well_founded_histories order) (Profile.update profile who alternative) x.val).map
        (eraseHistory game.toFOSG order) =
      game.information.runBehavioralTerminalFrom game.well_founded_histories
        (projectBehavioral game.toFOSG order (Profile.update profile who alternative)) h :=
  productBelief_terminal_deviation game order profile who alternative h ht

private def oneOrder : ExplicitOrder (Fin 1) := ⟨1,Equiv.refl _⟩

example (game : Game (Fin 1))
    (profile : Profile (game.serialized oneOrder).information.behavioralSignature)
    (alternative : (game.serialized oneOrder).information.BehavioralPolicy 0)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) :
    (game.productBelief oneOrder profile h ht 0).map Subtype.val =
      (game.serialized oneOrder).information.runBehavioralFrom
        (Profile.update profile 0 alternative) 0 (boundaryHistory game oneOrder h) :=
  productBelief_history_eq_run_prefix_update game oneOrder profile 0 alternative h ht

end KFOL.ObservedSerialRunRegression

#print axioms KFOL.Rounds.Game.SerialRun.run_prefix
#print axioms KFOL.Rounds.Game.SerialRun.prefixLaw_update_before
#print axioms KFOL.Rounds.Game.SerialRun.productBelief_terminal_deviation
#print axioms KFOL.Rounds.Game.SerialRun.productBelief_terminal_winner_deviation
