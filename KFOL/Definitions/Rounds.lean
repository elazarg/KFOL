module

public import GameTheory.Languages.MultiRound.Monitoring
public import GameTheory.Languages.Bridges.FOSGToEFG

/-! # Completely revealed Boolean commitment rounds

This initial protocol boundary supplies the serial two-bit/two-round gate.
It defines operational and information semantics, not an equilibrium recursion.
The general finite-menu tree and its strategic correspondence remain separate.
-/

@[expose] public section

noncomputable section

namespace KFOL.Rounds

open GameTheory.Languages

universe u

/-- Every role commits a bit in each round; the complete tuple is published
at the boundary. Private signals carry no additional information. -/
abbrev bitDisclosure (Role : Type u) (horizon : ℕ) : MultiRound.MonitoringGame Role where
  Action _ := Bool
  PublicSignal := Option (Role → Bool)
  PrivateSignal _ := Unit
  horizon := horizon
  initialPublic := none
  initialPrivate _ := ()
  signalLaw _ actions := PMF.pure (some actions, fun _ => ())

/-- The observed simultaneous-round source uses the library's canonical
execution and perfect-recall information model. -/
abbrev observed (Role : Type u) (horizon : ℕ) : FOSG.Game Role :=
  (bitDisclosure Role horizon).toFOSG

/-- Hidden sequential commitments, followed by one complete revelation step.
The operational schedule is explicit and introduces no action information. -/
abbrev serial {Role : Type u} [DecidableEq Role] (horizon : ℕ)
    (order : Bridges.FOSGToEFG.ExplicitOrder Role) : EFG.Game Role :=
  Bridges.FOSGToEFG.toEFG (observed Role horizon) order

end KFOL.Rounds
