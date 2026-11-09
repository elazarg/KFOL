module

public import KFOL.Rounds.SelectionMass

/-! # Exact public-reach factor in hidden commitment histories -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Finite Role]

set_option backward.isDefEq.respectTransparency false in
/-- Canonical reach probability factors into the public-boundary weight and
the ordered independent law of the earlier current commitments. This equality
also holds when the public weight is zero. -/
theorem prefix_reach_factor (game : Game Role) (order : ExplicitOrder Role)
    (policies : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) :
    ∀ (n : ℕ) (hn : n ≤ order.slots) (p : Prefix game.toFOSG order h n),
    ((game.serialized order).information.historyReachWeight policies
      (Serialization.historyAtPrefix game.toFOSG order h ht n p)).toReal =
    ((game.serialized order).information.historyReachWeight policies
      (Serialization.historyAtPrefix game.toFOSG order h ht 0 (Prefix.initial (G := game.toFOSG) (order := order) h))).toReal *
      (Serialization.prefixLaw game.toFOSG order policies h n hn p).toReal := by
  intro n
  induction n with
  | zero =>
    intro hn p
    have he := Serialization.prefix_zero game.toFOSG order h p
    subst p
    simp only [Serialization.prefixLaw,PMF.pure_apply_self,ENNReal.toReal_one,mul_one]
  | succ n ih =>
    intro hn p
    have hc : n < order.slots := Nat.lt_of_succ_le hn
    let prior := Serialization.prefixTrace game.toFOSG order
      (Serialization.boundaryTrace game.toFOSG order h.trace) ht n p.retreat
    let c := Serialization.lastChoice game.toFOSG order p
    have hs := game.serial_selection_step_probability order policies h ht p.retreat hc prior c
    have he : State.stage (G := game.toFOSG) (order := order) h (n+1) p =
        State.stage h (n+1) (p.retreat.advance hc c) :=
      congrArg (fun q : Prefix game.toFOSG order h (n+1) =>
        State.stage (G := game.toFOSG) (order := order) h (n+1) q)
          (Serialization.advance_retreat game.toFOSG order p hc).symm
    rw [← he] at hs
    simp only [Serialization.historyAtPrefix,Serialization.prefixTrace]
    rw [InformationModel.historyReachProbability_extend]
    rw [hs]
    change ((game.serialized order).information.historyReachWeight policies
      (Serialization.historyAtPrefix game.toFOSG order h ht n p.retreat)).toReal * _ = _
    rw [ih (Nat.le_of_lt hc),Serialization.prefixLaw_succ_apply,ENNReal.toReal_mul]
    dsimp only [c,Serialization.historyAtPrefix,Serialization.prefixTrace]
    ring

end KFOL.Rounds.Game
