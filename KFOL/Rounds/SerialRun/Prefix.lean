module

public import KFOL.Rounds.SerialRun.Step

/-! # The canonical finite serial run is exactly the prefix product law -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.SerialRun

open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u

variable {Role : Type u} [DecidableEq Role] [Finite Role]

omit [Finite Role] in
/-- The stored source history and prefix determine the whole actual serial
history, not only an observation of it. -/
theorem history_state_injective (game : Game Role) (order : ExplicitOrder Role) :
    Function.Injective (fun h : (game.serialized order).execution.History => h.state) := by
  intro h j he
  apply ((game.serialized order).execution.historyEquivReachableState (game.serial_tree_shaped order)).injective
  exact Subtype.ext he

omit [Finite Role] in
/-- Equality of state-projected laws reflects to actual complete-history laws
because the accepted serializer is tree-shaped. -/
theorem law_eq_of_map_state (game : Game Role) (order : ExplicitOrder Role)
    {p q : PMF (game.serialized order).execution.History}
    (he : p.map ExecutionProtocol.History.state = q.map ExecutionProtocol.History.state) : p = q := by
  ext h
  have hh := congrArg (fun law => law h.state) he
  simpa only [pmf_map_apply_of_injective p (history_state_injective game order) h,
    pmf_map_apply_of_injective q (history_state_injective game order) h] using hh

/-- The actual boundary history carrying this literal source trace. -/
def boundaryHistory (game : Game Role) (order : ExplicitOrder Role) (h : game.execution.History) :
    (game.serialized order).execution.History :=
  ⟨.stage h 0 (Prefix.initial (G := game.toFOSG) (order := order) h),
    Serialization.boundaryTrace game.toFOSG order h.trace⟩

/-- After n actual hidden commitments, the canonical complete-history law is
exactly the independent prefix law, for every public source history and every
whole target profile. There is no positive-reach assumption. -/
theorem run_prefix (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    (n : Nat) (hn : n ≤ order.slots) :
    (game.serialized order).information.runBehavioralFrom profile n (boundaryHistory game order h) =
      (Serialization.prefixLaw game.toFOSG order profile h n hn).map
        (Serialization.historyAtPrefix game.toFOSG order h ht n) := by
  induction n with
  | zero =>
    change PMF.pure (boundaryHistory game order h) =
      (PMF.pure (Prefix.initial (G := game.toFOSG) (order := order) h)).map _
    rw [PMF.pure_map]
    apply congrArg PMF.pure
    apply history_state_injective game order
    rfl
  | succ n ih =>
    have hnprev : n ≤ order.slots := by omega
    have hslot : n < order.slots := by omega
    apply law_eq_of_map_state game order
    have hsplit : (game.serialized order).information.runBehavioralFrom profile (n+1) (boundaryHistory game order h) =
        ((game.serialized order).information.runBehavioralFrom profile n (boundaryHistory game order h)).bind
          ((game.serialized order).information.runBehavioralFrom profile 1) :=
      (game.serialized order).execution.runRandomizedFor_add
        ((game.serialized order).information.randomizedChooser profile) n 1 (boundaryHistory game order h)
    rw [hsplit,PMF.map_bind,ih hnprev,PMF.bind_map,PMF.map_comp]
    have hs (p : Prefix game.toFOSG order h n) :
        (((game.serialized order).information.runBehavioralFrom profile 1
          (Serialization.historyAtPrefix game.toFOSG order h ht n p)).map ExecutionProtocol.History.state) =
        (Serialization.currentLaw game.toFOSG order profile h (order.player ⟨n,hslot⟩)).map
          (fun c => .stage h (n+1) (p.advance hslot c)) :=
      prefix_run_one_map_state game order profile h ht p hslot _
    dsimp only [Function.comp_def]
    simp_rw [hs]
    simp only [Serialization.prefixLaw]
    rw [bindPairLaw,PMF.map_bind,PMF.map_bind]
    apply congrArg ((Serialization.prefixLaw game.toFOSG order profile h n hnprev).bind)
    funext p
    rw [PMF.map_comp,PMF.map_comp]
    rfl

end KFOL.Rounds.Game.SerialRun
