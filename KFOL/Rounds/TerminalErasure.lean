module

public import KFOL.Rounds.SequentialExistence
public import KFOL.Rounds.SerializationTrace
public import KFOL.Rounds.Values

/-! # Exact terminal continuation laws at every public boundary -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- The source/serial law theorem applies to complete terminal continuations
at every public history. Certified fuel is removed on both sides. -/
theorem erase_terminal_continuation (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) :
    ((game.serialized order).information.runBehavioralTerminalFrom
      (game.serial_well_founded_histories order) profile
      ⟨.stage h 0 (Prefix.initial (G := game.toFOSG) (order := order) h),
        Serialization.boundaryTrace game.toFOSG order h.trace⟩).map
      (eraseHistory game.toFOSG order) =
    game.information.runBehavioralTerminalFrom game.well_founded_histories
      (projectBehavioral game.toFOSG order profile) h := by
  obtain ⟨sourceBound,_,hs⟩ := game.exists_bounded_horizon
  obtain ⟨targetBound,_,ht⟩ := game.serial_exists_bounded_horizon order
  let fuel := sourceBound + targetBound
  have sourceLarge : game.execution.BoundedHorizon fuel := by
    intro state trace hlen
    exact hs state trace (le_trans (by dsimp [fuel]; omega) hlen)
  have targetLarge : (game.serialized order).execution.BoundedHorizon (fuel * roundWidth order) := by
    intro state trace hlen
    apply ht state trace
    apply le_trans (show targetBound ≤ fuel * roundWidth order from ?_) hlen
    exact le_trans (by dsimp [fuel]; omega)
      (Nat.le_mul_of_pos_right fuel (Nat.succ_pos _))
  rw [(game.serialized order).information.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (game.serial_well_founded_histories order) targetLarge,
    game.information.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
      game.well_founded_histories sourceLarge]
  exact map_erase_runBehavioralFrom_eq_source game.toFOSG order profile fuel h _

/-- Winner distributions agree at every public boundary under every profile,
including all whole-player deviations. -/
theorem terminal_winner_law (game : Game Role) (order : ExplicitOrder Role)
    (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) :
    ((game.serialized order).information.runBehavioralTerminalFrom
      (game.serial_well_founded_histories order) profile
      ⟨.stage h 0 (Prefix.initial (G := game.toFOSG) (order := order) h),
        Serialization.boundaryTrace game.toFOSG order h.trace⟩).map (game.serialWinner order) =
    (game.information.runBehavioralTerminalFrom game.well_founded_histories
      (projectBehavioral game.toFOSG order profile) h).map game.winner := by
  calc
    _ = (((game.serialized order).information.runBehavioralTerminalFrom
        (game.serial_well_founded_histories order) profile
        ⟨.stage h 0 (Prefix.initial (G := game.toFOSG) (order := order) h),
          Serialization.boundaryTrace game.toFOSG order h.trace⟩).map
            (eraseHistory game.toFOSG order)).map game.winner := by
      rw [PMF.map_comp]
      rfl
    _ = _ := congrArg (PMF.map game.winner) (game.erase_terminal_continuation order profile h)

end KFOL.Rounds.Game
