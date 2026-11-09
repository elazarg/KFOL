module

public import KFOL.Rounds.Tree
public import Mathlib.Order.Interval.Set.Nat

/-! # Finite histories of the accepted serial round implementation -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game

open GameTheory.Protocol GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u}

/-- All source menus are finite, including the inactive terminal option. -/
instance finite_choiceAt (game : Game Role) (history : game.execution.History) (i : Role) :
    Finite (ChoiceAt game.toFOSG history i) := by
  apply Set.finite_coe_iff.mpr
  apply ((Set.finite_Iic (history.state.current.size i)).image some).insert none |>.subset
  intro c hc
  cases c with
  | none => exact Set.mem_insert _ _
  | some a =>
    exact Set.mem_insert_of_mem _ ⟨a,hc.2,rfl⟩

/-- A stored prefix has only finitely many legal choices. -/
instance finite_prefix [Finite Role] (game : Game Role) (order : ExplicitOrder Role)
    (history : game.execution.History) (count : ℕ) :
    Finite (Prefix game.toFOSG order history count) := by
  apply Finite.of_injective (fun p : Prefix game.toFOSG order history count => p.choices)
  intro p q he
  exact Prefix.ext he

/-- The count is bounded by the explicit schedule; completed source prefixes
and partially collected current tuples together form a finite state carrier. -/
instance finite_serial_state [Finite Role] [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) : Finite (game.serialized order).execution.State := by
  apply Finite.of_surjective
    (fun p : (history : game.execution.History) × (n : Fin (order.slots+1)) ×
        Prefix game.toFOSG order history n.val => State.stage p.1 p.2.1.val p.2.2)
  intro p
  cases p with
  | stage h n collected =>
    exact ⟨⟨h,⟨n,by have := collected.count_le; omega⟩,collected⟩,rfl⟩

/-- The accepted serializer stores enough history to retain a unique trace. -/
theorem serial_tree_shaped [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) : (game.serialized order).execution.IsTreeShaped :=
  treeShaped game.toFOSG order

instance finite_serial_history [Finite Role] [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) : Finite (game.serialized order).execution.History := by
  let _ : Fintype (game.serialized order).execution.State := Fintype.ofFinite _
  let _ := (game.serialized order).execution.historyFintype (game.serial_tree_shaped order)
  infer_instance

theorem serial_exists_bounded_horizon [Finite Role] [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) :
    ∃ bound, 0 < bound ∧ (game.serialized order).execution.BoundedHorizon bound :=
  (game.serialized order).execution.exists_pos_boundedHorizon

theorem serial_well_founded_histories [Finite Role] [DecidableEq Role] (game : Game Role)
    (order : ExplicitOrder Role) : (game.serialized order).execution.WellFoundedHistories :=
  (game.serialized order).execution.wellFoundedHistories_of_fintype

end KFOL.Rounds.Game
