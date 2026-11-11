module

public import KFOL.Definitions.Public
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Set.Lattice.Indexed

/-! # Cyclic rows and their exceptional input regions

The rows and regions are specified directly from variable positions and
singleton values. They do not use term realizability or a closure procedure.
-/

@[expose] public section
namespace KFOL.Core.Crown

universe u v
variable {Role : Type u} {Var : Type v}

/-- A cyclic matching-edge row: c at i, a at its successor, b elsewhere. -/
noncomputable def negative (three : Fin 3 ↪ Role) (next : Equiv.Perm Var)
    (i : Var) : Var → WinnerSet Role := by
  classical
  exact fun j => if j = i then WinnerSet.singleton (three 2)
    else if j = next i then WinnerSet.singleton (three 0)
    else WinnerSet.singleton (three 1)

/-- The opposite edge of the same two-coordinate square. -/
noncomputable def positive (three : Fin 3 ↪ Role) (next : Equiv.Perm Var)
    (i : Var) : Var → WinnerSet Role := by
  classical
  exact fun j => if j = i then WinnerSet.singleton (three 0)
    else if j = next i then WinnerSet.singleton (three 2)
    else WinnerSet.singleton (three 1)

/-- One c input, a successor input that is neither b nor c, and b elsewhere. -/
def Cylinder (b c : Role) (next : Equiv.Perm Var) (i : Var)
    (values : Var → WinnerSet Role) : Prop :=
  values i = WinnerSet.singleton c ∧
    values (next i) ≠ WinnerSet.singleton b ∧
    values (next i) ≠ WinnerSet.singleton c ∧
    ∀ j, j ≠ i → j ≠ next i → values j = WinnerSet.singleton b

/-- The full union of a nonempty family of input values. -/
noncomputable def inputUnion [Nonempty Var] (values : Var → WinnerSet Role) : WinnerSet Role :=
  ⟨(⋃ j, (values j).val), by
    obtain ⟨j⟩ := ‹Nonempty Var›
    obtain ⟨r, hr⟩ := (values j).property
    exact ⟨r, Set.mem_iUnion.mpr ⟨j, hr⟩⟩⟩

/-- Return {b,c} on selected exceptional regions, and the full input union elsewhere. -/
noncomputable def operation [Nonempty Var] (b c : Role) (next : Equiv.Perm Var)
    (selected : Set Var) (values : Var → WinnerSet Role) : WinnerSet Role := by
  classical
  exact if ∃ i ∈ selected, Cylinder b c next i values then
    (WinnerSet.singleton b).union (WinnerSet.singleton c) else inputUnion values

end KFOL.Core.Crown
