module

public import KFOL.Definitions.Public
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Set.Lattice.Indexed

/-! # Interval-selected winner operations and Boolean separators

A selected interval prescribes the pair of named endpoint winners. Other
inputs return their full union. The specification and separator conditions
are independent of term syntax and realizability.
-/

@[expose] public section
namespace KFOL.Core.Intervals
universe u v
variable {Role : Type u} {Var : Type v}

/-- Positions at the upper named singleton. -/
noncomputable def lowerInputs [Fintype Var] (c : Role)
    (values : Var → WinnerSet Role) : Finset Var := by
  classical
  exact Finset.univ.filter (fun j => values j = WinnerSet.singleton c)

/-- Positions that are not the lower named singleton. -/
noncomputable def upperInputs [Fintype Var] (b : Role)
    (values : Var → WinnerSet Role) : Finset Var := by
  classical
  exact Finset.univ.filter (fun j => values j ≠ WinnerSet.singleton b)

/-- The full union of a nonempty family of inputs. -/
noncomputable def inputUnion [Nonempty Var] (values : Var → WinnerSet Role) :
    WinnerSet Role :=
  ⟨⋃ j, (values j).val, by
    obtain ⟨j⟩ := ‹Nonempty Var›
    obtain ⟨r, hr⟩ := (values j).property
    exact ⟨r, Set.mem_iUnion.mpr ⟨j, hr⟩⟩⟩

/-- Collapse selected intervals to the named endpoint pair. -/
noncomputable def operation [Fintype Var] [Nonempty Var] (b c : Role)
    (selected : Set (Finset Var × Finset Var)) (values : Var → WinnerSet Role) :
    WinnerSet Role := by
  classical
  exact if (lowerInputs c values, upperInputs b values) ∈ selected then
    (WinnerSet.singleton b).union (WinnerSet.singleton c) else inputUnion values

/-- A normalized monotone Boolean cut constant on every selected interval. -/
structure Good [Fintype Var] (selected : Set (Finset Var × Finset Var))
    (φ : Finset Var → Bool) : Prop where
  mono : Monotone φ
  bot : φ ∅ = false
  top : φ Finset.univ = true
  edge : ∀ L U, (L,U) ∈ selected → φ L = φ U

/-- Selected intervals are strict and avoid the empty and full endpoints. -/
def Proper [Fintype Var] (selected : Set (Finset Var × Finset Var)) : Prop :=
  ∀ L U, (L,U) ∈ selected → L.Nonempty ∧ L ⊂ U ∧ U ≠ Finset.univ

/-- One allowed Boolean cut separates the interval endpoints. -/
def Separates [Fintype Var] (selected : Set (Finset Var × Finset Var))
    (L U : Finset Var) : Prop :=
  ∃ φ : Finset Var → Bool, Good selected φ ∧ φ L = false ∧ φ U = true

end KFOL.Core.Intervals
