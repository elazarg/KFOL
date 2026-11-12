module

public import KFOL.Definitions.Public

/-! # Atomic staircase rows

Each row has one tracked-owner atom, with the other columns before and after
it assigned the two endpoint owners.
-/

@[expose] public section
namespace KFOL.Core.Staircase
universe u
variable {Role : Type u}

/-- The i-th edge of the atomic staircase from constant b to constant c. -/
def row (a b c : Role) {n : Nat} (i j : Fin n) : WinnerSet Role :=
  if j.val < i.val then WinnerSet.singleton c
  else if j = i then WinnerSet.singleton a else WinnerSet.singleton b

/-- A Boolean endpoint of the staircase. -/
def vertex (b c : Role) {n : Nat} (k : Nat) (j : Fin n) : WinnerSet Role :=
  if j.val < k then WinnerSet.singleton c else WinnerSet.singleton b

end KFOL.Core.Staircase
