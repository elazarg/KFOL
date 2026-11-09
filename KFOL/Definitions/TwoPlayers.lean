module

public import KFOL.Definitions.Public

/-! # Canonical two-player truth values

The labels `e 0` and `e 1` denote the top and bottom player respectively.
The intervening value is their nonempty union. The truth chain uses the
ordinary order on Fin 3: bottom 0, ambiguity 1, top 2.
-/

@[expose] public section

namespace KFOL.TwoPlayers

universe u

/-- The three strong-Kleene truth values in the shared nonempty-set carrier. -/
def value {Role : Type u} (e : Fin 2 ≃ Role) (i : Fin 3) : WinnerSet Role :=
  if i = 0 then WinnerSet.singleton (e 1)
  else if i = 1 then (WinnerSet.singleton (e 0)).union (WinnerSet.singleton (e 1))
  else WinnerSet.singleton (e 0)

/-- Read the truth-chain position directly from the winner set. -/
noncomputable def rank {Role : Type u} (e : Fin 2 ≃ Role) (A : WinnerSet Role) : Fin 3 := by
  classical
  exact if A = WinnerSet.singleton (e 1) then 0
    else if A = WinnerSet.singleton (e 0) then 2 else 1

/-- The two atomic equality tests, as Boolean coordinates. -/
noncomputable def forcingCoordinates {Role : Type u} (e : Fin 2 ≃ Role)
    (A : WinnerSet Role) : Bool × Bool := by
  classical
  exact (decide (A = WinnerSet.singleton (e 0)),decide (A = WinnerSet.singleton (e 1)))

end KFOL.TwoPlayers
