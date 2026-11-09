module

public import KFOL.Complexity.GuardSubset

/-! Coordinate order, exact widths, zero-width inputs and the guard bridge. -/

@[expose] public section

namespace KFOLTest.GuardWords

open KFOL KFOL.Algorithms

example : Bitset.encode ({0, 2} : Finset (Fin 4)) = [true, false, true, false] := by decide
example : Bitset.decode 4 [true, false, true, false] = some {0, 2} := by decide
example : Bitset.decode 3 [true, false, true, false] = none := by decide
example : Bitset.decode 0 [] = some ∅ := by decide

example : GuardWords.subsetWord [true, false, true, false] [true, true, true, false] = [true] :=
  by decide
example : GuardWords.subsetWord [false, false, false, true] [true, false, false, false] =
    [false] := by decide

-- Padding is not accepted as an alternative width, even for empty sets.
example : GuardWords.subsetWord [] [] = [true] ∧
    GuardWords.subsetWord [] [false] = [false] ∧
    GuardWords.subsetWord [false] [] = [false] := by decide

-- Exercise the exact fixed-arity function whose machine certificate is proved.
example : GuardWords.subsetFn (fun i => if i = 0 then [false, true] else [true, false]) =
    [false] := by decide

private def candidate : Reset.GuardTable (Fin 4) where
  root := 0
  guards := fun j => if j = 0 then {∅} else if j = 3 then {{0, 2}} else ∅

example : candidate.Enabled (({0, 2} : Finset (Fin 4)) : Set (Fin 4)) 3 := by
  apply (enabled_iff_subsetWord candidate {0, 2} 3).mpr
  exact ⟨{0, 2}, by decide, by decide⟩

end KFOLTest.GuardWords
