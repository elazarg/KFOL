import KFOL.Complexity.ResetUnionWordCompleteness

/-! Regression cases for sparse CNF construction and its exact source boundary. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

open KFOL.Reductions

example : ResetUnion.support [] = [0] := by decide

example : ResetUnion.support [[(100000, true), (7, false), (100000, false)]] =
    [0, 7, 100000] := by decide

example : ResetUnion.literalName (100000, true) = 200003 := by decide

example : ResetUnion.literalName (100000, false) = 200004 := by decide

private def sparse : CNF := [[(2 ^ 30, true)]]

-- A billion-sized name contributes its binary digits, not a billion positions.
example : (ResetUnion.support sparse).length = 2 := by decide

example : (KFOL.ResetUnion.Code.encodeEquation (ResetUnion.equation sparse)).length < 5000 := by decide

example :
    (KFOL.ResetUnion.Code.decodeEquation
      (KFOL.ResetUnion.Code.encodeEquation (ResetUnion.equation [[(7, true)]]))).map
        KFOL.ResetUnion.Code.encodeEquation =
      some (KFOL.ResetUnion.Code.encodeEquation (ResetUnion.equation [[(7, true)]])) := by decide

-- Outside the source 3SAT language, wide clauses map to a valid identity.
example : KFOL.ResetUnion.Code.encodeEquation
    (KFOL.Complexity.ResetUnionSource.threeSATReduction [[(0, true), (1, true), (2, true), (3, true)]]) =
      KFOL.ResetUnion.Code.encodeEquation (.var 0, .var 0) := by decide

-- Empty source objects retain their distinct logical meanings.
example : ¬KFOL.ResetUnion.Valid (Fin 3) (ResetUnion.equation []) := by
  rw [ResetUnion.valid_equation_iff (Function.Embedding.refl (Fin 3))]
  intro h
  apply h
  exact ⟨fun _ => false, by simp⟩

example : KFOL.ResetUnion.Valid (Fin 3) (ResetUnion.equation [[]]) := by
  rw [ResetUnion.valid_equation_iff (Function.Embedding.refl (Fin 3))]
  rintro ⟨assignment, h⟩
  obtain ⟨literal, hl, _⟩ := h [] (by simp)
  simp at hl


example : KFOL.ResetUnion.Code.decode [true] = none := by decide

example : KFOL.ResetUnion.Code.decode [true, false] = none := by decide

example : KFOL.ResetUnion.Code.decode [false, false, false, false, true] = none := by decide

example : KFOL.ResetUnion.Code.decodeEquation
    (KFOL.Words.pair [true] (KFOL.ResetUnion.Code.encode (.var 0))) = none := by decide

example : KFOL.ResetUnion.Code.decodeEquation
    (KFOL.Words.pair (KFOL.ResetUnion.Code.encode (.var 0) ++ [false])
      (KFOL.ResetUnion.Code.encode (.var 1))) = none := by decide

example : Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits (KFOL.ResetUnion.Language (Fin 3)) :=
  KFOL.Complexity.ResetUnionWordCompleteness.coNPComplete (Function.Embedding.refl (Fin 3))
