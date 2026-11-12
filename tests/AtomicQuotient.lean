module

import KFOL.Core.AtomicBasis.Basis

/-! Independent table checks at the ambiguity/atom boundary. -/

open KFOL KFOL.Core.AtomicBasis

example : choice (0 : Fin 3) none (some 0) = some 0 := by decide
example : choice (0 : Fin 3) none (some 1) = none := by decide
example : choice (0 : Fin 3) (some 1) (some 2) = none := by decide
example : choice (0 : Fin 3) (some 1) (some 1) = some 1 := by decide

/-- Distinct ambiguous winner sets have exactly the same quotient value. -/
example : collapse ((WinnerSet.singleton (0 : Fin 3)).union (WinnerSet.singleton 1)) =
    collapse ((WinnerSet.singleton (0 : Fin 3)).union (WinnerSet.singleton 2)) := by
  apply ext_atoms
  intro i
  simp only [collapse_eq_some, WinnerSet.union_eq_singleton_iff, WinnerSet.singleton_inj]
  constructor <;> rintro ⟨h0, h1⟩ <;> omega

example : Fintype.card (BasisIndex (Fin 3)) = 22 := by rw [basisIndex_card]; rfl
example : Fintype.card (BasisIndex (Fin 4)) = 32 := by rw [basisIndex_card]; rfl

example : (theory (Function.Embedding.refl (Fin 3)) [0, 1, 2]).ncard = 22 := by
  rw [theory_ncard]
  rfl
