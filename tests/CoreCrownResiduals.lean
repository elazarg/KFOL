import KFOL.Core.CrownResiduals
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open KFOL KFOL.Core.Crown

namespace CoreCrownResidualsTests

-- The three-input assumption matters: with only two inputs, the exceptional
-- output can introduce b, which has no source outside the ambiguous input.
private def values : Fin 2 → WinnerSet (Fin 3) :=
  ![WinnerSet.singleton 2, ⟨{0, 2}, by simp⟩]

example : (values 1).Ambiguous := by
  intro r he
  have h0 : (0 : Fin 3) = r := by
    have h : (0 : Fin 3) ∈ (WinnerSet.singleton r).val := by
      rw [← he]
      simp [values]
    exact h
  have h2 : (2 : Fin 3) = r := by
    have h : (2 : Fin 3) ∈ (WinnerSet.singleton r).val := by
      rw [← he]
      simp [values]
    exact h
  omega

example : 1 ∉ (values 1).val := by simp [values]

example : 1 ∈ (operation 1 2 (Equiv.swap 0 1) {0} values).val := by
  have h : Cylinder 1 2 (Equiv.swap 0 1) 0 values := by
    refine ⟨rfl, ?_, ?_, ?_⟩
    · intro he
      have hm : (0 : Fin 3) ∈ (WinnerSet.singleton 1).val := by
        rw [← he]
        simp [values]
      simp at hm
    · intro he
      have hm : (0 : Fin 3) ∈ (WinnerSet.singleton 2).val := by
        rw [← he]
        simp [values]
      simp at hm
    · intro j hj0 hj1
      fin_cases j <;> simp_all
  unfold operation
  rw [ite_eq_left (show ∃ i ∈ ({0} : Set (Fin 2)),
    Cylinder 1 2 (Equiv.swap 0 1) i values from ⟨0, rfl, h⟩)]
  simp

example : ¬∃ i, i ≠ (1 : Fin 2) ∧ 1 ∈ (values i).val := by
  rintro ⟨i, hi, h⟩
  fin_cases i <;> simp_all [values]

end CoreCrownResidualsTests
