module

import KFOL.Reductions.ResetUnionCorrectness
import KFOL.Reductions.ResetUnionSize

namespace KFOLTest.ResetUnionReduction

open KFOL

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _

example : ResetUnion.Valid (Fin 3) (Reductions.ResetUnion.equation [[]]) := by
  apply (Reductions.ResetUnion.valid_equation_iff three _).mpr
  simp [Reductions.Satisfiable]

example : ¬ ResetUnion.Valid (Fin 3) (Reductions.ResetUnion.equation []) := by
  rw [Reductions.ResetUnion.valid_equation_iff three]
  simp [Reductions.Satisfiable]

example : ResetUnion.Valid (Fin 3)
    (Reductions.ResetUnion.equation [[(2^30, true)], [(2^30, false)]]) := by
  apply (Reductions.ResetUnion.valid_equation_iff three _).mpr
  rintro ⟨a, ha⟩
  have ht := ha [(2^30, true)] (by simp)
  have hf := ha [(2^30, false)] (by simp)
  simp only [List.mem_singleton, exists_eq_left] at ht hf
  exact Bool.false_ne_true (hf.symm.trans ht)

example : (Reductions.ResetUnion.equation []).1.size +
    (Reductions.ResetUnion.equation []).2.size = 36 := by decide

#print axioms KFOL.Reductions.ResetUnion.valid_equation_iff
#print axioms KFOL.Reductions.ResetUnion.size_equation_linear

end KFOLTest.ResetUnionReduction
