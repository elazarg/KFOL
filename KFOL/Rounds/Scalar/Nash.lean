module

public import KFOL.Rounds.Scalar.Diagonal

/-! # Canonical Nash uniqueness for the actual diagonal scalar stage -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- The four actual pure deviations alone force the diagonal value in every
canonical mixed Nash equilibrium. This includes both zero entries. -/
theorem diagonal_nash_value (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (profile : (i : Role) → PMF (Fin (binarySizes a b i+1)))
    (nash : IsNash (stageForm (binarySizes a b) (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed
      (euPreference (fun winner i => winnerPayoff id i winner)) profile) :
    (((independentProduct profile).bind (diagonalTable a b
      (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))) a).toReal = parallel x y := by
  let table := diagonalTable a b (distribution a b x hx0 hx1) (distribution a b y hy0 hy1)
  let value := (((independentProduct profile).bind table) a).toReal
  have hp (other : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
      (((independentProduct other).bind table) a).toReal =
        x * zeroProbability other a * zeroProbability other b +
        y * (1-zeroProbability other a) * (1-zeroProbability other b) :=
    diagonal_stage_coordinate a b hab x y hx0 hx1 hy0 hy1 other
  have hc (other : (i : Role) → PMF (Fin (binarySizes a b i+1))) :
      (((independentProduct other).bind table) b).toReal =
        1-(((independentProduct other).bind table) a).toReal :=
    diagonal_stage_complement a b hab x y hx0 hx1 hy0 hy1 other
  have hn := (Observed.stage_nash_iff (binarySizes a b) table profile).mp nash
  have r0 := hn a (PMF.pure 0)
  have r1 := hn a (PMF.pure (oneAction a b a (Or.inl rfl)))
  have c0 := hn b (PMF.pure 0)
  have c1 := hn b (PMF.pure (oneAction a b b (Or.inr rfl)))
  change _ ≤ value at r0 r1
  simp only [hp,zeroProbability_update_zero,zeroProbability_update_other a b a b hab.symm,
    mul_one,sub_self] at r0
  simp only [hp,zeroProbability_update_one,zeroProbability_update_other a b a b hab.symm,
    mul_zero,sub_zero] at r1
  rw [hc,hc] at c0 c1
  change 1-_ ≤ 1-value at c0 c1
  simp only [hp,zeroProbability_update_zero,zeroProbability_update_other a b b a hab,
    mul_one,sub_self,mul_zero,add_zero] at c0
  simp only [hp,zeroProbability_update_one,zeroProbability_update_other a b b a hab,
    mul_zero,sub_zero,mul_one,zero_add] at c1
  have lower := add_le_add (mul_le_mul_of_nonneg_left r0 hy0)
    (mul_le_mul_of_nonneg_left r1 hx0)
  have upper := add_le_add (mul_le_mul_of_nonneg_left c0 hy0)
    (mul_le_mul_of_nonneg_left c1 hx0)
  change value = parallel x y
  by_cases hs : x+y = 0
  · have hx : x = 0 := by linarith
    have hy : y = 0 := by linarith
    simp [parallel,hx,hy,value,hp]
  · apply (eq_div_iff hs).2
    nlinarith [lower,upper]

end KFOL.Rounds.Game.Scalar
