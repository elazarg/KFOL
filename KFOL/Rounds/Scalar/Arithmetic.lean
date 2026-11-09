module

public import KFOL.Rounds.Scalar.Diagonal

/-! # Parallel-sum arithmetic, including every zero boundary -/

@[expose] public section

namespace KFOL.Rounds.Game.Scalar

@[simp] theorem parallel_zero_left (x : ℝ) : parallel 0 x = 0 := by simp [parallel]
@[simp] theorem parallel_zero_right (x : ℝ) : parallel x 0 = 0 := by simp [parallel]

theorem parallel_comm (x y : ℝ) : parallel x y = parallel y x := by
  unfold parallel
  rw [mul_comm x y,add_comm x y]

theorem parallel_nonneg (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ parallel x y := div_nonneg (mul_nonneg hx hy) (add_nonneg hx hy)

theorem parallel_le_left (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    parallel x y ≤ x := by
  by_cases hs : x+y = 0
  · simp [parallel,hs,hx]
  · have hp : 0 < x+y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hs)
    apply (div_le_iff₀ hp).2
    nlinarith [sq_nonneg x]

theorem parallel_le_right (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    parallel x y ≤ y := by
  rw [parallel_comm]
  exact parallel_le_left y x hy hx

theorem parallel_le_one (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) :
    parallel x y ≤ 1 := le_trans (parallel_le_left x y hx0 hy0) hx1

/-- The reciprocal-game induction uses exactly this one-occurrence step. -/
theorem parallel_reciprocal_one (n : ℕ) :
    parallel (1/((n:ℝ)+1)) 1 = 1/((n:ℝ)+2) := by
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hm : (n:ℝ)+2 ≠ 0 := by positivity
  unfold parallel
  field_simp
  ring

/-- Reciprocal values turn positive parallel sum into addition. -/
theorem parallel_inv (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (parallel x y)⁻¹ = x⁻¹+y⁻¹ := by
  unfold parallel
  field_simp
  ring

theorem parallel_pos (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 < parallel x y := div_pos (mul_pos hx hy) (add_pos hx hy)

/-- Parallel sum is associative on all nonnegative arguments, including zeros. -/
theorem parallel_assoc (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    parallel (parallel x y) z = parallel x (parallel y z) := by
  by_cases hx0 : x = 0
  · subst x; simp
  by_cases hy0 : y = 0
  · subst y; simp
  by_cases hz0 : z = 0
  · subst z; simp
  have hxy : parallel x y ≠ 0 :=
    (parallel_pos x y (lt_of_le_of_ne hx (Ne.symm hx0)) (lt_of_le_of_ne hy (Ne.symm hy0))).ne'
  have hyz : parallel y z ≠ 0 :=
    (parallel_pos y z (lt_of_le_of_ne hy (Ne.symm hy0)) (lt_of_le_of_ne hz (Ne.symm hz0))).ne'
  apply inv_injective
  rw [parallel_inv _ _ hxy hz0,parallel_inv _ _ hx0 hyz,
    parallel_inv _ _ hx0 hy0,parallel_inv _ _ hy0 hz0]
  ring

/-- Parallel sum is monotone in either nonnegative argument. -/
theorem parallel_mono_left (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxy : x ≤ y) : parallel x z ≤ parallel y z := by
  by_cases hz0 : z = 0
  · subst z; simp
  have hpz : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  have hxz : 0 < x+z := add_pos_of_nonneg_of_pos hx hpz
  have hyz : 0 < y+z := add_pos_of_nonneg_of_pos hy hpz
  apply (div_le_div_iff₀ hxz hyz).2
  have hm := mul_nonneg (sub_nonneg.mpr hxy) (sq_nonneg z)
  nlinarith

theorem parallel_mono_right (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxy : x ≤ y) : parallel z x ≤ parallel z y := by
  rw [parallel_comm z x,parallel_comm z y]
  exact parallel_mono_left x y z hx hy hz hxy

/-- Monotonicity on the chain gives both distributivity laws. -/
theorem parallel_min (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    parallel x (min y z) = min (parallel x y) (parallel x z) := by
  rcases le_total y z with h | h
  · rw [min_eq_left h,min_eq_left (parallel_mono_right y z x hy hz hx h)]
  · rw [min_eq_right h,min_eq_right (parallel_mono_right z y x hz hy hx h)]

theorem parallel_max (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    parallel x (max y z) = max (parallel x y) (parallel x z) := by
  rcases le_total y z with h | h
  · rw [max_eq_right h,max_eq_right (parallel_mono_right y z x hy hz hx h)]
  · rw [max_eq_left h,max_eq_left (parallel_mono_right z y x hz hy hx h)]

end KFOL.Rounds.Game.Scalar
