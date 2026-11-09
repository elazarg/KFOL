module

public import KFOL.Rounds.Scalar.Extrema

/-! # Rational scalar syntax evaluates through actual canonical equilibria -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.ScalarTerm

/-- Every generated rational scalar is a valid probability, including the
both-zero diagonal boundary. -/
theorem rate_valid (term : ScalarTerm) : 0 ≤ term.rate ∧ term.rate ≤ 1 := by
  induction term with
  | zero => norm_num [rate]
  | one => norm_num [rate]
  | diagonal left right hl hr =>
    dsimp only [rate]
    constructor
    · exact div_nonneg (mul_nonneg hl.1 hr.1) (add_nonneg hl.1 hr.1)
    · by_cases hs : left.rate+right.rate = 0
      · simp [hs]
      · have hp : 0 < left.rate+right.rate :=
          lt_of_le_of_ne (add_nonneg hl.1 hr.1) (Ne.symm hs)
        apply (div_le_one hp).2
        have hm := mul_le_mul_of_nonneg_left hr.2 hl.1
        linarith
  | complement term ih => dsimp only [rate]; constructor <;> linarith [ih.1,ih.2]
  | sup left right hl hr =>
    exact ⟨le_max_of_le_left hl.1,max_le hl.2 hr.2⟩
  | inf left right hl hr =>
    exact ⟨le_min hl.1 hr.1,(min_le_left _ _).trans hl.2⟩

theorem rate_nonneg_real (term : ScalarTerm) : (0:ℝ) ≤ term.rate := by
  exact_mod_cast (rate_valid term).1

theorem rate_le_one_real (term : ScalarTerm) : (term.rate:ℝ) ≤ 1 := by
  exact_mod_cast (rate_valid term).2

end KFOL.Rounds.Game.ScalarTerm

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Every closed scalar syntax component has exactly its rational arithmetic
winner law as its actual canonical serial-SE value set. -/
theorem sequentialValues_scalarTerm (term : ScalarTerm) (a b : Role) (hab : a ≠ b)
    (order : ExplicitOrder Role) :
    (term.game a b).sequentialValues order =
      {distribution a b (term.rate:ℝ) term.rate_nonneg_real term.rate_le_one_real} := by
  induction term generalizing a b with
  | zero =>
    simpa only [ScalarTerm.game,ScalarTerm.rate,Rat.cast_zero,distribution_zero] using
      sequentialValues_leaf (Role := Role) b order
  | one =>
    simpa only [ScalarTerm.game,ScalarTerm.rate,Rat.cast_one,distribution_one] using
      sequentialValues_leaf (Role := Role) a order
  | diagonal left right hl hr =>
    have he := sequentialValues_diagonal a b hab (left.game a b) (right.game a b)
      (left.rate:ℝ) (right.rate:ℝ) left.rate_nonneg_real left.rate_le_one_real
      right.rate_nonneg_real right.rate_le_one_real order (hl a b hab) (hr a b hab)
    simpa only [ScalarTerm.game,ScalarTerm.rate,Rat.cast_div,Rat.cast_mul,Rat.cast_add,parallel] using he
  | complement term ih =>
    rw [ScalarTerm.game,ih b a hab.symm]
    simp only [ScalarTerm.rate,Rat.cast_sub,Rat.cast_one,distribution]
    exact congrArg (fun law : PMF Role => ({law} : Set (PMF Role)))
      (mix_swap (term.rate:ℝ) term.rate_nonneg_real term.rate_le_one_real
        (PMF.pure b) (PMF.pure a)).symm
  | sup left right hl hr =>
    have he := sequentialValues_public_max a b hab (left.game a b) (right.game a b) order
      (left.rate:ℝ) (right.rate:ℝ) left.rate_nonneg_real left.rate_le_one_real
      right.rate_nonneg_real right.rate_le_one_real (hl a b hab) (hr a b hab)
    simpa only [ScalarTerm.game,ScalarTerm.rate,Rat.cast_max] using he
  | inf left right hl hr =>
    have he := sequentialValues_public_min a b hab (left.game a b) (right.game a b) order
      (left.rate:ℝ) (right.rate:ℝ) left.rate_nonneg_real left.rate_le_one_real
      right.rate_nonneg_real right.rate_le_one_real (hl a b hab) (hr a b hab)
    simpa only [ScalarTerm.game,ScalarTerm.rate,Rat.cast_min] using he

end KFOL.Rounds.Game.Scalar
