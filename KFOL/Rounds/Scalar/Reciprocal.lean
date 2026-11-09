module

public import KFOL.Rounds.Scalar.Values
public import KFOL.Rounds.Correspondence

/-! # Actual reciprocal games have unique canonical equilibrium winner laws -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- The actual serial diagonal constructor has the parallel-sum singleton
law whenever its two continuation SE value sets are the corresponding scalar
singletons. No separate minimax or equilibrium-recursion hypothesis is needed. -/
theorem sequentialValues_diagonal (a b : Role) (hab : a ≠ b) (left right : Game Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (order : ExplicitOrder Role)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    (diagonal a b left right).sequentialValues order =
      {distribution a b (parallel x y) (parallel_nonneg x y hx0 hy0)
        (parallel_le_one x y hx0 hx1 hy0)} := by
  rw [sequentialValues_eq_observedValues] at hleft hright ⊢
  exact observedValues_diagonal a b hab left right x y hx0 hx1 hy0 hy1 hleft hright

/-- The canonical observed SPE value set of the actual linear-size game `Lₙ`
is the singleton reciprocal distribution. -/
theorem observedValues_reciprocal (a b : Role) (hab : a ≠ b) (n : ℕ) :
    (reciprocal a b n).observedValues = {reciprocalDistribution a b n} := by
  induction n with
  | zero =>
    simpa [reciprocal,reciprocalDistribution,distribution] using Observed.observedValues_leaf (Role := Role) a
  | succ n ih =>
    have hn0 : (0:ℝ) ≤ 1/((n:ℝ)+1) := by positivity
    have hn1 : 1/((n:ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).2
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hleaf : (Game.leaf a : Game Role).observedValues =
        {distribution a b 1 (by norm_num) le_rfl} := by
      simpa only [distribution_one] using Observed.observedValues_leaf (Role := Role) a
    have he := observedValues_diagonal a b hab (reciprocal a b n) (.leaf a)
      (1/((n:ℝ)+1)) 1 hn0 hn1 (by norm_num) le_rfl ih hleaf
    simpa only [reciprocal,reciprocalDistribution,parallel_reciprocal_one,
      Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1 = 2 by norm_num] using he

/-- Serial sequential equilibria of the actual reciprocal game have the same
unique complete winner law. The canonical SE/SPE bridge is already proved. -/
theorem sequentialValues_reciprocal (a b : Role) (hab : a ≠ b) (n : ℕ)
    (order : ExplicitOrder Role) :
    (reciprocal a b n).sequentialValues order = {reciprocalDistribution a b n} := by
  rw [sequentialValues_eq_observedValues]
  exact observedValues_reciprocal a b hab n

omit [Fintype Role] [DecidableEq Role] in
@[simp] theorem reciprocalDistribution_a (a b : Role) (hab : a ≠ b) (n : ℕ) :
    (reciprocalDistribution a b n a).toReal = 1/((n:ℝ)+1) :=
  distribution_a a b hab _ _ _

omit [Fintype Role] [DecidableEq Role] in
@[simp] theorem reciprocalDistribution_b (a b : Role) (hab : a ≠ b) (n : ℕ) :
    (reciprocalDistribution a b n b).toReal = (n:ℝ)/((n:ℝ)+1) := by
  rw [reciprocalDistribution,distribution_b a b hab]
  field_simp
  ring

end KFOL.Rounds.Game.Scalar
