module

public import KFOL.Rounds.Scalar.Threshold
public import KFOL.Rounds.Scalar.Support

/-! # Exact threshold winner observations in the actual serial game semantics -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

private theorem reciprocal_rate_lt (n m : ℕ) (hnm : n < m) :
    1/(((m+1:ℕ):ℝ)+1) < 1/(((n+1:ℕ):ℝ)+1) := by
  apply one_div_lt_one_div_of_lt (by positivity)
  exact_mod_cast (show (n+1)+1 < (m+1)+1 by omega)

/-- The complete main-paper threshold formula, for actual finite game syntax
and canonical serial SE winner distributions. -/
theorem possibleWinners_threshold (a b c : Role) (hab : a ≠ b) (hac : a ≠ c)
    (n m : ℕ) (order : ExplicitOrder Role) :
    possibleWinners ((threshold a b c n m).sequentialValues order) =
      if n < m then {a,b} else if n = m then {a,b,c} else {a,c} := by
  by_cases hnm : n < m
  · rw [ite_eq_left hnm]
    have he : (threshold a b c n m).sequentialValues order =
        {reciprocalDistribution a b (n+1)} := by
      apply publicChoice_singletons_of_gt a _ _ order _ _
        (sequentialValues_reciprocal a b hab (n+1) order)
        (sequentialValues_reciprocal a c hac (m+1) order)
      simpa only [reciprocalDistribution_a a b hab,reciprocalDistribution_a a c hac] using
        reciprocal_rate_lt n m hnm
    rw [he]
    exact possibleWinners_reciprocalDistribution_succ a b hab n
  · rw [ite_eq_right hnm]
    by_cases heq : n = m
    · rw [ite_eq_left heq]
      subst m
      rw [threshold,possibleWinners_publicChoice_of_eq a _ _ order
        (reciprocalDistribution a b (n+1)) (reciprocalDistribution a c (n+1))
        (sequentialValues_reciprocal a b hab (n+1) order)
        (sequentialValues_reciprocal a c hac (n+1) order)
        (by simp only [reciprocalDistribution_a a b hab,reciprocalDistribution_a a c hac]),
        possibleWinners_reciprocalDistribution_succ a b hab,
        possibleWinners_reciprocalDistribution_succ a c hac]
      ext who
      simp only [Set.mem_union,Set.mem_insert_iff,Set.mem_singleton_iff]
      tauto
    · rw [ite_eq_right heq]
      have hmn : m < n := by omega
      have he : (threshold a b c n m).sequentialValues order =
          {reciprocalDistribution a c (m+1)} := by
        apply publicChoice_singletons_of_lt a _ _ order _ _
          (sequentialValues_reciprocal a b hab (n+1) order)
          (sequentialValues_reciprocal a c hac (m+1) order)
        simpa only [reciprocalDistribution_a a b hab,reciprocalDistribution_a a c hac] using
          reciprocal_rate_lt m n hmn
      rw [he]
      exact possibleWinners_reciprocalDistribution_succ a c hac m

/-- The third role's actual possible-victory observation is the precise
integer threshold used to distinguish every two reciprocal components. -/
theorem third_possible_threshold_iff (a b c : Role) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (n m : ℕ) (order : ExplicitOrder Role) :
    c ∈ possibleWinners ((threshold a b c n m).sequentialValues order) ↔ m ≤ n := by
  rw [possibleWinners_threshold a b c hab hac]
  split_ifs with hnm heq
  · simp [hac.symm,hbc.symm,show ¬ m ≤ n by omega]
  · simp [show m ≤ n by omega]
  · simp [show m ≤ n by omega]

end KFOL.Rounds.Game.Scalar
