module

public import KFOL.Definitions.Rounds
public import GameTheory.Math.Probability.Mixture
public import GameTheory.Math.Probability.Support

/-! # Actual two-winner distributions and their scalar coordinate -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory.Math.Probability

universe u
variable {Role : Type u}

@[simp] theorem distribution_a (a b : Role) (hab : a ≠ b) (x : ℝ)
    (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (distribution a b x h0 h1 a).toReal = x := by
  rw [distribution,mix_apply_toReal]
  simp [hab]

@[simp] theorem distribution_b (a b : Role) (hab : a ≠ b) (x : ℝ)
    (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (distribution a b x h0 h1 b).toReal = 1-x := by
  rw [distribution,mix_apply_toReal]
  simp [hab.symm]

@[simp] theorem distribution_other (a b who : Role) (ha : who ≠ a) (hb : who ≠ b)
    (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    distribution a b x h0 h1 who = 0 := by
  simp [distribution,mix_apply,ha,hb]

/-- In a two-winner law the two actual masses sum to one, even when the role
carrier is infinite. -/
theorem pair_mass_add (a b : Role) (hab : a ≠ b) (law : PMF Role)
    (support : ∀ who, who ≠ a → who ≠ b → law who = 0) :
    law a + law b = 1 := by
  classical
  have hsum : (∑' who, law who) = law a + law b := by
    rw [tsum_eq_sum (s := {a,b})]
    · simp [hab]
    · intro who hwho
      exact support who (by intro he; exact hwho (by simp [he]))
        (by intro he; exact hwho (by simp [he]))
  rw [← hsum,PMF.tsum_coe]

/-- An actual winner law supported on the two designated roles is completely
specified by its first real coordinate. -/
theorem eq_distribution (a b : Role) (hab : a ≠ b) (law : PMF Role)
    (support : ∀ who, who ≠ a → who ≠ b → law who = 0) :
    law = distribution a b (law a).toReal ENNReal.toReal_nonneg
      (pmf_toReal_apply_le_one law a) := by
  classical
  have hm := pair_mass_add a b hab law support
  have hr : (law a).toReal + (law b).toReal = 1 := by
    rw [← ENNReal.toReal_add (law.apply_ne_top a) (law.apply_ne_top b),hm]
    norm_num
  apply pmf_ext_toReal
  intro who
  by_cases ha : who = a
  · subst who
    simp [distribution_a,hab]
  by_cases hb : who = b
  · subst who
    rw [distribution_b a b hab]
    linarith
  · rw [support who ha hb,distribution_other a b who ha hb]

@[simp] theorem distribution_zero (a b : Role) :
    distribution a b 0 le_rfl (by norm_num) = PMF.pure b := by
  exact mix_zero _ _

@[simp] theorem distribution_one (a b : Role) :
    distribution a b 1 (by norm_num) le_rfl = PMF.pure a := by
  exact mix_one _ _

end KFOL.Rounds.Game.Scalar
