module

public import KFOL.Rounds.Scalar.Reciprocal

/-! # The exact possible winners of actual reciprocal games -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Scalar

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u}

/-- A genuinely interior two-winner distribution has exactly that pair as its
possible winners, expressed through actual nonzero PMF coordinates. -/
theorem possibleWinners_distribution (a b : Role) (hab : a ≠ b) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    possibleWinners {distribution a b x hx0.le hx1.le} = {a,b} := by
  classical
  ext who
  constructor
  · rintro ⟨law,hlaw,hwho⟩
    have he : law = distribution a b x hx0.le hx1.le := hlaw
    rw [he] at hwho
    by_cases ha : who = a
    · exact Or.inl ha
    by_cases hb : who = b
    · exact Or.inr hb
    · exact (hwho (distribution_other a b who ha hb _ _ _)).elim
  · intro hwho
    refine ⟨distribution a b x hx0.le hx1.le,rfl,?_⟩
    rcases hwho with ha | hb
    · rw [ha]
      intro he
      have hr := distribution_a a b hab x hx0.le hx1.le
      rw [he,ENNReal.toReal_zero] at hr
      linarith
    · rw [hb]
      intro he
      have hr := distribution_b a b hab x hx0.le hx1.le
      rw [he,ENNReal.toReal_zero] at hr
      linarith

/-- Every actual input `Gₙ=Lₙ₊₁` of the threshold construction has exactly the
same pair of possible winners. -/
theorem possibleWinners_reciprocalDistribution_succ (a b : Role) (hab : a ≠ b) (n : ℕ) :
    possibleWinners {reciprocalDistribution a b (n+1)} = {a,b} := by
  have h0 : (0:ℝ) < 1/(((n+1:ℕ):ℝ)+1) := by positivity
  have h1 : 1/(((n+1:ℕ):ℝ)+1) < 1 := by
    apply (div_lt_one (by positivity : (0:ℝ) < ((n+1:ℕ):ℝ)+1)).2
    exact_mod_cast (show 1 < (n+1)+1 by omega)
  exact possibleWinners_distribution a b hab _ h0 h1

variable [DecidableEq Role] [Fintype Role]

/-- The statement concerns the actual sequential-equilibrium value set of the
actual finite reciprocal game, rather than an arithmetic stand-in. -/
theorem possibleWinners_reciprocal_succ (a b : Role) (hab : a ≠ b) (n : ℕ)
    (order : ExplicitOrder Role) :
    possibleWinners ((reciprocal a b (n+1)).sequentialValues order) = {a,b} := by
  rw [sequentialValues_reciprocal a b hab]
  exact possibleWinners_reciprocalDistribution_succ a b hab n

end KFOL.Rounds.Game.Scalar
