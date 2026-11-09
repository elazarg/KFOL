module

public import KFOL.Rounds.Scalar.Rational

/-! # Every rational probability is synthesized by actual scalar components -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.ScalarTerm

/-- Exact rational synthesis by decreasing the denominator, without any
assumption that the input fraction is reduced. -/
theorem synthesize_fraction (p q : ℕ) (hq : 0 < q) (hpq : p ≤ q) :
    ∃ term : ScalarTerm, term.UnaryGenerated ∧ term.rate = (p:ℚ)/q := by
  induction q using Nat.strongRecOn generalizing p with
  | ind q ih =>
    by_cases hp0 : p = 0
    · subst p
      exact ⟨.zero,.zero,by simp [rate]⟩
    by_cases hpqeq : p = q
    · subst p
      exact ⟨.one,.one,by simp [rate,Nat.ne_of_gt hq]⟩
    have hpos : 0 < p := by omega
    have hlt : p < q := by omega
    have hdiff : 0 < q-p := by omega
    have hqQ : (q:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
    have hpQ : (p:ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hpos
    have hdQ : ((q-p:ℕ):ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hdiff
    have hd : ((q-p:ℕ):ℚ) = (q:ℚ)-p := Nat.cast_sub hpq
    by_cases hsmall : p ≤ q-p
    · obtain ⟨term,hterm,hrate⟩ := ih (q-p) (by omega) p hdiff hsmall
      refine ⟨.diagonal term .one,.step hterm,?_⟩
      simp only [rate,hrate,mul_one]
      rw [hd]
      have hd' : (q:ℚ)-p ≠ 0 := hd ▸ hdQ
      field_simp [hqQ,hd']
      ring
    · obtain ⟨term,hterm,hrate⟩ := ih p hlt (q-p) hpos (by omega)
      refine ⟨.complement (.diagonal term .one),.complement (.step hterm),?_⟩
      simp only [rate,hrate,mul_one]
      rw [hd]
      field_simp [hqQ,hpQ]
      ring

/-- Every rational in the unit interval is realized by the small constructor
set; all generated scalar terms have valid rational values by `rate_valid`. -/
theorem synthesize (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ term : ScalarTerm, term.UnaryGenerated ∧ term.rate = q := by
  have hnum : (q.num.natAbs:ℤ) = q.num := by
    rw [Int.natCast_natAbs,abs_of_nonneg (Rat.num_nonneg.mpr hq0)]
  have hnumQ : (q.num.natAbs:ℚ) = (q.num:ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnum
  have hfrac : (q.num.natAbs:ℚ)/(q.den:ℚ) = q := by
    rw [hnumQ,Rat.num_div_den]
  have hden : (0:ℚ) < q.den := by exact_mod_cast q.den_pos
  have hleQ : (q.num.natAbs:ℚ) ≤ q.den :=
    (div_le_one hden).mp (hfrac.symm ▸ hq1)
  have hle : q.num.natAbs ≤ q.den := by exact_mod_cast hleQ
  obtain ⟨term,hterm,hrate⟩ := synthesize_fraction q.num.natAbs q.den q.den_pos hle
  exact ⟨term,hterm,hrate.trans hfrac⟩

/-- The exact generated scalar range is the rational unit interval. -/
theorem range_rate : Set.range rate = Set.Icc 0 1 := by
  ext q
  constructor
  · rintro ⟨term,rfl⟩
    exact rate_valid term
  · intro hq
    obtain ⟨term,_,hrate⟩ := synthesize q hq.1 hq.2
    exact ⟨term,hrate⟩

/-- Leaves, complement and the one-occurrence step already attain the whole
range; general diagonal/public extrema add no new scalar values. -/
theorem unaryGenerated_range :
    {q : ℚ | ∃ term : ScalarTerm, term.UnaryGenerated ∧ term.rate = q} = Set.Icc 0 1 := by
  ext q
  constructor
  · rintro ⟨term,_,rfl⟩
    exact rate_valid term
  · exact fun hq => synthesize q hq.1 hq.2

end KFOL.Rounds.Game.ScalarTerm

namespace KFOL.Rounds.Game.Scalar

open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Rational synthesis is connected to the actual finite game syntax and its
independently defined canonical serial-SE distributions. -/
theorem exists_rational_game (a b : Role) (hab : a ≠ b) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (order : ExplicitOrder Role) :
    ∃ term : ScalarTerm, term.UnaryGenerated ∧
      (term.game a b).sequentialValues order =
        {distribution a b (q:ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq1)} := by
  obtain ⟨term,hterm,hrate⟩ := ScalarTerm.synthesize q hq0 hq1
  refine ⟨term,hterm,?_⟩
  simpa only [hrate] using sequentialValues_scalarTerm term a b hab order

end KFOL.Rounds.Game.Scalar
