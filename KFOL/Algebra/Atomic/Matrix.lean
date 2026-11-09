module

public import KFOL.Definitions.Atomic

/-! # No rainbow corners force a two-valued or unary matrix -/

@[expose] public section

namespace KFOL.Atomic

universe u v w

private theorem not_three_in_pair {A : Type u} (a b c p q : A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a = p ∨ a = q) (hb : b = p ∨ b = q) (hc : c = p ∨ c = q) : False := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc
  all_goals first
    | exact hab (ha.trans hb.symm)
    | exact hac (ha.trans hc.symm)
    | exact hbc (hb.trans hc.symm)

/-- If a nonconstant row has only two values, all rows have those two values.
Otherwise its three distinct values force every row to agree pointwise.
Only the repeated-output law for three rectangle corners is assumed. -/
theorem matrix_of_nonconstant_row {Row : Type u} {Col : Type v} {Out : Type w}
    (f : Row → Col → Out)
    (corners : ∀ r s x y, Repeat (f r x) (f r y) (f s x))
    (r : Row) (x y : Col) (hxy : f r x ≠ f r y) :
    AtMostTwo (fun z : Row × Col => f z.1 z.2) ∨ ∀ s z, f s z = f r z := by
  classical
  by_cases hz : ∃ z, f r z ≠ f r x ∧ f r z ≠ f r y
  · obtain ⟨z,hzx,hzy⟩ := hz
    apply Or.inr
    intro s t
    by_contra hst
    have pair (a : Col) : f r a = f r t ∨ f r a = f s t := by
      rcases corners r s t a with h | h | h
      · exact Or.inl h.symm
      · exact False.elim (hst h.symm)
      · exact Or.inr h
    exact not_three_in_pair (f r x) (f r y) (f r z) (f r t) (f s t)
      hxy (Ne.symm hzx) (Ne.symm hzy) (pair x) (pair y) (pair z)
  · have rowPair (z : Col) : f r z = f r x ∨ f r z = f r y := by
      by_contra hn
      exact hz ⟨z,fun he => hn (Or.inl he),fun he => hn (Or.inr he)⟩
    apply Or.inl
    refine ⟨f r x,f r y,?_⟩
    rintro ⟨s,z⟩
    rcases rowPair z with hzx | hzy
    · rcases corners r s z y with h | h | h
      · exact False.elim (hxy (hzx.symm.trans h))
      · exact Or.inl (h.symm.trans hzx)
      · exact Or.inr h.symm
    · rcases corners r s z x with h | h | h
      · exact False.elim (hxy (h.symm.trans hzy))
      · exact Or.inr (h.symm.trans hzy)
      · exact Or.inl h.symm

end KFOL.Atomic
