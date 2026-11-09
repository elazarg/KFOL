module

public import KFOL.Core.GridTerms

/-! # The padded crossing identity in the complete native algebra -/

@[expose] public section

namespace KFOL.Core

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf

namespace Native

/-- The only obstruction to crossing coverage is simultaneous collapse
of the two arms to their distinct owning atoms. -/
theorem crossing_coverage (a b : Role) (hab : a ≠ b) (u t s : Native Role)
    (noCross : ¬ (t = .atom a ∧ s = .atom b)) :
    join u (join (choice a u t) (choice b u s)) = join (choice a u t) (choice b u s) := by
  apply ext_atoms_upper
  · intro i
    rw [join_eq_atom, join_eq_atom]
    constructor
    · exact And.right
    · intro h
      refine ⟨?_,h⟩
      by_cases hai : a = i
      · have hbi : b ≠ i := by intro hbi; exact hab (hai.trans hbi.symm)
        exact ((choice_eq_atom_other b i hbi u s).mp h.2).1
      · exact ((choice_eq_atom_other a i hai u t).mp h.1).1
  · rw [join_eq_upper]
    constructor
    · rintro (hu | h)
      · rw [join_eq_upper]
        by_cases ht : t = .atom a
        · have hs : s ≠ .atom b := fun hs => noCross ⟨ht,hs⟩
          exact Or.inr ((choice_eq_upper b u s).mpr ⟨Or.inl hu, by rw [hu]; simp, hs⟩)
        · exact Or.inl ((choice_eq_upper a u t).mpr ⟨Or.inl hu, by rw [hu]; simp, ht⟩)
      · exact h
    · exact Or.inr

end Native

namespace Grid

/-- The complete padded identity uses the actual core signature. Its
neutral join is the displayed derived term, not an additional operation. -/
def crossingIdentity {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (j : Fin s) :
    Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)) ×
      Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)) :=
  let right := unionTerm three
    (choiceTerm (three 0) (.var none) (tTerm three i))
    (choiceTerm (three 1) (.var none) (sTerm three j))
  (unionTerm three (.var none) right, right)

/-- Exact validity of the padded crossing equation, for every grid size
and every valuation in the full native algebra. -/
theorem crossing_valid {r s : ℕ} (three : Fin 3 ↪ Role) (i : Fin r) (j : Fin s)
    (v : Option (Variable r s) → Native Role) :
    (crossingIdentity three i j).1.realize v = (crossingIdentity three i j).2.realize v := by
  simp only [crossingIdentity, realize_union_native, realize_choice_native,
    FirstOrder.Language.Term.realize_var]
  exact Native.crossing_coverage (three 0) (three 1) (three.injective.ne (by decide))
    (v none) _ _ (terms_cannot_cross three i j v)

/-- The number of available variables in the displayed equation is
exactly the claimed padded rectangle size. -/
theorem crossing_variable_card (r s : ℕ) : Fintype.card (Option (Variable r s)) = (r+1)*(s+1) := by
  simp only [Fintype.card_option, Variable, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

end Grid

end KFOL.Core
