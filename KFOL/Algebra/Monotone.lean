module

public import KFOL.Algebra.Basic

/-! # Monotonicity for ordinary inclusion of winner sets -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

/-- Enlarging both inputs cannot remove a possible winner. -/
theorem choice_mono {Role : Type u} (r : Role) {A B C D : WinnerSet Role}
    (hAC : A.val ⊆ C.val) (hBD : B.val ⊆ D.val) :
    (choice r A B).val ⊆ (choice r C D).val := by
  classical
  by_cases h : C = singleton r ∨ D = singleton r
  · have hl : A = singleton r ∨ B = singleton r := by
      rcases h with hc | hd
      · exact Or.inl (eq_singleton_of_subset A r (by simpa [hc] using hAC))
      · exact Or.inr (eq_singleton_of_subset B r (by simpa [hd] using hBD))
    simp [choice, h, hl]
  · have he : choice r C D = C.union D := by simp [choice, h]
    rw [he]
    exact (choice_subset_union r A B).trans (Set.union_subset_union hAC hBD)

end KFOL.WinnerSet

namespace KFOL.Term

universe u v

/-- Every full-signature term is monotone for ordinary subset inclusion.
The two independently evaluated copies of a variable are enlarged together. -/
theorem eval_mono {Role : Type u} {Var : Type v} (t : Term Role Var)
    {v w : Var → WinnerSet Role} (h : ∀ x, (v x).val ⊆ (w x).val) :
    (t.eval v).val ⊆ (t.eval w).val := by
  induction t with
  | winner => exact Set.Subset.rfl
  | var x => exact h x
  | choice r s t hs ht => exact WinnerSet.choice_mono r hs ht
  | rename p t ht => exact Set.image_mono ht

end KFOL.Term
