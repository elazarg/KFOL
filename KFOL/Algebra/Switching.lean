module

public import KFOL.Algebra.Views

/-! # Full one-player observation under internal role switching -/

@[expose] public section

namespace KFOL.Term

universe u

/-- With role switches, one player's polynomial contextual equivalence is
exact equality, even with arbitrary winner-set ground parameters. -/
theorem full_polynomial_contextual_iff_eq {Role : Type u} (k : Role) (A B : WinnerSet Role) :
    (∀ (n : ℕ) (t : Term Role (Option (Fin n))) (parameters : Fin n → WinnerSet Role),
      (k ∈ (t.eval (fun x => x.elim A parameters)).val ↔
        k ∈ (t.eval (fun x => x.elim B parameters)).val)) ↔ A = B := by
  classical
  constructor
  · intro h
    apply Subtype.ext
    ext j
    have hm (X : WinnerSet Role) :
        k ∈ (Equiv.swap j k) '' X.val ↔ j ∈ X.val := by
      constructor
      · rintro ⟨a, ha, he⟩
        have haj : a = j := (Equiv.swap j k).injective
          (he.trans (Equiv.swap_apply_left j k).symm)
        exact haj ▸ ha
      · intro hj
        exact ⟨j, hj, Equiv.swap_apply_left j k⟩
    have ht := h 0 (.rename (Equiv.swap j k) (.var none)) Fin.elim0
    change (k ∈ (Equiv.swap j k) '' A.val ↔ k ∈ (Equiv.swap j k) '' B.val) at ht
    exact (hm A).symm.trans (ht.trans (hm B))
  · rintro rfl n t parameters
    exact Iff.rfl

end KFOL.Term
