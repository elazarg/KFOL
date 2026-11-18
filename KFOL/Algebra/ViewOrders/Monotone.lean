module

public import KFOL.Algebra.ViewOrders.Table
public import KFOL.Definitions.PaperAlgebra

/-! # Monotonicity of every gate in the observing player's order -/

@[expose] public section

namespace KFOL

universe u
variable {Role : Type u} {k : Role}

theorem PlayerView.below_self_iff_tests (p q : PlayerView k) :
    Below k p q ↔ (p = .possible → q = .possible) ∧
      ∀ i : {r : Role // r ≠ k}, q = .other i → p = .other i := by
  have foreign (i : {r : Role // r ≠ k}) : i.val ≠ k := i.property
  cases p <;> cases q <;> simp [Below, foreign]

namespace WinnerSet

theorem view_below_iff (k : Role) (A B : WinnerSet Role) :
    PlayerView.Below k (view k A) (view k B) ↔
      (k ∈ A.val → k ∈ B.val) ∧ ∀ r, r ≠ k → B = singleton r → A = singleton r := by
  rw [PlayerView.below_self_iff_tests]
  simp only [view_eq_possible_iff, view_eq_other_iff, Subtype.forall]

/-- Every owned choice preserves the observing player's order in both arguments. -/
theorem view_choice_mono (k r : Role) {A B C D : WinnerSet Role}
    (left : PlayerView.Below k (view k A) (view k C))
    (right : PlayerView.Below k (view k B) (view k D)) :
    PlayerView.Below k (view k (choice r A B)) (view k (choice r C D)) := by
  classical
  rw [view_below_iff] at left right ⊢
  constructor
  · intro wins
    by_cases absorb : C = WinnerSet.singleton r ∨ D = WinnerSet.singleton r
    · have new : WinnerSet.choice r C D = WinnerSet.singleton r :=
        (WinnerSet.choice_eq_owner_iff C D r).mpr absorb
      rw [new]
      by_cases same : r = k
      · subst r; exact Set.mem_singleton k
      · have old : WinnerSet.choice r A B = WinnerSet.singleton r := by
          apply (WinnerSet.choice_eq_owner_iff A B r).mpr
          exact absorb.imp (left.2 r same) (right.2 r same)
        rw [old] at wins
        exact False.elim (same (Set.mem_singleton_iff.mp wins).symm)
    · rw [WinnerSet.choice, ite_eq_right absorb]
      exact (WinnerSet.choice_subset_union r A B wins).imp left.1 right.1
  · intro other different equal
    by_cases owner : r = other
    · subst r
      apply (WinnerSet.choice_eq_owner_iff A B other).mpr
      exact ((WinnerSet.choice_eq_owner_iff C D other).mp equal).imp
        (left.2 other different) (right.2 other different)
    · apply (WinnerSet.choice_eq_other_iff A B r owner).mpr
      have parts := (WinnerSet.choice_eq_other_iff C D r owner).mp equal
      exact ⟨left.2 other different parts.1, right.2 other different parts.2⟩

/-- Replacing an observer-owned choice by either child can only decrease its view. -/
theorem view_below_choice_self (k : Role) {A B C : WinnerSet Role}
    (h : PlayerView.Below k (view k A) (view k B) ∨
      PlayerView.Below k (view k A) (view k C)) :
    PlayerView.Below k (view k A) (view k (choice k B C)) := by
  simp only [view_below_iff] at h ⊢
  constructor
  · intro wins
    apply (mem_choice_owner k B C).mpr
    exact h.imp (fun left => left.1 wins) (fun right => right.1 wins)
  · intro r hr absorbed
    have both := (choice_eq_other_iff B C k hr.symm).mp absorbed
    exact h.elim (fun left => left.2 r hr both.1) (fun right => right.2 r hr both.2)

end WinnerSet
end KFOL
