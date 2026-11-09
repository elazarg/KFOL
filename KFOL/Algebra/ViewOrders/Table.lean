module

public import KFOL.Algebra.Views

/-! # Exact independent player-view tables and their winner-set homomorphism -/

@[expose] public section

namespace KFOL

universe u

open Classical

namespace PlayerView

variable {Role : Type u} {k : Role}

/-- Possible/other singleton tests uniquely determine an observation. -/
theorem eq_of_tests {p q : PlayerView k}
    (hp : p = .possible ↔ q = .possible)
    (ho : ∀ i, p = .other i ↔ q = .other i) : p = q := by
  cases p with
  | possible => exact (hp.mp rfl).symm
  | other i => exact (ho i |>.mp rfl).symm
  | impossible =>
    cases q with
    | possible => have h := hp.mpr rfl; cases h
    | other i => have h := (ho i).mpr rfl; cases h
    | impossible => rfl

theorem choice_self_eq_possible (p q : PlayerView k) :
    choice k p q = .possible ↔ p = .possible ∨ q = .possible := by
  classical
  cases p <;> cases q <;> simp [choice,union]
  split_ifs <;> simp

theorem choice_other_eq_possible (r : Role) (hr : r ≠ k) (p q : PlayerView k) :
    choice r p q = .possible ↔
      (p = .possible ∨ q = .possible) ∧ p ≠ .other ⟨r,hr⟩ ∧ q ≠ .other ⟨r,hr⟩ := by
  classical
  cases p <;> cases q <;> simp [choice,union,hr]
  all_goals split_ifs <;> simp_all

theorem choice_eq_other (r : Role) (p q : PlayerView k) (i : {r : Role // r ≠ k}) :
    choice r p q = .other i ↔
      if r = i.val then p = .other i ∨ q = .other i else p = .other i ∧ q = .other i := by
  classical
  have hi := i.property
  cases p <;> cases q
  all_goals unfold choice union
  all_goals split_ifs <;> simp_all [Subtype.ext_iff]
  all_goals try split_ifs
  all_goals simp_all [Subtype.ext_iff]
  all_goals aesop

end PlayerView

namespace WinnerSet

variable {Role : Type u}

/-- The independent player-view table is the actual quotient operation. -/
theorem view_choice (k r : Role) (A B : WinnerSet Role) :
    view k (choice r A B) = PlayerView.choice r (view k A) (view k B) := by
  apply PlayerView.eq_of_tests
  · by_cases hr : r = k
    · subst r
      rw [PlayerView.choice_self_eq_possible]
      simp only [view_eq_possible_iff,mem_choice_owner]
    · rw [PlayerView.choice_other_eq_possible r hr]
      simp only [ne_eq,view_eq_possible_iff,view_eq_other_iff]
      exact mem_choice_other r k hr A B
  · intro i
    rw [PlayerView.choice_eq_other]
    simp only [view_eq_other_iff]
    by_cases hr : r = i.val
    · subst r
      simp only [ite_true,choice_eq_owner_iff]
    · simp only [hr,ite_false,choice_eq_other_iff _ _ _ hr]

end WinnerSet

end KFOL
