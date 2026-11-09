module

public import KFOL.Algebra.Basic
public import KFOL.Definitions.Core

/-! # Public unary contexts and singleton/membership observations -/

@[expose] public section

namespace KFOL.Term

universe u v

variable {Role : Type u} {Var : Type v}

/-- A public unary context with arbitrary fixed winner-set parameters is
constant or extensive. Every active input occurrence receives the same
independent input value. No normal form or finite-role assumption is needed. -/
theorem IsPublic.unary_constant_or_extensive {t : Term Role Var} (ht : t.IsPublic)
    (active : Var → Bool) (fixed : Var → WinnerSet Role) :
    (∃ A : WinnerSet Role, ∀ X : WinnerSet Role,
      t.eval (fun x => if active x then X else fixed x) = A) ∨
    (∀ X : WinnerSet Role,
      X.val ⊆ (t.eval (fun x => if active x then X else fixed x)).val) := by
  classical
  induction t with
  | winner r => exact Or.inl ⟨WinnerSet.singleton r,fun _ => rfl⟩
  | rename => exact False.elim ht
  | var x =>
    cases hx : active x
    · exact Or.inl ⟨fixed x,fun X => by simp [eval,hx]⟩
    · exact Or.inr (fun X => by simp [eval,hx])
  | choice r s t ihs iht =>
    rcases ihs ht.1 with ⟨A,hA⟩ | hs <;> rcases iht ht.2 with ⟨B,hB⟩ | ht'
    · exact Or.inl ⟨WinnerSet.choice r A B,fun X => by simp only [eval,hA,hB]⟩
    · by_cases howner : A = WinnerSet.singleton r
      · exact Or.inl ⟨WinnerSet.singleton r,fun X => by simp [eval,hA,howner,WinnerSet.choice]⟩
      · exact Or.inr (fun X => by
          rw [eval,hA,WinnerSet.choice_comm]
          exact (ht' X).trans (WinnerSet.subset_choice_of_right_ne _ _ _ howner))
    · by_cases howner : B = WinnerSet.singleton r
      · exact Or.inl ⟨WinnerSet.singleton r,fun X => by simp [eval,hB,howner,WinnerSet.choice]⟩
      · exact Or.inr (fun X => by
          rw [eval,hB]
          exact (hs X).trans (WinnerSet.subset_choice_of_right_ne _ _ _ howner))
    · exact Or.inr (fun X => WinnerSet.subset_choice_of_subset_both _ _ _ _ (hs X) (ht' X))

/-- Singleton-only observation cannot distinguish any two ambiguous inputs,
even with arbitrary fixed parameters in the public unary context. -/
theorem IsPublic.ambiguous_singleton_observation {t : Term Role Var} (ht : t.IsPublic)
    (active : Var → Bool) (fixed : Var → WinnerSet Role)
    (A B : WinnerSet Role) (hA : A.Ambiguous) (hB : B.Ambiguous) (r : Role) :
    (t.eval (fun x => if active x then A else fixed x) = WinnerSet.singleton r) ↔
      (t.eval (fun x => if active x then B else fixed x) = WinnerSet.singleton r) := by
  rcases ht.unary_constant_or_extensive active fixed with ⟨C,hC⟩ | hsub
  · rw [hC A,hC B]
  · have hnA : t.eval (fun x => if active x then A else fixed x) ≠ WinnerSet.singleton r := by
      intro he
      apply hA r
      apply WinnerSet.eq_singleton_of_subset A r
      simpa only [he,WinnerSet.val_singleton] using hsub A
    have hnB : t.eval (fun x => if active x then B else fixed x) ≠ WinnerSet.singleton r := by
      intro he
      apply hB r
      apply WinnerSet.eq_singleton_of_subset B r
      simpa only [he,WinnerSet.val_singleton] using hsub B
    exact ⟨fun h => False.elim (hnA h),fun h => False.elim (hnB h)⟩

end KFOL.Term

namespace KFOL.WinnerSet

universe u

/-- The family of all membership observations distinguishes every difference
of value already in the identity context. -/
theorem exists_membership_difference {Role : Type u} (A B : WinnerSet Role) (hne : A ≠ B) :
    ∃ r : Role, ¬(r ∈ A.val ↔ r ∈ B.val) := by
  classical
  by_contra hno
  apply hne
  apply Subtype.ext
  apply Set.ext
  intro r
  by_contra hr
  exact hno ⟨r,hr⟩

end KFOL.WinnerSet
