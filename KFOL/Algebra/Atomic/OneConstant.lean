module

public import KFOL.Algebra.Atomic.Necessity
public import KFOL.Algebra.SemilatticeTrace

/-! # Core contexts containing one fixed atom -/

@[expose] public section

namespace KFOL

universe u v



namespace Term

variable {Role : Type u} {Var : Type v}

/-- In a core context whose leaves are either the input or one fixed atom,
every input is either always discarded or always retained. -/
theorem IsCore.one_constant_dichotomy {t : Term Role Var} (ht : t.IsCore)
    (active : Var → Bool) (r : Role) :
    (∀ X : WinnerSet Role,
      t.eval (fun x => if active x then X else WinnerSet.singleton r) = WinnerSet.singleton r) ∨
    (∀ X : WinnerSet Role,
      X.val ⊆ (t.eval (fun x => if active x then X else WinnerSet.singleton r)).val) := by
  classical
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x =>
    cases hx : active x
    · exact Or.inl (fun X => by simp [eval,hx])
    · exact Or.inr (fun X => by simp [eval,hx])
  | choice p s t ihs iht =>
    rcases ihs ht.1 with hs | hs <;> rcases iht ht.2 with ht' | ht'
    · exact Or.inl (fun X => by simp only [eval,hs,ht',WinnerSet.choice_idempotent])
    · by_cases hp : p = r
      · subst p
        exact Or.inl (fun X => by simp [eval,hs,WinnerSet.choice])
      · apply Or.inr
        intro X
        rw [eval,hs,WinnerSet.choice_comm]
        exact (ht' X).trans (WinnerSet.subset_choice_of_right_ne p _ _
          (fun h => hp (WinnerSet.singleton_inj.mp h).symm))
    · by_cases hp : p = r
      · subst p
        exact Or.inl (fun X => by simp [eval,ht',WinnerSet.choice])
      · apply Or.inr
        intro X
        rw [eval,ht']
        exact (hs X).trans (WinnerSet.subset_choice_of_right_ne p _ _
          (fun h => hp (WinnerSet.singleton_inj.mp h).symm))
    · exact Or.inr (fun X => WinnerSet.subset_choice_of_subset_both p X _ _ (hs X) (ht' X))

/-- A single distinct atomic input detects global constancy of a one-constant
context, including all ambiguous inputs. -/
theorem IsCore.one_constant_rigidity {t : Term Role Var} (ht : t.IsCore)
    (active : Var → Bool) (r q : Role) (hne : q ≠ r)
    (h : t.eval (fun x => if active x then WinnerSet.singleton q else WinnerSet.singleton r) =
      WinnerSet.singleton r) :
    ∀ X : WinnerSet Role,
      t.eval (fun x => if active x then X else WinnerSet.singleton r) = WinnerSet.singleton r := by
  rcases ht.one_constant_dichotomy active r with hc | he
  · exact hc
  · have hm := he (WinnerSet.singleton q) (show q ∈ ({q} : Set Role) from rfl)
    rw [h] at hm
    exact False.elim (hne hm)

/-- A distinct atomic identity test detects global inflationarity. -/
theorem IsCore.one_constant_inflationary {t : Term Role Var} (ht : t.IsCore)
    (active : Var → Bool) (r q : Role) (hne : q ≠ r)
    (h : t.eval (fun x => if active x then WinnerSet.singleton q else WinnerSet.singleton r) =
      WinnerSet.singleton q) :
    ∀ X : WinnerSet Role,
      X.val ⊆ (t.eval (fun x => if active x then X else WinnerSet.singleton r)).val := by
  rcases ht.one_constant_dichotomy active r with hc | he
  · exact False.elim (hne (WinnerSet.singleton_inj.mp ((hc _).symm.trans h)).symm)
  · exact he

end Term

end KFOL
