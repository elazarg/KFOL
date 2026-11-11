module

public import KFOL.Definitions.CoreFunctions
public import Mathlib.Data.Fintype.Card

/-! # Relational tests and coherent patches

An n-point interpolant is equivalent to preservation of every invariant
n-ary relation. An (n+1)-term family with at most one exception at each
valuation supplies all n-point interpolants.
-/

@[expose] public section

namespace KFOL.Core

private theorem eval_mem {Role Var : Type*} (n : ℕ) (t : Term Role Var) (ht : t.IsCore)
    (R : Set (Fin n → WinnerSet Role)) (hR : InvariantRelation n R)
    (v : Fin n → Var → WinnerSet Role) (h : ∀ j, (fun i => v i j) ∈ R) :
    (fun i => t.eval (v i)) ∈ R := by
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var j => exact h j
  | choice r s t ihs iht => exact hR r _ _ (ihs ht.1) (iht ht.2)

theorem locallyInterpolable_iff_preservesInvariants {Role Var : Type*} (n : ℕ)
    (f : (Var → WinnerSet Role) → WinnerSet Role) : LocallyInterpolable n f ↔ PreservesInvariants n f := by
  constructor
  · intro hf R hR v h
    obtain ⟨t, ht, he⟩ := hf v
    have hh := eval_mem n t ht R hR v h
    simpa only [he] using hh
  · intro hf v
    let R : Set (Fin n → WinnerSet Role) :=
      {p | ∃ t : Term Role Var, t.IsCore ∧ ∀ i, t.eval (v i) = p i}
    exact hf R (by
      rintro r x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
      exact ⟨.choice r s t, ⟨hs, ht⟩, by intro i; simp [Term.eval, hx, hy]⟩)
      v (fun j => ⟨.var j, trivial, fun _ => rfl⟩)

theorem locallyInterpolable_of_patches {Role Var : Type*} (n : ℕ)
    (terms : Fin (n+1) → Term Role Var) (hcore : ∀ i, (terms i).IsCore)
    (f : (Var → WinnerSet Role) → WinnerSet Role)
    (h : ∀ v, ∃ bad : Fin (n+1), ∀ i, i ≠ bad → (terms i).eval v = f v) : LocallyInterpolable n f := by
  classical
  intro v
  choose bad hb using fun j => h (v j)
  have hn : ¬ Function.Surjective bad := by
    intro hs
    have hh := Fintype.card_le_of_surjective bad hs
    simp only [Fintype.card_fin] at hh
    omega
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, bad j ≠ i := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  exact ⟨terms i, hcore i, fun j => hb j i (Ne.symm (hi j))⟩

end KFOL.Core
