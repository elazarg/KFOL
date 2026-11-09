module

public import KFOL.Algebra.TestDomains
public import Mathlib.Data.Fintype.EquivFin

/-! # An extensive unary term can be reset on atoms without changing ambiguity -/

@[expose] public section

namespace KFOL.Term

universe u v

variable {Role : Type u} {Var : Type v}

/-- A common input lower bound survives every step of the actual suppression fold. -/
theorem subset_eval_suppress (roles : List Role) (acc base : Term Role Var)
    (v : Var → WinnerSet Role) (X : WinnerSet Role)
    (ha : X.val ⊆ (acc.eval v).val) (hb : X.val ⊆ (base.eval v).val) :
    X.val ⊆ ((suppress roles acc base).eval v).val := by
  induction roles with
  | nil => exact ha
  | cons r rest ih => exact WinnerSet.subset_choice_of_subset_both r X _ _ ih hb

/-- The concrete fold fixes each covered atom, agrees with the extensive
term at every ambiguous input, and remains extensive throughout. -/
theorem unary_reset_fold (roles : List Role) (covers : ∀ r, r ∈ roles)
    (t : Term Role Var) (i : Var)
    (hext : ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun _ => X)).val) :
    (∀ r, (suppress roles t (.var i)).eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r) ∧
    (∀ X : WinnerSet Role, X.Ambiguous →
      (suppress roles t (.var i)).eval (fun _ => X) = t.eval (fun _ => X)) ∧
    (∀ X : WinnerSet Role, X.val ⊆ ((suppress roles t (.var i)).eval (fun _ => X)).val) := by
  refine ⟨?_,?_,?_⟩
  · intro r
    exact eval_suppress_atom roles t (.var i) _ r (covers r) rfl
  · intro X hX
    exact eval_suppress_ambiguous roles t (.var i) _ hX (hext X)
  · intro X
    exact subset_eval_suppress roles t (.var i) _ X (hext X) Set.Subset.rfl

/-- Every extensive actual unary term over a finite role type has a reset
term fixing all atoms and retaining exactly its ambiguous-input behavior. -/
theorem exists_unary_reset [Finite Role] (t : Term Role (Fin 1))
    (hext : ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun _ => X)).val) :
    ∃ s : Term Role (Fin 1),
      (∀ r, s.eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r) ∧
      (∀ X : WinnerSet Role, X.Ambiguous → s.eval (fun _ => X) = t.eval (fun _ => X)) ∧
      (∀ X : WinnerSet Role, X.val ⊆ (s.eval (fun _ => X)).val) := by
  classical
  let := Fintype.ofFinite Role
  exact ⟨suppress Finset.univ.toList t (.var 0),unary_reset_fold _ (by simp) t 0 hext⟩

end KFOL.Term
