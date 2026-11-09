module

import KFOL.Algebra.NoBooleanProduct
import KFOL.Algebra.PublicContexts
import KFOL.Algebra.UnaryReset

namespace KFOL.PublicPureClaimsRegression

universe u v w

/-- Original Boolean-product statement, with arbitrary product index and
arbitrary coordinate choice of meet or join for every owned operation. -/
theorem no_boolean_product {Role : Type u} (three : Fin 3 ↪ Role)
    {Index : Type v} (M : Index → Type w) [∀ i, BooleanAlgebra (M i)]
    (select : Role → Index → Bool) :
    ¬∃ f : WinnerSet Role → ∀ i, M i, Function.Injective f ∧
      (∀ r A B i, f (WinnerSet.choice r A B) i =
        if select r i then f A i ⊔ f B i else f A i ⊓ f B i) := by
  rintro ⟨f,hinj,hf⟩
  exact WinnerSet.no_boolean_product_embedding three M select f hf hinj

/-- The full unique-winner observation assertion, with arbitrary parameters. -/
theorem observations {Role : Type u} {Var : Type v} (t : Term Role Var)
    (ht : t.IsPublic) (active : Var → Bool) (parameters : Var → WinnerSet Role) :
    ((∃ C : WinnerSet Role, ∀ X : WinnerSet Role,
      t.eval (fun x => if active x then X else parameters x) = C) ∨
      (∀ X : WinnerSet Role, X.val ⊆
        (t.eval (fun x => if active x then X else parameters x)).val)) ∧
    (∀ A B : WinnerSet Role, A.Ambiguous → B.Ambiguous → ∀ r,
      (t.eval (fun x => if active x then A else parameters x) = WinnerSet.singleton r) ↔
        (t.eval (fun x => if active x then B else parameters x) = WinnerSet.singleton r)) :=
  ⟨ht.unary_constant_or_extensive active parameters,
    fun A B hA hB r => ht.ambiguous_singleton_observation active parameters A B hA hB r⟩

example {Role : Type u} [Finite Role] (t : Term Role (Fin 1))
    (hext : ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun _ => X)).val) :
    ∃ s : Term Role (Fin 1),
      (∀ r, s.eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r) ∧
      (∀ X : WinnerSet Role, X.Ambiguous → s.eval (fun _ => X) = t.eval (fun _ => X)) ∧
      (∀ X : WinnerSet Role, X.val ⊆ (s.eval (fun _ => X)).val) :=
  t.exists_unary_reset hext

end KFOL.PublicPureClaimsRegression

#print axioms KFOL.WinnerSet.no_boolean_product_embedding
#print axioms KFOL.Term.IsPublic.unary_constant_or_extensive
#print axioms KFOL.Term.IsPublic.ambiguous_singleton_observation
#print axioms KFOL.Term.exists_unary_reset
