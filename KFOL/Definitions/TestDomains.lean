module

public import KFOL.Definitions.Core

/-! # Input-equation and diagonal-idempotency testing at every finite arity -/

@[expose] public section

namespace KFOL

universe u

/-- A fixed set of allowed input values tests every full-signature equation,
at every finite arity. Intermediate term values need not lie in the domain. -/
def CompleteTestDomain {Role : Type u} (D : Set (WinnerSet Role)) : Prop :=
  ∀ (n : ℕ) (s t : Term Role (Fin n)),
    (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
      s.eval valuation = t.eval valuation) →
    ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation

/-- Completeness for equations in the public reduct, without internal switches. -/
def CompletePublicTestDomain {Role : Type u} (D : Set (WinnerSet Role)) : Prop :=
  ∀ (n : ℕ) (s t : Term Role (Fin n)), s.IsPublic → t.IsPublic →
    (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
      s.eval valuation = t.eval valuation) →
    ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation

/-- Agreement on this domain along the diagonal certifies full idempotency. -/
def CertifiesIdempotency {Role : Type u} (D : Set (WinnerSet Role)) : Prop :=
  ∀ (n : ℕ) (t : Term Role (Fin n)),
    (∀ A ∈ D, t.eval (fun _ => A) = A) →
    ∀ A : WinnerSet Role, t.eval (fun _ => A) = A

end KFOL
