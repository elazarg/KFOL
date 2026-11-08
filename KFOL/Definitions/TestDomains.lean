module

public import KFOL.Definitions.Public

/-! # Fixed input domains for equations at every finite arity -/

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

end KFOL
