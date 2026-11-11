module

public import KFOL.Definitions.CoreBasis

/-! # Intrinsic conditions on singleton-winning predicates

The predicates below are specified independently of terms. A Boolean input
marks the variables assigned one owner's singleton. A winning coalition is
an input on which that owner's predicate is true.
-/

@[expose] public section

namespace KFOL.Core

universe u v

/-- Monotonicity, unanimity, and a common variable in every selection of
winning coalitions, one per owner. No term representation is assumed. -/
structure AdmissibleProfiles {Role : Type u} {Var : Type v}
    (F : Role → (Var → Bool) → Bool) : Prop where
  mono : ∀ r v w, (∀ x, v x = true → w x = true) → F r v = true → F r w = true
  top : ∀ r, F r (fun _ => true) = true
  common_source : ∀ v : Role → Var → Bool,
    (∀ r, F r (v r) = true) → ∃ x, ∀ r, v r x = true

end KFOL.Core
