module

public import KFOL.Definitions.Public
public import Mathlib.Data.Fintype.Basic

/-! # Direct input conditions for one-budget profile realization

The predicates inspect only the prescribed Boolean profiles, winner inputs,
and one upper bound. They quantify neither terms nor auxiliary relations.
-/

@[expose] public section
namespace KFOL.Core.ProfileBounds
universe u v
variable {Role : Type u} {Var : Type v}

/-- An eligible projection or an allowed owner atom separates two coalitions. -/
def PairSafe (r : Role) (A B : Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) : Prop :=
  (∃ j, A j = true ∧ B j = false ∧ (values j).val ⊆ U) ∨
  (r ∈ U ∧ (∃ l, A l = true ∧ B l = false) ∧
    ∃ j, values j = WinnerSet.singleton r ∧ B j = false) ∨
  ((∃ l, A l = true ∧ B l = false) ∧
    ∃ s ∈ U, s ≠ r ∧ ∃ j, A j = true ∧ values j = WinnerSet.singleton s)

/-- The explicit implication preorder on coalitions for a given winner budget. -/
def CoalitionLE (values : Var → WinnerSet Role) (U : Set Role) (r : Role)
    (A B : Var → Bool) : Prop := ¬PairSafe r A B values U

/-- A common eligible input or an allowed atom supports a rainbow of coalitions. -/
def RainbowSafe (J : Finset Role) (A : Role → Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) : Prop :=
  (∃ j, ∀ r ∈ J, A r j = true) ∧
  ((∃ j, (∀ r ∈ J, A r j = true) ∧ (values j).val ⊆ U) ∨
    ∃ s ∈ J, s ∈ U ∧ ∃ j, values j = WinnerSet.singleton s ∧
      ∀ r ∈ J, r ≠ s → A r j = true)

/-- Top bits, ownerwise coalition separation, and full-owner rainbow feasibility. -/
def ProfileCondition [Fintype Role] (Φ : Role → (Var → Bool) → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) : Prop :=
  (∀ r, Φ r (fun _ => true) = true) ∧
  (∀ r A B, Φ r A = true → Φ r B = false → PairSafe r A B values U) ∧
  ∀ A : Role → Var → Bool, (∀ r, Φ r (A r) = true) →
    RainbowSafe Finset.univ A values U

end KFOL.Core.ProfileBounds
