module

public import KFOL.Definitions.Public
public import Mathlib.Data.Fintype.Basic

/-! # Direct input conditions for one-budget profile realization

The predicates inspect only the prescribed Boolean profiles, winner inputs,
and one upper or exact output bound, optionally with a required winner.
They quantify neither terms nor auxiliary relations.
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

/-- The positions at which an input is exactly the given owner atom. -/
noncomputable def atomicBits (r : Role) (values : Var → WinnerSet Role) : Var → Bool := by
  classical
  exact fun j => decide (values j = WinnerSet.singleton r)

/-- Rainbow feasibility, a whole input carrying the queried winner, and
foreign-owner separation from the corresponding atomic inputs. -/
def QuerySafe (J : Finset Role) (A : Role → Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) (k : Role) : Prop :=
  RainbowSafe J A values U ∧
  (∃ j, k ∈ (values j).val ∧ (values j).val ⊆ U) ∧
  ∀ r ∈ J, r ≠ k → PairSafe r (A r) (atomicBits r values) values U

/-- Top bits, ownerwise coalition separation, and full-owner rainbow feasibility. -/
def ProfileCondition [Fintype Role] (Φ : Role → (Var → Bool) → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) : Prop :=
  (∀ r, Φ r (fun _ => true) = true) ∧
  (∀ r A B, Φ r A = true → Φ r B = false → PairSafe r A B values U) ∧
  ∀ A : Role → Var → Bool, (∀ r, Φ r (A r) = true) →
    RainbowSafe Finset.univ A values U

/-- A full profile tuple and one exact winner value: bounded feasibility,
atomic compatibility, and a whole-input source for every requested winner. -/
def OnePointCondition [Fintype Role] (Φ : Role → (Var → Bool) → Bool)
    (values : Var → WinnerSet Role) (target : WinnerSet Role) : Prop :=
  ProfileCondition Φ values target.val ∧
  (∀ r, Φ r (atomicBits r values) = true ↔ target = WinnerSet.singleton r) ∧
  ∀ k ∈ target.val, ∃ j, k ∈ (values j).val ∧ (values j).val ⊆ target.val

end KFOL.Core.ProfileBounds
