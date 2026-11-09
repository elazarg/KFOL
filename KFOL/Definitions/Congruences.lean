module

public import KFOL.Definitions.Views
public import Mathlib.Order.Closure
public import Mathlib.Order.Setoid.Basic
public import Mathlib.Data.Set.Card

/-! # Independent congruences and closure conditions for the winner algebra -/

@[expose] public section

namespace KFOL

universe u

namespace WinnerSet

/-- The full possible-winner value. -/
def full {Role : Type u} [Nonempty Role] : WinnerSet Role := ⟨Set.univ,Set.univ_nonempty⟩

/-- A congruence of the owned-choice algebra. Constants impose no further
condition, and union compatibility is a theorem when three owners exist. -/
structure Congruence (Role : Type u) extends Setoid (WinnerSet Role) where
  choice : ∀ (owner : Role) {A B C D : WinnerSet Role},
    r A C → r B D → r (WinnerSet.choice owner A B) (WinnerSet.choice owner C D)

/-- A congruence of the expansion by every internal role permutation. -/
structure SymmetricCongruence (Role : Type u) extends Congruence Role where
  rename : ∀ (p : Equiv.Perm Role) {A B : WinnerSet Role},
    r A B → r (WinnerSet.rename p A) (WinnerSet.rename p B)

/-- The exact singleton condition imposed on a closure by owned absorption. -/
def AtomClosure {Role : Type u} [Nonempty Role] (c : ClosureOperator (WinnerSet Role)) : Prop :=
  ∀ owner, c (singleton owner) = singleton owner ∨ c (singleton owner) = full

/-- Internal permutation compatibility of a closure, stated independently
of congruence extraction or any classification theorem. -/
def PermutationInvariant {Role : Type u} (c : ClosureOperator (WinnerSet Role)) : Prop :=
  ∀ p A, c (rename p A) = rename p (c A)

/-- The proposed ambiguity threshold fixes small nonempty sets and merges
larger ones with the full winner value. -/
noncomputable def threshold {Role : Type u} [Nonempty Role] (m : ℕ) (A : WinnerSet Role) : WinnerSet Role :=
  if A.val.ncard ≤ m then A else full

/-- The paper's fixed-family condition: full is present, every inhabited
intersection with nonempty result is present, and proper members retain all
their singleton points. -/
def AdmissibleFamily {Role : Type u} [Nonempty Role] (F : Set (WinnerSet Role)) : Prop :=
  full ∈ F ∧
  (∀ G : Set (WinnerSet Role), G.Nonempty → G ⊆ F →
    ∀ hne : (⋂ A ∈ G, A.val).Nonempty, (⟨⋂ A ∈ G, A.val,hne⟩ : WinnerSet Role) ∈ F) ∧
  (∀ A ∈ F, A ≠ full → ∀ owner ∈ A.val, singleton owner ∈ F)

/-- The intersection of all family members containing the input. A point
of the input belongs to every such member, proving nonemptiness directly. -/
def familyClosureValue {Role : Type u} (F : Set (WinnerSet Role)) (A : WinnerSet Role) : WinnerSet Role :=
  ⟨{owner | ∀ B ∈ F, A ≤ B → owner ∈ B.val}, by
    obtain ⟨owner,howner⟩ := A.property
    exact ⟨owner,fun _ _ hAB => hAB howner⟩⟩

end WinnerSet

end KFOL
