module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Fintype.Pi

/-! # Relations of owner-colored Boolean profiles

The operation for an owner is disjunction in its own coordinate group and
conjunction in every other group. The independent theory language consists
of forced bits, implications within one owner, and rainbow conflicts.
-/

@[expose] public section
namespace KFOL.Core.ProfileRelations
universe u v
variable {Index : Type u} {Role : Type v}

/-- All bits in a finite premise are true. -/
def AllTrue (S : Finset Index) (x : Index → Bool) : Prop := ∀ i ∈ S, x i = true

/-- A premise uses at most one coordinate of any owner. -/
def Rainbow (owner : Index → Role) (S : Finset Index) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, owner i = owner j → i = j

/-- The owner's Boolean profile gate, applied independently in every coordinate. -/
def mixedChoice [DecidableEq Role] (owner : Index → Role) (r : Role)
    (x y : Index → Bool) : Index → Bool :=
  fun i => if owner i = r then x i || y i else x i && y i

/-- Closure under all owner-colored Boolean gates. -/
def ChoiceClosed [DecidableEq Role] (owner : Index → Role)
    (R : Set (Index → Bool)) : Prop :=
  ∀ r x y, x ∈ R → y ∈ R → mixedChoice owner r x y ∈ R

/-- An explicit, term-independent theory of colored profile constraints. -/
structure Theory (owner : Index → Role) where
  forced : Finset Index
  implies : Index → Index → Prop
  same_owner : ∀ i j, implies i j → owner i = owner j
  conflicts : Finset (Finset Index)
  rainbow : ∀ S ∈ conflicts, Rainbow owner S

/-- Models have every forced bit, respect the implications, and avoid conflicts. -/
def Theory.Models {owner : Index → Role} (T : Theory owner) (x : Index → Bool) : Prop :=
  (∀ i ∈ T.forced, x i = true) ∧
  (∀ i j, T.implies i j → x i = true → x j = true) ∧
  ∀ S ∈ T.conflicts, ¬AllTrue S x

end KFOL.Core.ProfileRelations
