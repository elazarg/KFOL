module

public import KFOL.Definitions.Public

/-! # Zero extension and the regular representation of a powerset product

The fresh point observes the represented set itself. Ordinary rows use right
multiplication, so the construction also applies to noncommutative products.
-/

@[expose] public section
namespace KFOL
universe u

namespace WinnerSet

open Classical in
/-- Extend owned choice to all subsets by adjoining an annihilating zero.
This is an algebraic extension, not the value of an empty game. -/
noncomputable def choiceWithZero {Role : Type u} (owner : Role) (A B : Set Role) : Set Role :=
  if ha : A.Nonempty then
    if hb : B.Nonempty then (choice owner ⟨A, ha⟩ ⟨B, hb⟩).val else ∅
  else ∅

end WinnerSet

namespace Relational

/-- The right regular relation, with a fresh point that makes it faithful.
There are no incoming edges to the fresh point. -/
def regularRelation {α : Type u} (mul : Set α → Set α → Set α) (A : Set α) :
    Option α → Option α → Prop := fun x y =>
  match y with
  | none => False
  | some y => match x with
    | none => y ∈ A
    | some x => y ∈ mul {x} A

end Relational
end KFOL
