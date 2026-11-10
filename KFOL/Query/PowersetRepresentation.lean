module

public import KFOL.Definitions.Relational
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Logic.Relation

/-! # A relational Cayley theorem for finite powersets

Only associativity, preservation of binary unions, and annihilation of the
empty set are required. Neither commutativity nor meet preservation is used.
-/

@[expose] public section
namespace KFOL.Relational
universe u v
variable {α : Type u} {β : Type v}

theorem regularRelation_injective (mul : Set α → Set α → Set α) :
    Function.Injective (regularRelation mul) := by
  intro A B h
  ext a
  exact Iff.of_eq (congrFun (congrFun h none) (some a))

/-- Atomic expansion of a finitely additive map on a finite subset. -/
theorem mem_finite_additive (f : Set α → Set β) (empty : f ∅ = ∅)
    (add : ∀ A B, f (A ∪ B) = f A ∪ f B) (A : Set α) (finite : A.Finite) (b : β) :
    b ∈ f A ↔ ∃ a ∈ A, b ∈ f {a} := by
  induction A, finite using Set.Finite.induction_on with
  | empty => simp [empty]
  | @insert a A _ _ ih =>
    rw [Set.insert_eq, add]
    simp only [Set.mem_union, ih, Set.mem_singleton_iff, exists_eq_left,
      or_and_right, exists_or]

/-- The regular construction needs atomic expansion only in the first argument.
This form also applies to infinite powersets with completely additive products. -/
theorem regular_representation_of_columns (mul : Set α → Set α → Set α)
    (assoc : ∀ A B C, mul (mul A B) C = mul A (mul B C))
    (columns : ∀ A B k, k ∈ mul A B ↔ ∃ a ∈ A, k ∈ mul {a} B)
    (add : ∀ A B C, mul A (B ∪ C) = mul A B ∪ mul A C)
    (zero : ∀ A, mul A ∅ = ∅) :
    Function.Injective (regularRelation mul) ∧
    regularRelation mul ∅ = (fun _ _ => False) ∧
    (∀ A B, regularRelation mul (A ∪ B) = fun x y =>
      regularRelation mul A x y ∨ regularRelation mul B x y) ∧
    ∀ A B, regularRelation mul (mul A B) =
      Relation.Comp (regularRelation mul A) (regularRelation mul B) := by
  refine ⟨regularRelation_injective mul, ?_, ?_, ?_⟩
  · funext x y
    cases y <;> cases x <;> simp [regularRelation, zero]
  · intro A B
    funext x y
    cases y <;> cases x <;> simp [regularRelation, add]
  · intro A B
    funext x y
    apply propext
    cases y with
    | none =>
      change False ↔ ∃ middle, regularRelation mul A x middle ∧ False
      simp
    | some k =>
      have middle :
          Relation.Comp (regularRelation mul A) (regularRelation mul B) x (some k) ↔
          ∃ a, regularRelation mul A x (some a) ∧ k ∈ mul {a} B := by
        constructor
        · rintro ⟨mid, ha, hb⟩
          cases mid with
          | none => cases ha
          | some a => exact ⟨a, ha, hb⟩
        · rintro ⟨a, ha, hb⟩; exact ⟨some a, ha, hb⟩
      rw [middle]
      cases x with
      | none => exact columns A B k
      | some x =>
        change k ∈ mul {x} (mul A B) ↔ ∃ a ∈ mul {x} A, k ∈ mul {a} B
        rw [← assoc]
        exact columns (mul {x} A) B k

/-- Every finite powerset semigroup with a union-preserving multiplication and
an annihilating zero embeds into relations on one more point. -/
theorem finite_powerset_representation [Finite α] (mul : Set α → Set α → Set α)
    (assoc : ∀ A B C, mul (mul A B) C = mul A (mul B C))
    (add_left : ∀ A B C, mul (A ∪ B) C = mul A C ∪ mul B C)
    (add_right : ∀ A B C, mul A (B ∪ C) = mul A B ∪ mul A C)
    (zero_left : ∀ A, mul ∅ A = ∅) (zero_right : ∀ A, mul A ∅ = ∅) :
    Function.Injective (regularRelation mul) ∧
    regularRelation mul ∅ = (fun _ _ => False) ∧
    (∀ A B, regularRelation mul (A ∪ B) = fun x y =>
      regularRelation mul A x y ∨ regularRelation mul B x y) ∧
    ∀ A B, regularRelation mul (mul A B) =
      Relation.Comp (regularRelation mul A) (regularRelation mul B) := by
  apply regular_representation_of_columns mul assoc
  · intro A B k
    exact mem_finite_additive (fun A => mul A B) (zero_left B)
      (fun A C => add_left A C B) A A.toFinite k
  · exact add_right
  · exact zero_right

end KFOL.Relational
