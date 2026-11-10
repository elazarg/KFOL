module

public import KFOL.Query.PowersetRepresentation
public import KFOL.Query.Relations

/-! # Owned choice with an annihilating empty set

The standard powerset Boolean lattice and this product form a distributive
lattice-ordered semigroup. The regular representation is proved directly,
including for infinite role types, by atomic expansion.
-/

@[expose] public section
namespace KFOL.WinnerSet
universe u
variable {Role : Type u} (owner : Role)

@[simp] theorem choiceWithZero_empty_left (A : Set Role) :
    choiceWithZero owner ∅ A = ∅ := by
  simp [choiceWithZero]

@[simp] theorem choiceWithZero_empty_right (A : Set Role) :
    choiceWithZero owner A ∅ = ∅ := by
  classical
  simp [choiceWithZero]

@[simp] theorem choiceWithZero_val (A B : WinnerSet Role) :
    choiceWithZero owner A.val B.val = (choice owner A B).val := by
  simp [choiceWithZero, A.property, B.property]

theorem choiceWithZero_comm (A B : Set Role) :
    choiceWithZero owner A B = choiceWithZero owner B A := by
  rcases Set.eq_empty_or_nonempty A with rfl | ha
  · simp
  rcases Set.eq_empty_or_nonempty B with rfl | hb
  · simp
  simpa only [choiceWithZero, dite_eq_left ha, dite_eq_left hb] using
    congrArg Subtype.val (choice_comm ⟨A, ha⟩ ⟨B, hb⟩ owner)

theorem choiceWithZero_assoc (A B C : Set Role) :
    choiceWithZero owner (choiceWithZero owner A B) C =
      choiceWithZero owner A (choiceWithZero owner B C) := by
  rcases Set.eq_empty_or_nonempty A with rfl | ha
  · simp
  rcases Set.eq_empty_or_nonempty B with rfl | hb
  · simp
  rcases Set.eq_empty_or_nonempty C with rfl | hc
  · simp
  let a : WinnerSet Role := ⟨A, ha⟩
  let b : WinnerSet Role := ⟨B, hb⟩
  let c : WinnerSet Role := ⟨C, hc⟩
  change choiceWithZero owner (choiceWithZero owner a.val b.val) c.val =
    choiceWithZero owner a.val (choiceWithZero owner b.val c.val)
  simp only [choiceWithZero_val]
  exact congrArg Subtype.val (choice_assoc a b owner c)

theorem choiceWithZero_self (A : Set Role) : choiceWithZero owner A A = A := by
  rcases Set.eq_empty_or_nonempty A with rfl | ha
  · simp
  simpa only [choiceWithZero, dite_eq_left ha] using
    congrArg Subtype.val (choice_self ⟨A, ha⟩ owner)

theorem choiceWithZero_union_right (A B C : Set Role) :
    choiceWithZero owner A (B ∪ C) =
      choiceWithZero owner A B ∪ choiceWithZero owner A C := by
  rcases Set.eq_empty_or_nonempty A with rfl | ha
  · simp
  rcases Set.eq_empty_or_nonempty B with rfl | hb
  · simp
  rcases Set.eq_empty_or_nonempty C with rfl | hc
  · simp
  let a : WinnerSet Role := ⟨A, ha⟩
  let b : WinnerSet Role := ⟨B, hb⟩
  let c : WinnerSet Role := ⟨C, hc⟩
  change choiceWithZero owner a.val (b.union c).val =
    choiceWithZero owner a.val b.val ∪ choiceWithZero owner a.val c.val
  simp only [choiceWithZero_val]
  exact congrArg Subtype.val (Dissemilattice.winner_mul_add owner a b c)

theorem choiceWithZero_union_left (A B C : Set Role) :
    choiceWithZero owner (A ∪ B) C =
      choiceWithZero owner A C ∪ choiceWithZero owner B C := by
  rw [choiceWithZero_comm owner (A ∪ B), choiceWithZero_union_right]
  rw [choiceWithZero_comm owner C A, choiceWithZero_comm owner C B]

theorem choiceWithZero_columns (A B : Set Role) (k : Role) :
    k ∈ choiceWithZero owner A B ↔ ∃ a ∈ A, k ∈ choiceWithZero owner {a} B := by
  rcases Set.eq_empty_or_nonempty A with rfl | ha
  · simp
  rcases Set.eq_empty_or_nonempty B with rfl | hb
  · simp
  let a : WinnerSet Role := ⟨A, ha⟩
  let b : WinnerSet Role := ⟨B, hb⟩
  change k ∈ choiceWithZero owner a.val b.val ↔
    ∃ x ∈ a.val, k ∈ choiceWithZero owner (singleton x).val b.val
  simp only [choiceWithZero_val]
  rw [choice_comm a b, Query.mem_choice_columns]
  simp only [choice_comm b]

/-- All product laws needed for the Boolean lattice expansion; no finiteness
hypothesis is imposed on the role set. -/
theorem choiceWithZero_laws :
    (∀ A B : WinnerSet Role, choiceWithZero owner A.val B.val = (choice owner A B).val) ∧
    (∀ A B C, choiceWithZero owner (choiceWithZero owner A B) C =
      choiceWithZero owner A (choiceWithZero owner B C)) ∧
    (∀ A B, choiceWithZero owner A B = choiceWithZero owner B A) ∧
    (∀ A, choiceWithZero owner A A = A) ∧
    (∀ A B C, choiceWithZero owner (A ∪ B) C =
      choiceWithZero owner A C ∪ choiceWithZero owner B C) ∧
    (∀ A B C, choiceWithZero owner A (B ∪ C) =
      choiceWithZero owner A B ∪ choiceWithZero owner A C) ∧
    (∀ A, choiceWithZero owner ∅ A = ∅) ∧
    ∀ A, choiceWithZero owner A ∅ = ∅ :=
  ⟨choiceWithZero_val owner, choiceWithZero_assoc owner, choiceWithZero_comm owner,
    choiceWithZero_self owner, choiceWithZero_union_left owner,
    choiceWithZero_union_right owner, choiceWithZero_empty_left owner,
    choiceWithZero_empty_right owner⟩

theorem choiceWithZero_representation :
    Function.Injective (Relational.regularRelation (choiceWithZero owner)) ∧
    Relational.regularRelation (choiceWithZero owner) ∅ = (fun _ _ => False) ∧
    (∀ A B, Relational.regularRelation (choiceWithZero owner) (A ∪ B) = fun x y =>
      Relational.regularRelation (choiceWithZero owner) A x y ∨
      Relational.regularRelation (choiceWithZero owner) B x y) ∧
    ∀ A B, Relational.regularRelation (choiceWithZero owner) (choiceWithZero owner A B) =
      Relation.Comp (Relational.regularRelation (choiceWithZero owner) A)
        (Relational.regularRelation (choiceWithZero owner) B) :=
  Relational.regular_representation_of_columns (choiceWithZero owner)
    (choiceWithZero_assoc owner) (choiceWithZero_columns owner)
    (choiceWithZero_union_right owner) (choiceWithZero_empty_right owner)

/-- The old nonempty representation is the restriction of the zero extension. -/
theorem choiceWithZero_relation (A : WinnerSet Role) :
    Relational.regularRelation (choiceWithZero owner) A.val = Query.relation owner A := by
  funext x y
  cases y with
  | none => rfl
  | some y =>
    cases x with
    | none => rfl
    | some x =>
      change (y ∈ choiceWithZero owner (singleton x).val A.val) = _
      rw [choiceWithZero_val, choice_comm]
      rfl

end KFOL.WinnerSet
