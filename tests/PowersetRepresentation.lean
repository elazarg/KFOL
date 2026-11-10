module

public import KFOL.Query.ZeroExtension
public import Mathlib.Tactic.NormNum

/-! The regular theorem must also work for noncommutative products. The
left-zero semigroup detects an accidental reversal of composition. -/

@[expose] public section
namespace PowersetRepresentationTest
open KFOL

def leftProduct (A B : Set (Fin 2)) : Set (Fin 2) := {x | x ∈ A ∧ B.Nonempty}

theorem leftProduct_assoc (A B C : Set (Fin 2)) :
    leftProduct (leftProduct A B) C = leftProduct A (leftProduct B C) := by
  ext x
  simp only [leftProduct, Set.mem_ofPred_eq, Set.nonempty_def]
  aesop

theorem leftProduct_union_left (A B C : Set (Fin 2)) :
    leftProduct (A ∪ B) C = leftProduct A C ∪ leftProduct B C := by
  ext x
  simp [leftProduct, or_and_right]

theorem leftProduct_union_right (A B C : Set (Fin 2)) :
    leftProduct A (B ∪ C) = leftProduct A B ∪ leftProduct A C := by
  ext x
  simp [leftProduct, Set.union_nonempty, and_or_left]

example :
    Relational.regularRelation leftProduct (leftProduct {0} {1}) =
      Relation.Comp (Relational.regularRelation leftProduct {0})
        (Relational.regularRelation leftProduct {1}) :=
  (Relational.finite_powerset_representation leftProduct leftProduct_assoc
    leftProduct_union_left leftProduct_union_right (by intro A; ext x; simp [leftProduct])
    (by intro A; ext x; simp [leftProduct])).2.2.2 {0} {1}

example : Relational.regularRelation leftProduct (leftProduct {0} {1}) none (some 0) := by
  simp [Relational.regularRelation, leftProduct]

example : ¬Relation.Comp (Relational.regularRelation leftProduct {1})
    (Relational.regularRelation leftProduct {0}) none (some 0) := by
  simp [Relation.Comp, Relational.regularRelation, leftProduct, Option.exists]

example (A : Set (Fin 3)) : WinnerSet.choiceWithZero 0 ∅ A = ∅ ∧
    WinnerSet.choiceWithZero 0 A ∅ = ∅ := by simp

/-- The lattice is Boolean; product need not preserve its meet. -/
example : WinnerSet.choiceWithZero (0 : Fin 3) ({1, 2}) ({0, 1} ∩ {0, 2}) ≠
    WinnerSet.choiceWithZero 0 {1, 2} {0, 1} ∩
      WinnerSet.choiceWithZero 0 {1, 2} {0, 2} := by
  intro h
  have atOne := Set.ext_iff.mp h 1
  norm_num [WinnerSet.choiceWithZero, WinnerSet.choice, WinnerSet.singleton,
    WinnerSet.union, Set.ext_iff, Set.nonempty_def, Subtype.ext_iff, apply_ite,
    Fin.forall_fin_succ, Fin.exists_fin_succ] at atOne

example (Role : Type) : BooleanAlgebra (Set Role) := inferInstance

end PowersetRepresentationTest
