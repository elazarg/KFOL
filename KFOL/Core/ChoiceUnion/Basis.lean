module

public import KFOL.Core.ChoiceUnion.ThreeCompleteness
public import KFOL.Core.ChoiceUnion.Embedding
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Set.Card

/-! # The full seven-equation basis for one raw owned choice and union -/

@[expose] public section

namespace KFOL.Dissemilattice

universe u v

attribute [local instance] Three.structureOf

/-- A model belongs to the winner-generated variety exactly when it is a
nonempty meet-distributive bisemilattice. The complete seven-law generation
argument is direct and does not assume an external generation theorem. -/
theorem inVariety_winner_iff_laws {Role : Type v} (three : Fin 3 ↪ Role) (owner : Role)
    (M : Type u) [(Equational.language Symbol).Structure M] :
    letI := winnerStructure owner
    Equational.InVariety Symbol (WinnerSet Role) M ↔ Nonempty M ∧ Laws (M := M) add mul := by
  let _ := winnerStructure owner
  constructor
  · intro hM
    exact ⟨hM.1,laws_iff_models.mpr (hM.models (laws_iff_models.mp (winner_laws owner)))⟩
  · rintro ⟨hne,hM⟩
    let _ := hne
    exact (three_in_winner_variety three owner).trans (inVariety_three_of_laws hM)

/-- Full equational completeness of the literal seven equations for every
owner of every role carrier containing three distinct roles. -/
theorem basis_winner {Role : Type v} (three : Fin 3 ↪ Role) (owner : Role) :
    letI := winnerStructure owner
    Equational.IsBasis (WinnerSet Role) theory := by
  let _ := winnerStructure owner
  apply (Equational.isBasis_iff_models theory).mpr
  refine ⟨laws_iff_models.mp (winner_laws owner),?_⟩
  intro M _ hne hM
  exact (inVariety_winner_iff_laws three owner M).mpr ⟨hne,laws_iff_models.mpr hM⟩

private def joinCount {Var : Type u} : Term Var → ℕ
  | .var _ => 0
  | .func Symbol.join args => joinCount (args 0) + joinCount (args 1) + 1
  | .func Symbol.mul args => joinCount (args 0) + joinCount (args 1)

private def mulCount {Var : Type u} : Term Var → ℕ
  | .var _ => 0
  | .func Symbol.join args => mulCount (args 0) + mulCount (args 1)
  | .func Symbol.mul args => mulCount (args 0) + mulCount (args 1) + 1

private def axiomTag (e : Equational.Identity Symbol) : ℕ :=
  100 * joinCount e.lhs + 10 * mulCount e.lhs + joinCount e.rhs + mulCount e.rhs

/-- The seven displayed syntax pairs are distinct, not just a length-seven
list that could contain duplicate equations. -/
theorem basisAxiom_injective : Function.Injective basisAxiom := by
  intro i j he
  have ht := congrArg axiomTag he
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | simp [axiomTag,basisAxiom,joinCount,mulCount,joinTerm,mulTerm] at ht

theorem theory_finite : theory.Finite := Set.finite_range basisAxiom

theorem theory_ncard : theory.ncard = 7 := by
  rw [theory,Set.ncard_range_of_injective basisAxiom_injective,Nat.card_fin]

theorem hasFiniteBasis_winner {Role : Type v} (three : Fin 3 ↪ Role) (owner : Role) :
    letI := winnerStructure owner
    Equational.HasFiniteBasis Symbol (WinnerSet Role) := by
  let _ := winnerStructure owner
  exact ⟨theory,theory_finite,basis_winner three owner⟩

/-- The other distributive law fails in the actual generator, so none was
silently used by the completeness proof. -/
theorem three_not_other_distributive :
    Three.add .n (Three.mul .b .p) ≠ Three.mul (Three.add .n .b) (Three.add .n .p) := by decide

end KFOL.Dissemilattice
