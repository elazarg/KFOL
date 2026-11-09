module

public import KFOL.Core.GridLocalCover

/-! # Matching blocks for arbitrary finite sets of generated elements -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

open FirstOrder

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf Equational.coreStructure structureOf

/-- Arbitrary Boolean observations on m objects have at most 2^m profiles. -/
theorem exists_duplicate_bits {M : Type*} (X : Finset M) {n : ℕ}
    (bits : Fin n → M → Bool) (hn : 2 ^ X.card < n) :
    ∃ i k : Fin n, i ≠ k ∧ ∀ x ∈ X, bits i x = bits k x := by
  classical
  let signature : Fin n → X → Bool := fun i x => bits i x.val
  have hi : ¬ Function.Injective signature := by
    intro h
    have hc := Fintype.card_le_of_injective signature h
    simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
    omega
  simp only [Function.Injective, not_forall] at hi
  obtain ⟨i,k,hik,hne⟩ := hi
  refine ⟨i,k,hne,?_⟩
  intro x hx
  exact congrFun hik ⟨x,hx⟩

/-- Adjoin e to an arbitrary finite set of generated elements. These are
not assumed to be any of the original source columns. -/
def generated {r s : ℕ} (three : Fin 3 ↪ Role) (X : Finset (span (r := r) (s := s) three)) :
    (Equational.language (Equational.CoreSymbol Role)).Substructure (span (r := r) (s := s) three) :=
  Language.Substructure.closure _ (insert (lower three) (X : Set (span three)))

theorem lower_mem_generated {r s : ℕ} (three : Fin 3 ↪ Role)
    (X : Finset (span (r := r) (s := s) three)) : lower three ∈ generated three X :=
  Language.Substructure.subset_closure (Set.mem_insert _ _)

/-- Equality of Boolean block maps on arbitrary generators extends to their
whole generated subalgebra, including the separately adjoined e. -/
theorem A_matching_generated {r s : ℕ} (hr : 2 ≤ r) (three : Fin 3 ↪ Role)
    (X : Finset (span (r := r) (s := s) three)) (i k : Fin r)
    (matching : ∀ x ∈ X, A hr three i x = A hr three k x)
    (x : generated three X) : A hr three i x.val = A hr three k x.val := by
  refine Language.Substructure.closure_induction
    (p := fun c => A hr three i c = A hr three k c) x.property ?_ ?_
  · intro c hc
    rcases hc with hc | hc
    · subst c; simp
    · exact matching c hc
  · intro n f args ih
    cases f with
    | choice owner =>
      rw [funMap_choice]
      change A hr three i (Core.operation owner (args 0) (args 1)) = _
      rw [A_operation,A_operation,ih 0,ih 1]

theorem B_matching_generated {r s : ℕ} (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (X : Finset (span (r := r) (s := s) three)) (j l : Fin s)
    (matching : ∀ x ∈ X, B hs three j x = B hs three l x)
    (x : generated three X) : B hs three j x.val = B hs three l x.val := by
  refine Language.Substructure.closure_induction
    (p := fun c => B hs three j c = B hs three l c) x.property ?_ ?_
  · intro c hc
    rcases hc with hc | hc
    · subst c; simp
    · exact matching c hc
  · intro n f args ih
    cases f with
    | choice owner =>
      rw [funMap_choice]
      change B hs three j (Core.operation owner (args 0) (args 1)) = _
      rw [B_operation,B_operation,ih 0,ih 1]

/-- Full arbitrary-generator local cover, with the exact exponential
pigeonhole bound from the report. -/
theorem upper_clone_generated_inVariety {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (X : Finset (span (r := r) (s := s) three)) (hXr : 2 ^ X.card < r) (hXs : 2 ^ X.card < s) :
    letI := upperStructure (Role := Role)
      (⟨lower three,lower_mem_generated three X⟩ : generated three X)
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Option (generated three X)) := by
  obtain ⟨i,k,hik,hA⟩ := exists_duplicate_bits X (A hr three) hXr
  obtain ⟨j,l,hjl,hB⟩ := exists_duplicate_bits X (B hs three) hXs
  exact upper_clone_of_matching_blocks hr hs three (generated three X) (lower_mem_generated three X)
    i k hik j l hjl (A_matching_generated hr three X i k hA) (B_matching_generated hs three X j l hB)

end KFOL.Core.Grid
