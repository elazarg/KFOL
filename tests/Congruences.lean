module

public import KFOL.Congruences

/-! Complete proposed statements and exhaustive quotient-count specializations. -/

@[expose] public section

namespace KFOLTest.Congruences

open KFOL
open WinnerSet

universe u

/-- The full closure and fixed-family classification, including the converse
construction for every admissible closure or family. -/
theorem congruence_classification {Role : Type u} [Finite Role] [Nonempty Role]
    (three : Fin 3 ↪ Role) :
    (∀ θ : WinnerSet.Congruence Role,
      ∃! c : ClosureOperator (WinnerSet Role),
        (∀ owner, c (singleton owner) = singleton owner ∨ c (singleton owner) = full) ∧
        ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ c : ClosureOperator (WinnerSet Role),
      (∀ owner, c (singleton owner) = singleton owner ∨ c (singleton owner) = full) →
      ∃ θ : WinnerSet.Congruence Role, ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ θ : WinnerSet.Congruence Role,
      ∃! F : Set (WinnerSet Role), AdmissibleFamily F ∧
        ∀ A B, θ.r A B ↔ familyClosureValue F A = familyClosureValue F B) ∧
    (∀ F : Set (WinnerSet Role), AdmissibleFamily F →
      ∃ θ : WinnerSet.Congruence Role, ∀ A B,
        θ.r A B ↔ familyClosureValue F A = familyClosureValue F B) := by
  refine ⟨WinnerSet.Congruence.exists_unique_closure three,?_,
    WinnerSet.Congruence.exists_unique_family three,?_⟩
  · intro c hc
    exact ⟨WinnerSet.ClosureOperator.kernel c hc,fun _ _ => Iff.rfl⟩
  · intro F hF
    exact ⟨WinnerSet.ClosureOperator.kernel (familyClosure F) (familyClosure_atom F hF),
      fun _ _ => Iff.rfl⟩

/-- The symmetric statement includes all ranks, their unique kernels,
the exact congruence count, chain order, endpoints and quotient cardinalities. -/
theorem symmetric_congruence_chain {Role : Type u} [Finite Role] [Nonempty Role]
    (three : Fin 3 ↪ Role) :
    (∀ θ : SymmetricCongruence Role,
      ∃! m : Fin (Nat.card Role), ∀ A B : WinnerSet Role,
        θ.r A B ↔ threshold m.val A = threshold m.val B) ∧
    (∀ m : Fin (Nat.card Role), ∃ θ : SymmetricCongruence Role, ∀ A B : WinnerSet Role,
      θ.r A B ↔ threshold m.val A = threshold m.val B) ∧
    Nat.card (SymmetricCongruence Role) = Nat.card Role ∧
    (∀ (m n : ℕ), m ≤ n → ∀ A B : WinnerSet Role,
      threshold n A = threshold n B → threshold m A = threshold m B) ∧
    (∀ A : WinnerSet Role, threshold 0 A = full) ∧
    (∀ A : WinnerSet Role, threshold (Nat.card Role - 1) A = A) ∧
    (∀ m : ℕ, m < Nat.card Role →
      Nat.card (Quotient (Setoid.ker (threshold (Role := Role) m))) =
        1 + ∑ j ∈ Finset.Icc 1 m, (Nat.card Role).choose j) := by
  refine ⟨SymmetricCongruence.exists_unique_threshold three,?_,
    SymmetricCongruence.card three,?_,threshold_zero,threshold_last,?_⟩
  · intro m
    exact ⟨WinnerSet.ClosureOperator.symmetricKernel (thresholdClosure m.val)
      (thresholdClosure_atom m.val) (thresholdClosure_invariant m.val),fun _ _ => Iff.rfl⟩
  · intro m n h A B he
    exact threshold_kernel_antitone h A B he
  · intro m hm
    exact card_thresholdQuotient hm

private def three3 : Fin 3 ↪ Fin 3 := Function.Embedding.refl _
private def three4 : Fin 3 ↪ Fin 4 := {
  toFun := fun i => ⟨i.val,by omega⟩
  inj' := fun _ _ h => Fin.ext (congrArg (fun x : Fin 4 => x.val) h) }

example : Nat.card (SymmetricCongruence (Fin 3)) = 3 := by
  simpa only [Nat.card_fin] using SymmetricCongruence.card three3
example : Nat.card (SymmetricCongruence (Fin 4)) = 4 := by
  simpa only [Nat.card_fin] using SymmetricCongruence.card three4

example : Nat.card (Quotient (Setoid.ker (threshold (Role := Fin 4) 2))) = 11 := by
  rw [card_thresholdQuotient (by rw [Nat.card_fin]; decide)]
  simp only [Nat.card_fin]
  decide

example : Nat.card (Quotient (Setoid.ker (threshold (Role := Fin 3) 1))) = 4 := by
  rw [card_thresholdQuotient (by rw [Nat.card_fin]; decide)]
  simp only [Nat.card_fin]
  decide

example : Nat.card (Quotient (Setoid.ker (threshold (Role := Fin 3) 2))) = 7 := by
  rw [card_thresholdQuotient (by rw [Nat.card_fin]; decide)]
  simp only [Nat.card_fin]
  decide

/-- info: 'KFOLTest.Congruences.congruence_classification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOLTest.Congruences.congruence_classification

/-- info: 'KFOLTest.Congruences.symmetric_congruence_chain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOLTest.Congruences.symmetric_congruence_chain

end KFOLTest.Congruences
