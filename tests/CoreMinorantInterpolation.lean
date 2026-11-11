import KFOL.Core.MinorantPatches
import KFOL.Core.MinorantFivePatches
import KFOL.Core.FivePointInterpolation

open KFOL Core

-- The obstruction excludes every core minorant, not just equality with a term.
example : ∃ f : (Fin 4 → WinnerSet (Fin 3)) → WinnerSet (Fin 3),
    LocallyInterpolable 3 f ∧
      ¬∃ t : Term (Fin 3) (Fin 4), t.IsCore ∧ ∀ v, (t.eval v).val ⊆ (f v).val := by
  obtain ⟨f, hf, _, hn⟩ := exists_three_local_without_core_minorant
    (Function.Embedding.refl (Fin 3))
  exact ⟨f, hf, hn⟩

-- No finiteness of the role set is hidden in the four-row cover or the patches.
example : ∃ f : (Fin 4 → WinnerSet ℕ) → WinnerSet ℕ,
    PreservesInvariants 3 f ∧
      ¬∃ t : Term ℕ (Fin 4), t.IsCore ∧ ∀ v, t.eval v = f v := by
  let three : Fin 3 ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  obtain ⟨f, _, hf, hn⟩ := exists_three_local_without_core_minorant three
  refine ⟨f, hf, ?_⟩
  rintro ⟨t, ht, he⟩
  exact hn ⟨t, ht, fun v => by rw [he v]⟩

-- Five explicit patches raise the obstruction to four-point tests, uniformly
-- in extra roles. Their finite status certificate is checked by the kernel.
example : ∃ f : (Fin 5 → WinnerSet ℕ) → WinnerSet ℕ,
    LocallyInterpolable 4 f ∧ PreservesInvariants 4 f ∧
      ¬∃ t : Term ℕ (Fin 5), t.IsCore ∧ ∀ v, (t.eval v).val ⊆ (f v).val :=
  exists_four_local_without_core_minorant ⟨Fin.val, Fin.val_injective⟩

-- The five-point obstruction also works with infinitely many owners; its
-- actual core minorant distinguishes it from the earlier cover obstructions.
example : ∃ f : (Fin 5 → WinnerSet ℕ) → WinnerSet ℕ,
    LocallyInterpolable 5 f ∧ PreservesInvariants 5 f ∧
      (∃ t : Term ℕ (Fin 5), t.IsCore ∧ ∀ v, (t.eval v).val ⊆ (f v).val) ∧
      ¬∃ t : Term ℕ (Fin 5), t.IsCore ∧ ∀ v, t.eval v = f v :=
  exists_five_local_noncore ⟨Fin.val, Fin.val_injective⟩
