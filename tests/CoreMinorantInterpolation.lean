import KFOL.Core.MinorantPatches

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
