import KFOL.Core.Interpolation

open KFOL

private def atom (i : Fin 3) : WinnerSet (Fin 3) := WinnerSet.singleton i

-- Three entries suffice to rule out a proposed full winner-set operation.
-- Its singleton-output predicates alone do not express the middle entry.
example (f : (Fin 3 → WinnerSet (Fin 3)) → WinnerSet (Fin 3))
    (h₀ : f ![(atom 0).union (atom 1), atom 1, atom 1] = atom 1)
    (h₁ : f ![atom 1, (atom 1).union (atom 2), (atom 0).union (atom 1)] =
      (atom 1).union (atom 2))
    (h₂ : f ![atom 0, atom 1, atom 2] = (atom 0).union (atom 2)) :
    ¬∃ t : Term (Fin 3) (Fin 3), t.IsCore ∧ ∀ v, t.eval v = f v := by
  rintro ⟨t, ht, he⟩
  have hb := Core.three_valuation_persistence (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) id t ht (by simpa [he, atom] using h₀)
    (by simpa [he, atom] using h₁)
  rw [he] at hb
  change (1 : Fin 3) ∈ (f ![atom 0, atom 1, atom 2]).val at hb
  rw [h₂] at hb
  simp [atom] at hb
