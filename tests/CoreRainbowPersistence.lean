import KFOL.Core.RainbowPersistence

open KFOL KFOL.Core

attribute [local instance] Equational.coreStructure

-- No finite-domain assumption: an upper bound without profile requirements
-- is feasible exactly when some input already satisfies it.
example (values : ℕ → WinnerSet ℕ) (U : Set ℕ) :
    (∃ t : Equational.Term (Equational.CoreSymbol ℕ) ℕ,
      (t.realize values).val ⊆ U) ↔ ∃ j, (values j).val ⊆ U := by
  have h := rainbow_budget_iff (∅ : Finset ℕ) (fun _ _ : ℕ => false) values U
  simpa using h

-- Empty variable types have no witness, even with no profile demands and
-- a completely unrestricted output bound.
example (values : Fin 0 → WinnerSet ℕ) :
    ¬∃ t : Equational.Term (Equational.CoreSymbol ℕ) (Fin 0),
      (t.realize values).val ⊆ Set.univ := by
  have h := rainbow_budget_iff (∅ : Finset ℕ)
    (fun _ : ℕ => fun _ : Fin 0 => false) values Set.univ
  simpa using h
