module

public import KFOL.Complexity.ResetUnionHardness
public import KFOL.Complexity.FiniteAlgebraVerifier

/-! # Full machine-level coNP completeness at every fixed finite role set -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionCompleteness

open Turing.MultiTapeTM
open KFOL.ResetUnion

private theorem fold_eval {Role : Type} (valuation : ℕ → WinnerSet Role) (t : KFOL.ResetUnion.Term ℕ) :
    ResetUnionEvaluation.fold (fun (v : ℕ → WinnerSet Role) j => v j)
      WinnerSet.reset WinnerSet.union valuation t = t.eval valuation := by
  induction t using Term.induction_binary with
  | var j => rfl
  | reset s t hs ht => rw [ResetUnionEvaluation.fold_reset, Term.eval_reset, hs, ht]
  | union s t hs ht => rw [ResetUnionEvaluation.fold_union, Term.eval_union, hs, ht]

/-- At fixed finite Role, countervaluations of linearly many finite-value
blocks give a complete native polynomial-time verifier for nonvalidity. -/
theorem validity_mem_coNP {Role : Type} [Fintype Role] [Nonempty Role] :
    {equation | Valid Role equation} ∈ Cslib.Complexity.coNP ResetUnionMachines.equationEncoding := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton (Classical.choice inferInstance)⟩
  have h := FiniteAlgebraVerifier.holds_mem_coNP (Value := WinnerSet Role) WinnerSet.reset WinnerSet.union
  have he : {equation | FiniteAlgebraVerifier.Holds (Value := WinnerSet Role) WinnerSet.reset WinnerSet.union equation} =
      {equation | Valid Role equation} := by
    ext equation
    simp only [FiniteAlgebraVerifier.Holds, Valid, fold_eval, Set.mem_ofPred_eq]
  rw [he] at h
  exact h

/-- Actual many-one hardness and a complete polynomial countervaluation
verifier, for every fixed finite role set with three distinct roles. -/
theorem coNPComplete {Role : Type} [Fintype Role] (three : Fin 3 ↪ Role) :
    Cslib.Complexity.coNPComplete ResetUnionMachines.equationEncoding {equation | Valid Role equation} := by
  let : Nonempty Role := ⟨three 0⟩
  exact ⟨validity_mem_coNP, ResetUnionHardness.coNPHard three⟩

end KFOL.Complexity.ResetUnionCompleteness
