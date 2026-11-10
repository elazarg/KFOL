module

public import KFOL.Complexity.CircuitCompleteness
public import KFOL.Complexity.CircuitGenerator
public import KFOL.Complexity.CNFHardness

/-! Actual native 3SAT transport for the complete original reset DAG language. -/

@[expose] public section

namespace KFOL.Complexity.CircuitCompleteness

universe u

open Turing.MultiTapeTM

private theorem unsatisfiable_empty_clause : ¬Reductions.Satisfiable [[]] := by
  rintro ⟨assignment, hall⟩
  obtain ⟨literal, hl, _⟩ := hall [] (by simp)
  exact List.not_mem_nil hl

private theorem mem_encode_iff {M : Type u}
    [(Equational.language Reset.Symbol).Structure M] (equation : Circuit.Equation Reset.Symbol ℕ) :
    Circuit.Code.encode Reset.Symbol equation ∈ Circuit.Code.Language Reset.Symbol M ↔ equation.Holds M := by
  constructor
  · rintro ⟨other, he, hh⟩
    have heq := (Circuit.Code.encoding Reset.Symbol).injective he
    exact heq ▸ hh
  · intro hh
    exact ⟨equation, rfl, hh⟩

private theorem chain_equation_iff (formula : Reductions.CNF) :
    let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    (Circuit.ResetCNF.equation formula).Holds (Fin 3) ↔ ¬Reductions.Satisfiable formula := by
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  let _ := Reset.structureOf (WinnerSet.reset (Role := Fin 3))
  have hchain := (Circuit.ResetCNF.equation formula).reset_holds_iff_fin_three (Function.Embedding.refl (Fin 3))
  dsimp only at hchain
  exact hchain.symm.trans (Circuit.ResetCNF.equation_holds_iff_unsatisfiable (Function.Embedding.refl _) formula)

/-- The generator is an actual native polynomial-time machine producing the
ORIGINAL shared graph word. The lower bound uses pinned machine-level3SAT. -/
theorem reset_chain_coNPHard :
    let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    Cslib.Complexity.coNPHard encBits (Circuit.Code.Language Reset.Symbol (Fin 3)) := by
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  apply CNFHardness.coNPHard_of_CNF (fun word => word ∈ Circuit.Code.Language Reset.Symbol (Fin 3))
    (fun formula => Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation formula))
    CircuitGenerator.encoded_reduction_polyTime
    (fun formula => (mem_encode_iff _).trans (chain_equation_iff formula))
    (Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation [[]]))
  exact (mem_encode_iff _).mpr ((chain_equation_iff [[]]).mpr unsatisfiable_empty_clause)

/-- The same original-word machine reduction works for every role carrier
with three roles, without assuming or enumerating its full finite carrier. -/
theorem reset_coNPHard {Role : Type u} (three : Fin 3 ↪ Role) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    Cslib.Complexity.coNPHard encBits (Circuit.Code.Language Reset.Symbol (WinnerSet Role)) := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  apply CNFHardness.coNPHard_of_CNF (fun word => word ∈ Circuit.Code.Language Reset.Symbol (WinnerSet Role))
    (fun formula => Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation formula))
    CircuitGenerator.encoded_reduction_polyTime
    (fun formula => (mem_encode_iff _).trans (Circuit.ResetCNF.equation_holds_iff_unsatisfiable three formula))
    (Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation [[]]))
  exact (mem_encode_iff _).mpr ((Circuit.ResetCNF.equation_holds_iff_unsatisfiable three [[]]).mpr unsatisfiable_empty_clause)

/-- Full coNP-completeness of the complete ORIGINAL shared-graph word language
on the displayed three-element multiplication table, malformed words excluded. -/
theorem reset_chain_coNPComplete :
    let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    Cslib.Complexity.coNPComplete encBits (Circuit.Code.Language Reset.Symbol (Fin 3)) := by
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  exact ⟨reset_chain_language_mem_coNP, reset_chain_coNPHard⟩

/-- Full coNP-completeness for the actual winner-set reset DAG equations. -/
theorem reset_coNPComplete {Role : Type u} (three : Fin 3 ↪ Role) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    Cslib.Complexity.coNPComplete encBits (Circuit.Code.Language Reset.Symbol (WinnerSet Role)) := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  exact ⟨reset_language_mem_coNP three, reset_coNPHard three⟩

end KFOL.Complexity.CircuitCompleteness
