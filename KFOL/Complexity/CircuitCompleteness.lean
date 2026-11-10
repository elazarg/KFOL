module

public import KFOL.Complexity.CircuitVerifier
public import KFOL.Complexity.CircuitGeneratorRecords
public import KFOL.Reductions.Circuits

/-! Complete original reset-DAG language on the actual three-element algebra. -/

@[expose] public section

namespace KFOL.Complexity.CircuitCompleteness

universe u

open Turing.MultiTapeTM

/-- Cached evaluation on the actual three-element reset table supplies a
complete native coNP verifier for the original flat graph word language. -/
theorem reset_chain_language_mem_coNP :
    let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    Circuit.Code.Language Reset.Symbol (Fin 3) ∈ Cslib.Complexity.coNP encBits := by
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  exact CircuitMachine.language_mem_coNP (σ := Reset.Symbol) (Value := Fin 3)

/-- The SAME fixed Fin3 cached verifier works for all role carriers admitting
three roles; its machine bound does not enumerate that carrier. -/
theorem reset_language_mem_coNP {Role : Type u} (three : Fin 3 ↪ Role) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    Circuit.Code.Language Reset.Symbol (WinnerSet Role) ∈ Cslib.Complexity.coNP encBits := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  have heq : Circuit.Code.Language Reset.Symbol (WinnerSet Role) = Circuit.Code.Language Reset.Symbol (Fin 3) := by
    ext word
    change (∃ equation : Circuit.Equation Reset.Symbol ℕ,
      Circuit.Code.encode Reset.Symbol equation = word ∧ equation.Holds (WinnerSet Role)) ↔
      ∃ equation : Circuit.Equation Reset.Symbol ℕ,
        Circuit.Code.encode Reset.Symbol equation = word ∧ equation.Holds (Fin 3)
    apply exists_congr
    intro equation
    exact and_congr Iff.rfl (equation.reset_holds_iff_fin_three three)
  change Circuit.Code.Language Reset.Symbol (WinnerSet Role) ∈ Cslib.Complexity.coNP encBits
  rw [heq]
  exact reset_chain_language_mem_coNP

end KFOL.Complexity.CircuitCompleteness
