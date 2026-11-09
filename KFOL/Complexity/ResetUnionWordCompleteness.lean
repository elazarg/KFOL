module

public import KFOL.Complexity.ResetUnionCompleteness
public import KFOL.Complexity.ResetUnionDecoding
public import Complexity.Computability.Complexity.Classes.NP.Witness

/-! # Full binary-language coNP completeness, with malformed codes rejected -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionWordCompleteness

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.ResetUnion

private def invalidEquation : Equation := (.var 0, .var 1)

private theorem invalid {Role : Type} (three : Fin 3 ↪ Role) : ¬Valid Role invalidEquation := by
  intro h
  have he := h (fun j => if j = 0 then WinnerSet.singleton (three 0) else WinnerSet.singleton (three 1))
  change WinnerSet.singleton (three 0) = WinnerSet.singleton (three 1) at he
  have hr := three.injective (WinnerSet.singleton_inj.mp he)
  simp at hr

private def totalDecode (word : List Bool) : Equation := (Code.decodeEquation word).getD invalidEquation

private theorem totalDecode_polyTime : ComputableInPolyTime totalDecode encBits ResetUnionMachines.equationEncoding :=
  ResetUnionDecoding.decodeEquation_polyTime.optionGetDWithInput (const invalidEquation)

private theorem totalDecode_correct {Role : Type} (three : Fin 3 ↪ Role) (word : List Bool) :
    word ∈ Language Role ↔ Valid Role (totalDecode word) := by
  unfold totalDecode
  cases hd : Code.decodeEquation word with
  | none =>
    simp only [Option.getD_none]
    constructor
    · rintro ⟨equation, he, _⟩
      have hh := Code.decodeEquation_encodeEquation equation
      rw [he, hd] at hh
      cases hh
    · intro h
      exact False.elim (invalid three h)
  | some equation =>
    simp only [Option.getD_some]
    have he := ResetUnionDecoding.encodeEquation_of_decodeEquation hd
    constructor
    · rintro ⟨other, ho, hv⟩
      have hother := Code.encodeEquation_injective (ho.trans he.symm)
      exact hother ▸ hv
    · intro hv
      exact ⟨equation, he, hv⟩

/-- The complete original binary language belongs to coNP, including all
malformed words. A native total decoder maps those to a fixed invalid equation,
then the imported closure-under-reductions theorem transports the full verifier. -/
theorem language_mem_coNP {Role : Type} [Fintype Role] (three : Fin 3 ↪ Role) :
    Language Role ∈ Cslib.Complexity.coNP encBits := by
  let : Nonempty Role := ⟨three 0⟩
  have hreduce : Cslib.Complexity.PolyTimeReducible encBits ResetUnionMachines.equationEncoding
      (Language Role) {equation | Valid Role equation} :=
    ⟨totalDecode, totalDecode_polyTime, totalDecode_correct three⟩
  exact hreduce.mem_coNP ResetUnionCompleteness.validity_mem_coNP

/-- Native 3SAT hardness and a complete native countervaluation verifier for
the exact original binary reset/union language at every fixed finite role set
containing three distinct roles. There are no caller correctness hypotheses. -/
theorem coNPComplete {Role : Type} [Fintype Role] (three : Fin 3 ↪ Role) :
    Cslib.Complexity.coNPComplete encBits (Language Role) :=
  ⟨language_mem_coNP three, ResetUnionHardness.language_coNPHard three⟩

end KFOL.Complexity.ResetUnionWordCompleteness
