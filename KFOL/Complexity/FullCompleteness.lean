module
public import KFOL.Complexity.FullCounterCorrectness
public import KFOL.Complexity.FullPublicReduction
public import Complexity.Computability.Complexity.Classes.NP.Witness
@[expose] public section
namespace KFOL.Complexity.FullCompleteness
open Turing.MultiTapeTM
open KFOL.FullTermCode
open FullHardness

theorem full_coNPComplete : Cslib.Complexity.coNPComplete encBits FullLanguage :=
  ⟨FullCounterVerifier.full_mem_coNP,FullHardness.full_coNPHard⟩

theorem core_coNPComplete : Cslib.Complexity.coNPComplete encBits CoreLanguage :=
  ⟨FullCounterVerifier.core_mem_coNP,FullHardness.core_coNPHard⟩

theorem public_mem_coNP : PublicLanguage ∈ Cslib.Complexity.coNP encBits := by
  have reduction : Cslib.Complexity.PolyTimeReducible encBits encBits PublicLanguage FullLanguage :=
    ⟨FullPublicReduction.reduce,FullPublicReduction.reduce_polyTime,FullPublicReduction.reduce_correct⟩
  exact reduction.mem_coNP FullCounterVerifier.full_mem_coNP

theorem public_coNPComplete : Cslib.Complexity.coNPComplete encBits PublicLanguage :=
  ⟨public_mem_coNP,FullHardness.public_coNPHard⟩

theorem fixed_full_mem_coNP (K : ℕ) (hK : 3 ≤ K) :
    {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
      ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} ∈
      Cslib.Complexity.coNP (originalEquationEncoding K) := by
  have reduction : Cslib.Complexity.PolyTimeReducible (originalEquationEncoding K) encBits
      {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
        ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} FullLanguage :=
    ⟨fun equation => encodeEquationInput ⟨K,equation⟩,Turing.MultiTapeTM.ComputableInPolyTime.of_eq (fun _ => rfl),
      fun equation => by simp only [Set.mem_ofPred_eq,fullLanguage_encode,hK,true_and]⟩
  exact reduction.mem_coNP FullCounterVerifier.full_mem_coNP

theorem fixed_core_mem_coNP (K : ℕ) (hK : 3 ≤ K) :
    {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
      equation.1.IsCore ∧ equation.2.IsCore ∧
        ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} ∈
      Cslib.Complexity.coNP (originalEquationEncoding K) := by
  have reduction : Cslib.Complexity.PolyTimeReducible (originalEquationEncoding K) encBits
      {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
        equation.1.IsCore ∧ equation.2.IsCore ∧
          ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} CoreLanguage :=
    ⟨fun equation => encodeEquationInput ⟨K,equation⟩,Turing.MultiTapeTM.ComputableInPolyTime.of_eq (fun _ => rfl),
      fun equation => by simp only [Set.mem_ofPred_eq,coreLanguage_encode,hK,true_and]⟩
  exact reduction.mem_coNP FullCounterVerifier.core_mem_coNP

theorem fixed_public_mem_coNP (K : ℕ) (hK : 3 ≤ K) :
    {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
      equation.1.IsPublic ∧ equation.2.IsPublic ∧
        ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} ∈
      Cslib.Complexity.coNP (originalEquationEncoding K) := by
  have reduction : Cslib.Complexity.PolyTimeReducible (originalEquationEncoding K) encBits
      {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
        equation.1.IsPublic ∧ equation.2.IsPublic ∧
          ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} PublicLanguage :=
    ⟨fun equation => encodeEquationInput ⟨K,equation⟩,Turing.MultiTapeTM.ComputableInPolyTime.of_eq (fun _ => rfl),
      fun equation => by simp only [Set.mem_ofPred_eq,publicLanguage_encode,hK,true_and]⟩
  exact reduction.mem_coNP public_mem_coNP

private def threeRoles (K : ℕ) (hK : 3 ≤ K) : Fin 3 ↪ Fin K :=
  ⟨fun i => ⟨i.val,by omega⟩,fun _ _ h => Fin.ext (show _ = _ from congrArg (fun j : Fin K => j.val) h)⟩

theorem fixed_full_coNPComplete (K : ℕ) (hK : 3 ≤ K) :
    Cslib.Complexity.coNPComplete (originalEquationEncoding K)
      {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
        ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} := by
  let three := threeRoles K hK
  exact ⟨fixed_full_mem_coNP K hK,FullHardness.fixed_full_coNPHard (three 0) (three 1) (three 2)
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) (three.injective.ne (by decide))⟩

theorem fixed_core_coNPComplete (K : ℕ) (hK : 3 ≤ K) :
    Cslib.Complexity.coNPComplete (originalEquationEncoding K)
      {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
        equation.1.IsCore ∧ equation.2.IsCore ∧
          ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} := by
  let three := threeRoles K hK
  exact ⟨fixed_core_mem_coNP K hK,FullHardness.fixed_core_coNPHard (three 0) (three 1) (three 2)
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) (three.injective.ne (by decide))⟩

theorem fixed_public_coNPComplete (K : ℕ) (hK : 3 ≤ K) :
    Cslib.Complexity.coNPComplete (originalEquationEncoding K)
      {equation : KFOL.Term (Fin K) ℕ × KFOL.Term (Fin K) ℕ |
        equation.1.IsPublic ∧ equation.2.IsPublic ∧
          ∀ valuation : ℕ → WinnerSet (Fin K), equation.1.eval valuation = equation.2.eval valuation} := by
  let three := threeRoles K hK
  exact ⟨fixed_public_mem_coNP K hK,FullHardness.fixed_public_coNPHard (three 0) (three 1) (three 2)
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) (three.injective.ne (by decide))⟩
end KFOL.Complexity.FullCompleteness
