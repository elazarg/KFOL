module

public import KFOL.Complexity.GuardedPairCompleteness

/-! Original ternary-only reduction, sparse support and complete class endpoints. -/

@[expose] public section

namespace KFOLTest.ComplexityGuardedPair

open KFOL KFOL.Complexity
open Turing.MultiTapeTM

example (operation : FiniteTermCode.Operation GuardedPair.Symbol) : operation.1 = 3 := by
  cases operation with
  | mk n symbol => cases symbol; rfl

example : (Reductions.ResetUnion.support [[(2^30, true)]]).length = 2 := by decide
example : Reductions.GuardedPair.booleanName (2^30) = 1073741826 := by decide

example :
    (Reductions.GuardedPair.equation [[(2^30, true)]]).1.size +
      (Reductions.GuardedPair.equation [[(2^30, true)]]).2.size = 35 := by decide

example (formula : Reductions.CNF) :
    FiniteTermCode.decodeEquation GuardedPair.Symbol
      (FiniteTermCode.encodeEquation GuardedPair.Symbol (Reductions.GuardedPair.equation formula)) =
        some (Reductions.GuardedPair.equation formula) := FiniteTermCode.decodeEquation_encodeEquation _

example : ComputableInPolyTime Reductions.GuardedPair.equation
    GuardedPairMachines.cnfEncoding GuardedPairMachines.equationEncoding := GuardedPairMachines.reduction_polyTime

example : Cslib.Complexity.coNPComplete encBits
    {word | ∃ equation : GuardedPairMachines.Tree × GuardedPairMachines.Tree,
      FiniteTermCode.encodeEquation GuardedPair.Symbol equation = word ∧
        ∀ valuation : ℕ → WinnerSet (Fin 3), equation.1.eval 0 1 valuation = equation.2.eval 0 1 valuation} :=
  GuardedPairCompleteness.language_coNPComplete (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)

example : Cslib.Complexity.coNPComplete encBits
    {word | ∃ equation : GuardedPairMachines.Tree × GuardedPairMachines.Tree,
      FiniteTermCode.encodeEquation GuardedPair.Symbol equation = word ∧
        ∀ valuation : ℕ → WinnerSet (Fin 3),
          (2 : Fin 3) ∈ (equation.1.eval 0 1 valuation).val ↔ 2 ∈ (equation.2.eval 0 1 valuation).val} :=
  GuardedPairCompleteness.observation_language_coNPComplete (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)

end KFOLTest.ComplexityGuardedPair
