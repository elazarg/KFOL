module
public import KFOL.Complexity.RawPairCompleteness
public import KFOL.Complexity.Canonicalization
@[expose] public section
namespace KFOLTest.ComplexityRawPairs
open KFOL KFOL.Complexity Turing.MultiTapeTM
example (operation : FiniteTermCode.Operation RawPair.Symbol) : operation.1 = 2 := by
  cases operation with | mk n symbol => cases symbol; rfl
example : Reductions.RawPair.equation [[]] = ((.var 0, .var 0) : RawPairMachines.Tree × RawPairMachines.Tree) := rfl
example : Reductions.RawPair.twoOwnerEquation [] = ((.var 0, .var 1) : RawPairMachines.Tree × RawPairMachines.Tree) := rfl
example : Reductions.ResetChoice.equation [[]] = ((.var 0, .var 0) : RawPairMachines.Tree × RawPairMachines.Tree) := rfl
example : (Reductions.ResetUnion.support [[(2^30, true)]]).length = 2 := by decide
example (formula : Reductions.CNF) :
    FiniteTermCode.decodeEquation RawPair.Symbol (FiniteTermCode.encodeEquation RawPair.Symbol
      (Reductions.ResetChoice.equation formula)) = some (Reductions.ResetChoice.equation formula) :=
  FiniteTermCode.decodeEquation_encodeEquation _
example : ComputableInPolyTime Reductions.RawPair.equation RawPairMachines.cnfEncoding RawPairMachines.equationEncoding :=
  RawPairMachines.reduction_polyTime
example : ComputableInPolyTime Reductions.RawPair.twoOwnerEquation RawPairMachines.cnfEncoding RawPairMachines.equationEncoding :=
  RawPairMachines.twoOwnerReduction_polyTime
example : ComputableInPolyTime Reductions.ResetChoice.equation RawPairMachines.cnfEncoding RawPairMachines.equationEncoding :=
  ResetChoiceMachines.reduction_polyTime
example : Cslib.Complexity.coNPComplete encBits
    (RawPairCompleteness.Language (WinnerSet.choice (0 : Fin 3)) WinnerSet.union) :=
  RawPairCompleteness.union_language_coNPComplete (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
example : Cslib.Complexity.coNPComplete encBits
    (RawPairCompleteness.Language (WinnerSet.choice (0 : Fin 3)) (WinnerSet.choice 1)) :=
  RawPairCompleteness.twoOwners_language_coNPComplete (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
example : Cslib.Complexity.coNPComplete encBits
    (RawPairCompleteness.Language WinnerSet.reset (WinnerSet.choice (0 : Fin 3))) :=
  RawPairCompleteness.resetChoice_language_coNPComplete (0 : Fin 3) 1 2 (by decide) (by decide) (by decide)
end KFOLTest.ComplexityRawPairs
