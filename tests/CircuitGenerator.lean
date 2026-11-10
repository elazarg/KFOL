module
import KFOL.Complexity.CircuitGenerator
import KFOL.Reductions.Circuits
namespace KFOL.Tests.CircuitGenerator
open KFOL.Complexity.CircuitGenerator
open Turing.MultiTapeTM
open KFOL.Reductions

/-- Native runtime and exact whole original word roundtrip are connected. -/
theorem original_shared_generator :
    ComputableInPolyTime (fun φ => Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation φ))
      KFOL.Complexity.ResetUnionReduction.cnfEncoding encBits ∧
    ∀ φ : CNF, Circuit.Code.decode Reset.Symbol
      (Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation φ)) =
        some (Circuit.ResetCNF.equation φ) :=
  ⟨encoded_reduction_polyTime,fun φ => Circuit.Code.decode_encode Reset.Symbol (Circuit.ResetCNF.equation φ)⟩

example : combNodes [8,3] 1 10 = [resetGate 3 1,resetGate 8 10] := rfl
example : clauseNodes [4,5] 1 0 10 =
    [resetGate 1 4,resetGate 1 5,resetGate 11 0,resetGate 10 12] := rfl
example : consistencyNodes [(2,3),(4,5)] 1 0 6 =
    [resetGate 1 2,resetGate 6 3,resetGate 1 4,resetGate 8 5,
      resetGate 9 0,resetGate 7 10] := rfl
example : cnfNodes [[],[2],[]] 1 0 10 = [resetGate 0 2,resetGate 10 0] := rfl
example : prefixOutput [[],[2],[]] 1 0 10 = 0 := rfl
example : prefixOutput [] 1 0 10 = 1 := rfl
example : (Circuit.ResetCNF.equation []).gates.length = 10 := by decide
example : (Circuit.ResetCNF.equation [[]]).gates.length = 10 := by decide
example : (Circuit.ResetCNF.equation [[(1000000000,true)]]).gates.length = 19 := by decide
example (formula : CNF) : (Circuit.ResetCNF.equation formula).WellFormed :=
  Circuit.ResetCNF.equation_wellFormed formula
example (formula : CNF) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := ℕ))
    (Circuit.ResetCNF.equation formula).Holds (WinnerSet ℕ) ↔ ¬ Satisfiable formula :=
  Circuit.ResetCNF.equation_holds_iff_unsatisfiable (Fin.valEmbedding : Fin 3 ↪ ℕ) formula
#print axioms original_shared_generator
end KFOL.Tests.CircuitGenerator
