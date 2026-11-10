module

public import KFOL.Complexity.CircuitHardness

@[expose] public section

namespace KFOLTest.ComplexityCircuits

open KFOL
open KFOL.Complexity
open Turing.MultiTapeTM

noncomputable local instance : (Equational.language Reset.Symbol).Structure (Fin 3) :=
  Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)

private def invalid : Circuit.Equation Reset.Symbol ℕ :=
  ⟨[.input 0, Circuit.Gate.reset 1000000000 0], 1, 0⟩

example : ¬invalid.WellFormed := by decide

example (context : FiniteAlgebraVerifier.Context) :
    (CircuitMachine.evaluate context (CircuitMachine.view invalid) : Option (Fin 3 × Fin 3)) = none := by
  rw [CircuitMachine.evaluate_view]
  exact invalid.eval_eq_none_of_not_wellFormed (by decide) _

example (word : List Bool) : CircuitMachine.verifier (CircuitMachine.view invalid, word) (Value := Fin 3) = true := by
  unfold CircuitMachine.verifier
  rw [CircuitMachine.evaluate_view, invalid.eval_eq_none_of_not_wellFormed (by decide)]
  rfl

example (equation : Circuit.Equation Reset.Symbol ℕ) :
    CircuitMachine.decodeData (Circuit.Code.encode Reset.Symbol equation) = some (CircuitMachine.view equation) := by
  rw [CircuitMachine.decodeData_eq, Circuit.Code.decode_encode]
  rfl

example (equation : Circuit.Equation Reset.Symbol ℕ) :
    CircuitMachine.encodeData (CircuitMachine.view equation) = Circuit.Code.encode Reset.Symbol equation :=
  CircuitMachine.encodeData_view equation

example : Cslib.Complexity.coNPComplete encBits (Circuit.Code.Language Reset.Symbol (Fin 3)) :=
  CircuitCompleteness.reset_chain_coNPComplete

example :
    let _ := Reset.structureOf (WinnerSet.reset (Role := ℕ))
    Cslib.Complexity.coNPComplete encBits (Circuit.Code.Language Reset.Symbol (WinnerSet ℕ)) :=
  CircuitCompleteness.reset_coNPComplete ⟨Fin.val, Fin.val_injective⟩

example :
    ComputableInPolyTime
      (fun phi => Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation phi))
      ResetUnionReduction.cnfEncoding encBits := CircuitGenerator.encoded_reduction_polyTime

/-- info: 'KFOL.Circuit.Code.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Code.decode_encode

/-- info: 'KFOL.Circuit.Code.encode_of_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Code.encode_of_decode

/-- info: 'KFOL.Circuit.Code.gates_length_le_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Code.gates_length_le_encode

/-- info: 'KFOL.Circuit.Equation.reset_holds_iff_fin_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Equation.reset_holds_iff_fin_three

/-- info: 'KFOL.Complexity.CircuitMachine.encodeData_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.encodeData_polyTime

/-- info: 'KFOL.Complexity.CircuitMachine.decodeData_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.decodeData_polyTime

/-- info: 'KFOL.Complexity.CircuitMachine.decodeData_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.decodeData_eq

/-- info: 'KFOL.Complexity.CircuitMachine.run_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.run_polyTime

/-- info: 'KFOL.Complexity.CircuitMachine.evaluate_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.evaluate_polyTime

/-- info: 'KFOL.Complexity.CircuitMachine.evaluate_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.evaluate_view

/-- info: 'KFOL.Complexity.CircuitMachine.verifier_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.verifier_polyTime

/-- info: 'KFOL.Complexity.CircuitMachine.verifier_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.verifier_sound

/-- info: 'KFOL.Complexity.CircuitMachine.verifier_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.verifier_complete

/-- info: 'KFOL.Complexity.CircuitMachine.wordVerifier_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.wordVerifier_polyTime

/-- info: 'KFOL.Complexity.CircuitMachine.language_mem_coNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitMachine.language_mem_coNP

/-- info: 'KFOL.Complexity.CircuitCompleteness.reset_chain_language_mem_coNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitCompleteness.reset_chain_language_mem_coNP

/-- info: 'KFOL.Complexity.CircuitCompleteness.reset_language_mem_coNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitCompleteness.reset_language_mem_coNP

/-- info: 'KFOL.Complexity.CircuitCompleteness.reset_chain_coNPHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitCompleteness.reset_chain_coNPHard

/-- info: 'KFOL.Complexity.CircuitCompleteness.reset_coNPHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitCompleteness.reset_coNPHard

/-- info: 'KFOL.Complexity.CircuitCompleteness.reset_chain_coNPComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitCompleteness.reset_chain_coNPComplete

/-- info: 'KFOL.Complexity.CircuitCompleteness.reset_coNPComplete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.CircuitCompleteness.reset_coNPComplete

end KFOLTest.ComplexityCircuits
