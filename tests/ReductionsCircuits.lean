module

public import KFOL.Reductions.Circuits

@[expose] public section

namespace KFOLTest.ReductionsCircuits

open KFOL
open KFOL.Circuit

example : (ResetCNF.equation []).WellFormed := by decide
example : (ResetCNF.equation [[]]).WellFormed := by decide
example : (ResetCNF.equation [[(1000000000, true)]]).WellFormed := by decide
example : (ResetCNF.equation []).gates.length = 10 := by decide
example : operationCount (ResetCNF.equation []).gates = 6 := by decide
example : operationCount (ResetCNF.equation [[]]).gates = 6 := by decide
example : (ResetCNF.equation [[(1000000000, true)]]).gates.length = 19 := by decide
example : operationCount (ResetCNF.equation [[(1000000000, true)]]).gates = 13 := by decide
example : Gate.references (Gate.func Reset.Symbol.reset (fun i => if i = 0 then 7 else 3) : Gate Reset.Symbol ℕ) = [7, 3] := by decide
example : Gate.references ((Gate.reset 7 3 : Gate Reset.Symbol ℕ).liftReset (Owner.Symbol.guarded ())) = [3, 7, 7] := by decide

example : ¬(⟨[], 0, 0⟩ : Equation Reset.Symbol ℕ).WellFormed := by decide
example :
    let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    (⟨[], 0, 0⟩ : Equation Reset.Symbol ℕ).eval (fun _ => (0 : Fin 3)) = none := rfl

example (three : Fin 3 ↪ ℕ) (formula : Reductions.CNF) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := ℕ))
    (ResetCNF.equation formula).Holds (WinnerSet ℕ) ↔ ¬Reductions.Satisfiable formula :=
  ResetCNF.equation_holds_iff_unsatisfiable three formula

example (three : Fin 3 ↪ ℕ) (owner : ℕ) (formula : Reductions.CNF) :
    let _ := Owner.oneOwnerStructure owner
    ((ResetCNF.equation formula).liftReset (Owner.Symbol.guarded ())).Holds (WinnerSet ℕ) ↔
      ¬Reductions.Satisfiable formula := ResetCNF.guarded_holds_iff_unsatisfiable three owner formula

example (three : Fin 3 ↪ ℕ) (D : Unit → Set ℕ) (formula : Reductions.CNF) :
    let _ := Policies.structureOf D
    ((ResetCNF.equation formula).liftReset (Policies.Symbol.selective ())).Holds (WinnerSet ℕ) ↔
      ¬Reductions.Satisfiable formula := ResetCNF.policy_holds_iff_unsatisfiable three D () formula

example (equation : Equation Reset.Symbol ℕ) (gate : Gate (Owner.Symbol Unit) ℕ)
    (hg : gate ∈ (equation.liftReset (Owner.Symbol.guarded ())).gates) :
    (∃ j, gate = .input j) ∨ ∃ refs : Fin 3 → ℕ, gate = .func (.guarded ()) refs :=
  Equation.gates_liftReset _ equation gate hg

/-- info: 'KFOL.Circuit.runFrom_total' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.runFrom_total

/-- info: 'KFOL.Circuit.Equation.eval_some_of_wellFormed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Equation.eval_some_of_wellFormed

/-- info: 'KFOL.Circuit.Gate.eval_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Gate.eval_map

/-- info: 'KFOL.Circuit.Equation.eval_of_unfold' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Equation.eval_of_unfold

/-- info: 'KFOL.Circuit.Equation.reset_holds_iff_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Equation.reset_holds_iff_chain

/-- info: 'KFOL.Circuit.ResetCNF.eval_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.eval_equation

/-- info: 'KFOL.Circuit.ResetCNF.equation_wellFormed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.equation_wellFormed

/-- info: 'KFOL.Circuit.ResetCNF.equation_gate_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.equation_gate_count

/-- info: 'KFOL.Circuit.ResetCNF.equation_reset_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.equation_reset_gate_count

/-- info: 'KFOL.Circuit.ResetCNF.equation_holds_of_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.equation_holds_of_unsatisfiable

/-- info: 'KFOL.Circuit.ResetCNF.satisfying_assignment_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.satisfying_assignment_separates

/-- info: 'KFOL.Circuit.ResetCNF.equation_holds_iff_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.equation_holds_iff_unsatisfiable

/-- info: 'KFOL.Circuit.ResetCNF.equation_chain_valid_iff_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.equation_chain_valid_iff_unsatisfiable

/-- info: 'KFOL.Circuit.Equation.gates_liftReset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Equation.gates_liftReset

/-- info: 'KFOL.Circuit.Equation.eval_toGuarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Equation.eval_toGuarded

/-- info: 'KFOL.Circuit.Equation.eval_toPolicy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.Equation.eval_toPolicy

/-- info: 'KFOL.Circuit.ResetCNF.guarded_holds_iff_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.guarded_holds_iff_unsatisfiable

/-- info: 'KFOL.Circuit.ResetCNF.policy_holds_iff_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.ResetCNF.policy_holds_iff_unsatisfiable

/-- info: 'KFOL.Circuit.edgeCount_reset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.edgeCount_reset

/-- info: 'KFOL.Circuit.operationCount_liftReset' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.operationCount_liftReset

/-- info: 'KFOL.Circuit.edgeCount_liftReset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Circuit.edgeCount_liftReset

end KFOLTest.ReductionsCircuits
