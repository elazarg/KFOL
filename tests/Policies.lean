module

public import KFOL.Policies.Public

@[expose] public section

namespace KFOLTest.Policies

open KFOL.Policies

private def x {Label : Type} : Term Label (Fin 3) := .var 0
private def y {Label : Type} : Term Label (Fin 3) := .var 1
private def z {Label : Type} : Term Label (Fin 3) := .var 2

example : Term.singleEquationB (Term.selective () x y y) (Term.step y x) = true := by decide
example : Term.singleEquationB (Term.selective () x y z) (Term.selective () x z y) = false := by decide
example : (Term.selective () x y z).guards.length = 3 := by decide
example : Term.singleEquationB (Term.selective false x y z) (Term.selective true x y z) = true := by decide

/-- info: 'KFOL.Policies.Term.singleEquationB_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Term.singleEquationB_correct

/-- info: 'KFOL.Policies.Term.single_countervaluation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Term.single_countervaluation

/-- info: 'KFOL.Policies.twoOwnerSelective_not_reset_definable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.twoOwnerSelective_not_reset_definable

private def exampleFamily (d : Fin 3) : Finset (Fin 5) :=
  if d = 0 then {0, 1} else if d = 1 then {0, 1, 3, 4} else {0, 1, 2}

example : familyEasyB exampleFamily (List.finRange 5) (List.finRange 3) = false := by decide
example : familyEasyB (fun d : Fin 2 => exampleFamily (if d = 0 then 0 else 1))
    (List.finRange 5) (List.finRange 2) = true := by decide
example : familyEasyB (fun d : Fin 2 => exampleFamily (if d = 0 then 0 else 2))
    (List.finRange 5) (List.finRange 2) = true := by decide
example : familyEasyB (fun d : Fin 2 => exampleFamily (if d = 0 then 1 else 2))
    (List.finRange 5) (List.finRange 2) = true := by decide

/-- info: 'KFOL.Policies.familyEasyB_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.familyEasyB_correct

private def nestedFamily (d : Fin 2) : Finset (Fin 5) := exampleFamily (if d = 0 then 0 else 1)
private def coveringFamily (d : Fin 2) : Finset (Fin 5) := exampleFamily (if d = 0 then 1 else 2)

example : Term.familyEquationB nestedFamily (List.finRange 5) (List.finRange 2)
    (Term.selective 0 x y z) (Term.selective 1 x y z) = false := by decide
example : Term.familyEquationB nestedFamily (List.finRange 5) (List.finRange 2)
    (Term.selective 0 x y (Term.selective 1 x y z)) (Term.selective 1 x y z) = true := by decide
example : Term.familyEquationB coveringFamily (List.finRange 5) (List.finRange 2)
    (Term.selective 0 x y (Term.selective 1 x y z)) (Term.step (Term.step z y) x) = true := by decide

/-- info: 'KFOL.Policies.Term.familyEquationB_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Term.familyEquationB_correct

/-- info: 'KFOL.Policies.Term.familyEquation_countervaluation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Term.familyEquation_countervaluation

end KFOLTest.Policies
