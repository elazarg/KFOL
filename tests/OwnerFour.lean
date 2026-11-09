module

public import KFOL.Owner.Four

@[expose] public section

namespace KFOLTest.OwnerFour

open KFOL.Owner

example : Fintype.card Four = 4 := Four.card
example : Four.reset .winning .ambiguous = .winning := by decide
example : Four.reset .winning .other = .other := by decide
example : Four.guarded .ambiguous .owner .winning = .ambiguous := by decide
example : Four.guarded .ambiguous .other .winning = .winning := by decide
example : Four.guarded .winning .owner .other = .winning := by decide

private def x : Term Unit (Fin 3) := .var 0
private def y : Term Unit (Fin 3) := .var 1
private def z : Term Unit (Fin 3) := .var 2

example : (Term.guarded () x y z).evalFour (fun i =>
    if i = 0 then .ambiguous else if i = 1 then .owner else .winning) = .ambiguous := by decide
example : (Term.guarded () x y z).evalFour (fun i =>
    if i = 0 then .ambiguous else if i = 1 then .other else .winning) = .winning := by decide

/-- info: 'KFOL.Owner.Term.four_element_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.Term.four_element_complete

end KFOLTest.OwnerFour
