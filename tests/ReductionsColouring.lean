module

public import KFOL.Reductions.Colouring

@[expose] public section

namespace KFOLTest.ReductionsColouring

open KFOL
open KFOL.Reductions.Colouring

example : edges 3 = [(0, 1), (0, 2), (1, 2)] := by decide
example : (equation 3).arity = 5 := rfl
example : vertexName 3 0 = 2 := rfl
example : vertexName 3 2 = 4 := rfl

example : letI := ResetUnion.structureOf (Role := Fin 3)
    (equation 3).Holds (WinnerSet (Fin 3)) := equation_holds_fin 3

example : letI := ResetUnion.structureOf (Role := Fin 4)
    ¬(equation 3).Holds (WinnerSet (Fin 4)) := not_equation_holds_fin_succ 3 (by decide)

example :
    {e : Equational.Identity ResetUnion.Symbol |
      letI := ResetUnion.structureOf (Role := Fin 4); e.Holds (WinnerSet (Fin 4))} ⊂
    {e : Equational.Identity ResetUnion.Symbol |
      letI := ResetUnion.structureOf (Role := Fin 3); e.Holds (WinnerSet (Fin 3))} :=
  theory_succ_ssubset 3 (by decide)

/-- info: 'KFOL.Reductions.Colouring.equation_holds_fin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.Colouring.equation_holds_fin

/-- info: 'KFOL.Reductions.Colouring.successor_separates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.Colouring.successor_separates

/-- info: 'KFOL.Reductions.Colouring.theory_succ_ssubset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.Colouring.theory_succ_ssubset

end KFOLTest.ReductionsColouring
