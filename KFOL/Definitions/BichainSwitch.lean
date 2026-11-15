module

public import KFOL.Definitions.BichainEssential

/-! # The matching-to-square Boolean switch

Coordinates 0,1,2,3 are a,b,c,d; coordinate 4 selects the additional edges.
-/

@[expose] public section
namespace KFOL.Bichain

/-- Two disjoint edges, with the other two square edges enabled by coordinate 4. -/
def squareSwitch (v : Fin 5 → Bool) : Bool :=
  (v 0 && v 1) || (v 2 && v 3) || (v 4 && v 0 && v 3) || (v 4 && v 1 && v 2)

/-- Explicit read-once realizers for all ten one-variable Boolean cofactors. -/
def squareSwitchCofactorTerm (j : Fin 5) (bit : Bool) : Term (Fin 5) :=
  let a : Term (Fin 5) := .var 0
  let b' : Term (Fin 5) := .var 1
  let c' : Term (Fin 5) := .var 2
  let d : Term (Fin 5) := .var 3
  let z : Term (Fin 5) := .var 4
  match j.val, bit with
  | 0, false => .inf c' (.sup d (.inf z b'))
  | 0, true => .sup b' (.inf d (.sup c' z))
  | 1, false => .inf d (.sup c' (.inf z a))
  | 1, true => .sup a (.inf c' (.sup d z))
  | 2, false => .inf a (.sup b' (.inf z d))
  | 2, true => .sup d (.inf b' (.sup a z))
  | 3, false => .inf b' (.sup a (.inf z c'))
  | 3, true => .sup c' (.inf a (.sup b' z))
  | _, false => .sup (.inf a b') (.inf c' d)
  | _, true => .inf (.sup a c') (.sup b' d)

end KFOL.Bichain
