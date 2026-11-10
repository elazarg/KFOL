module

public import KFOL.Owner.FourVariableObstruction

/-! Regressions for actual support, rather than declared arity, and the
five-variable witness separating the whole four-variable theory. -/

@[expose] public section
namespace KFOLTest.OwnerFourVariableObstruction
open KFOL
open Owner.FourVariableObstruction

def paddedExpansion : Equational.Identity (Owner.Symbol Unit) :=
  let u : Owner.Term Unit (Fin 100) := .var 0
  let r : Owner.Term Unit (Fin 100) := .var 1
  let a : Owner.Term Unit (Fin 100) := .var 2
  let b : Owner.Term Unit (Fin 100) := .var 3
  ⟨100, Owner.Term.guarded () (Owner.Term.step u r) a b,
    Owner.Term.step (Owner.Term.step u r) (Owner.Term.guarded () r a b)⟩

example : paddedExpansion.arity = 100 ∧ paddedExpansion.variableCount = 4 := by decide

example : paddedExpansion.Holds Carrier := by
  apply holds_of_variableCount_le _ (by decide)
  intro v
  change Fin 100 → Owner.Four at v
  exact Owner.FiniteBasis.law_h_expand (v 1) (v 2) (v 3) (v 0)

example : ¬actionBand.Holds Carrier := actionBand_fails

example (T : Equational.Theory (Owner.Symbol Unit)) (n : ℕ)
    (hbasis : letI := Owner.fourStructure (Role := Unit); Equational.IsBasis Owner.Four T)
    (hbound : Equational.HasVariableBound T n) : 5 ≤ n :=
  variableBound_ge_five T n hbasis hbound

/-- info: 'KFOL.Owner.FourVariableObstruction.holds_of_variableCount_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FourVariableObstruction.holds_of_variableCount_le

/-- info: 'KFOL.Owner.FourVariableObstruction.variableBound_ge_five_winnerSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FourVariableObstruction.variableBound_ge_five_winnerSet

end KFOLTest.OwnerFourVariableObstruction
