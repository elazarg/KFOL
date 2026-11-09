module

public import KFOL.Owner.BasisObstruction

@[expose] public section

namespace KFOLTest.OwnerBasisObstruction

open KFOL.Owner.BasisObstruction

example : Fintype.card Carrier = 4 := by decide
example : rootExpansion.variableCount = 4 := by decide
example : guarded (reset .middle .low) .high .isolated = .middle := by decide
example : reset (reset .middle .low) (guarded .low .high .isolated) = .high := by decide

/-- info: 'KFOL.Owner.BasisObstruction.holds_of_variableCount_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.BasisObstruction.holds_of_variableCount_le

/-- info: 'KFOL.Owner.BasisObstruction.variableBound_ge_four' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.BasisObstruction.variableBound_ge_four

end KFOLTest.OwnerBasisObstruction
