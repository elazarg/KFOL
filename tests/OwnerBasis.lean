module

public import KFOL.Owner.Basis

@[expose] public section

namespace KFOLTest.OwnerBasis

open KFOL.Owner.FiniteBasis

example : (basisAxiom 23).variableCount = 6 := by decide
example : (basisAxiom 0).variableCount = 1 := by decide

/-- info: 'KFOL.Owner.FiniteBasis.basisAxiom_holds' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.basisAxiom_holds

/-- info: 'KFOL.Owner.FiniteBasis.models_theory_iff' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.models_theory_iff

/-- info: 'KFOL.Owner.FiniteBasis.Laws.word_normal_form' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.Laws.word_normal_form

/-- info: 'KFOL.Owner.FiniteBasis.Laws.two_source_absorption' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.Laws.two_source_absorption

/-- info: 'KFOL.Owner.FiniteBasis.isBasis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.isBasis

/-- info: 'KFOL.Owner.FiniteBasis.isBasis_winnerSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.isBasis_winnerSet

/-- info: 'KFOL.Owner.FiniteBasis.variableBound_ge_four_winnerSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.variableBound_ge_four_winnerSet

end KFOLTest.OwnerBasis
