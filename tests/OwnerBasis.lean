module

public import KFOL.Owner.Basis

@[expose] public section

namespace KFOLTest.OwnerBasis

open KFOL.Owner.FiniteBasis

example : (basisAxiom 21).variableCount = 6 := by decide
example : (basisAxiom 0).variableCount = 1 := by decide


example : theory.ncard = 36 := theory_ncard
example : Function.Injective basisAxiom := basisAxiom_injective

/-- The removed projection and action equations remain derivable laws,
not additional fields of the thirty-six-law assumptions. -/
example {M : Type*} {f : M → M → M} {h : M → M → M → M}
    (laws : Laws f h) (r a u : M) :
    f (f u r) r = f u r ∧ f (f r a) r = f a r ∧
      h r (f r a) u = h r a u ∧ f (f u a) r = f (f (f u r) a) r :=
  ⟨laws.project_idem r u, laws.G_zero r a, laws.F_zero r a u, laws.reset_back r a u⟩

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

/-- info: 'KFOL.Owner.FiniteBasis.basisAxiom_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.basisAxiom_injective

/-- info: 'KFOL.Owner.FiniteBasis.theory_ncard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.theory_ncard

/-- info: 'KFOL.Owner.FiniteBasis.Laws.project_idem' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.Laws.project_idem

/-- info: 'KFOL.Owner.FiniteBasis.Laws.G_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.Laws.G_zero

/-- info: 'KFOL.Owner.FiniteBasis.Laws.F_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.Laws.F_zero

/-- info: 'KFOL.Owner.FiniteBasis.Laws.reset_back' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.Laws.reset_back

end KFOLTest.OwnerBasis
