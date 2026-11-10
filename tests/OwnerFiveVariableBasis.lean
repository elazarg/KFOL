module

public import KFOL.Owner.Basis.Exchange
public import KFOL.Owner.FourVariableObstruction

@[expose] public section
namespace KFOLTest.OwnerFiveVariableBasis
open KFOL Owner.FiniteBasis

-- The presentation has an exact cardinality and an actual-support bound,
-- independent of the retained padded arities in the other thirty-five laws.
example : (Set.range fiveVariableAxiom).ncard = 36 := FiveVariables.theory_ncard
example : (fiveVariableAxiom 21).arity = 5 ∧
    (fiveVariableAxiom 21).variableCount = 5 := by decide
example : (fiveVariableAxiom 10).arity = 6 ∧
    (fiveVariableAxiom 10).variableCount = 5 := by decide
example : Equational.HasVariableBound fiveVariableTheory 5 := FiveVariables.variable_bound

-- The original action presentation and its six-variable law remain available.
example : (basisAxiom 21).variableCount = 6 := by decide
example {M : Type*} [(Equational.language (Owner.Symbol Unit)).Structure M]
    (hm : Equational.Models fiveVariableTheory M) : Equational.Models theory M :=
  FiveVariables.models_old hm

example : letI := Owner.fourStructure (Role := Unit);
    Equational.IsBasis Owner.Four fiveVariableTheory := FiveVariables.isBasis

/-- info: 'KFOL.Owner.FiniteBasis.FiveVariables.isBasis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.FiveVariables.isBasis

end KFOLTest.OwnerFiveVariableBasis
