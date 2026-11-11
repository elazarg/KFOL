module

public import KFOL.Definitions.Public
public import Mathlib.Data.Set.Card

/-! # Occurrence counts and winner losses for the full syntax -/

@[expose] public section

namespace KFOL.Term

universe u v
variable {Role : Type u} {Var : Type v}

/-- Binary choices, ignoring unary permutations. -/
def choiceCount : Term Role Var → ℕ
  | .winner _ | .var _ => 0
  | .choice _ s t => s.choiceCount + t.choiceCount + 1
  | .rename _ t => t.choiceCount

/-- Sum of the sizes supplied at leaf occurrences; repeated inputs count again. -/
noncomputable def leafMass (ν : Var → WinnerSet Role) : Term Role Var → ℕ
  | .winner _ => 1
  | .var x => (ν x).val.ncard
  | .choice _ s t => s.leafMass ν + t.leafMass ν
  | .rename _ t => t.leafMass ν

/-- Ambiguity supplied by input occurrences beyond their mandatory one winner. -/
noncomputable def inputExcess (ν : Var → WinnerSet Role) : Term Role Var → ℕ
  | .winner _ => 0
  | .var x => (ν x).val.ncard - 1
  | .choice _ s t => s.inputExcess ν + t.inputExcess ν
  | .rename _ t => t.inputExcess ν

/-- Intersection losses summed over evaluated binary choices. -/
noncomputable def overlapLoss (ν : Var → WinnerSet Role) : Term Role Var → ℕ
  | .winner _ | .var _ => 0
  | .choice _ s t => s.overlapLoss ν + t.overlapLoss ν +
      ((s.eval ν).val ∩ (t.eval ν).val).ncard
  | .rename _ t => t.overlapLoss ν

/-- Winners removed from the union at absorbing choices. -/
noncomputable def absorptionLoss (ν : Var → WinnerSet Role) : Term Role Var → ℕ
  | .winner _ | .var _ => 0
  | .choice r s t => s.absorptionLoss ν + t.absorptionLoss ν +
      if s.eval ν = WinnerSet.singleton r ∨ t.eval ν = WinnerSet.singleton r
      then ((s.eval ν).val ∪ (t.eval ν).val).ncard - 1 else 0
  | .rename _ t => t.absorptionLoss ν

/-- Number of absorbing choices under this valuation. -/
noncomputable def absorbingCount (ν : Var → WinnerSet Role) : Term Role Var → ℕ
  | .winner _ | .var _ => 0
  | .choice r s t => s.absorbingCount ν + t.absorbingCount ν +
      if s.eval ν = WinnerSet.singleton r ∨ t.eval ν = WinnerSet.singleton r
      then 1 else 0
  | .rename _ t => t.absorbingCount ν

/-- Every choice takes a disjoint union without absorption. -/
def DisjointChoices (ν : Var → WinnerSet Role) : Term Role Var → Prop
  | .winner _ | .var _ => True
  | .choice r s t => s.DisjointChoices ν ∧ t.DisjointChoices ν ∧
      ¬(s.eval ν = WinnerSet.singleton r ∨ t.eval ν = WinnerSet.singleton r) ∧
      Disjoint (s.eval ν).val (t.eval ν).val
  | .rename _ t => t.DisjointChoices ν

end KFOL.Term
