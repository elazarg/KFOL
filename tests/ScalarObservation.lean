module
import KFOL.Rounds.Scalar.PairFullAbstraction
namespace KFOL.Tests.ScalarObservation
open KFOL.Rounds.Game
open GameTheory.Languages.Bridges.FOSGToEFG

example : Countable ScalarTerm := inferInstance
example : Countable {probe : ScalarTerm // probe.UnaryGenerated} := inferInstance

/-- No scalar syntax, Boolean menus, or supplied uniqueness premise is
required of either component. The testing contexts alone are Boolean. -/
example (left right : KFOL.Rounds.Game (Fin 3))
    (hl : left.UsesOnly 0 1) (hr : right.UsesOnly 0 1) (order : ExplicitOrder (Fin 3)) :
    left.sequentialValues order = right.sequentialValues order ↔
      ∀ context : Context (Fin 3), context.BooleanMenus →
        ((2 : Fin 3) ∈ possibleWinners ((context.fill left).sequentialValues order) ↔
          (2 : Fin 3) ∈ possibleWinners ((context.fill right).sequentialValues order)) :=
  TwoPlayers.sequentialValues_eq_iff_boolean_observation left right 0 1 2
    (by decide) (by decide) (by decide) hl hr order

/-- The real-coordinate theorem is independent of component syntax. -/
example (left right : KFOL.Rounds.Game (Fin 3)) (order : ExplicitOrder (Fin 3))
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hl : left.sequentialValues order = {Scalar.distribution (0 : Fin 3) 1 x hx0 hx1})
    (hr : right.sequentialValues order = {Scalar.distribution (0 : Fin 3) 1 y hy0 hy1}) :
    x ≤ y ↔ ∀ probe : ScalarTerm, probe.UnaryGenerated → probe.rate < 1 →
      ((2 : Fin 3) ∈ possibleWinners ((publicChoice 0 right (probe.game 0 2)).sequentialValues order) →
        (2 : Fin 3) ∈ possibleWinners ((publicChoice 0 left (probe.game 0 2)).sequentialValues order)) :=
  Scalar.singleton_scalar_le_iff_rational_tests left right 0 1 2
    (by decide) (by decide) (by decide) order x y hx0 hx1 hy0 hy1 hl hr

/-- The threshold endpoint x=z belongs to the winning cut, including z=0. -/
example (order : ExplicitOrder (Fin 3)) :
    (2 : Fin 3) ∈ possibleWinners ((publicChoice 0 (.leaf 1) (.leaf 2)).sequentialValues order) := by
  apply (Scalar.third_possible_comparison_iff (.leaf 1) (.leaf 2) 0 1 2
    (by decide) (by decide) (by decide) order 0 0 le_rfl (by norm_num) le_rfl
    (by norm_num) ?_ ?_).2 le_rfl
  · simp only [Scalar.distribution_zero,sequentialValues_leaf]
  · simp only [Scalar.distribution_zero,sequentialValues_leaf]

#print axioms KFOL.Rounds.Game.instCountableScalarTerm
#print axioms Scalar.comparisonContext_booleanMenus
#print axioms Scalar.singleton_scalar_separator
#print axioms Scalar.singleton_third_boolean_full_abstraction
#print axioms Scalar.singleton_boolean_full_abstraction
#print axioms Scalar.third_possible_comparison_iff
#print axioms Scalar.singleton_scalar_le_iff_rational_tests
#print axioms Scalar.singleton_scalar_eq_iff_rational_tests
#print axioms TwoPlayers.sequentialValues_eq_iff_boolean_observation
#print axioms TwoPlayers.sequentialValues_eq_iff_rational_observation
#print axioms TwoPlayers.sequentialValues_eq_iff_boolean_winners
#print axioms Scalar.scalar_separator
#print axioms Scalar.scalar_third_full_abstraction
#print axioms Scalar.scalar_full_abstraction
end KFOL.Tests.ScalarObservation
