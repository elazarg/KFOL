module

import KFOL.Rounds.Scalar.Reciprocal

namespace KFOL.Tests.ScalarDiagonal
open KFOL.Rounds KFOL.Rounds.Game KFOL.Rounds.Game.Scalar
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Complete semantic regression: the actual serial game, not a scalar
certificate, has the claimed unique canonical SE winner law. -/
theorem actual_diagonal (a b : Role) (hab : a ≠ b) (left right : Game Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (order : ExplicitOrder Role)
    (hleft : left.sequentialValues order = {distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {distribution a b y hy0 hy1}) :
    (diagonal a b left right).sequentialValues order =
      {distribution a b (x*y/(x+y)) (parallel_nonneg x y hx0 hy0)
        (parallel_le_one x y hx0 hx1 hy0)} :=
  sequentialValues_diagonal a b hab left right x y hx0 hx1 hy0 hy1 order hleft hright

example (order : ExplicitOrder (Fin 3)) :
    (diagonal (0:Fin 3) 1 (.leaf 1) (.leaf 1)).sequentialValues order = {PMF.pure 1} := by
  simpa using sequentialValues_diagonal (0:Fin 3) 1 (by decide) (.leaf 1) (.leaf 1)
    0 0 le_rfl (by norm_num) le_rfl (by norm_num) order
    (by simpa using sequentialValues_leaf (Role := Fin 3) 1 order)
    (by simpa using sequentialValues_leaf (Role := Fin 3) 1 order)

example (order : ExplicitOrder (Fin 3)) :
    (reciprocal (0:Fin 3) 1 0).sequentialValues order = {PMF.pure 0} := by
  simpa [reciprocalDistribution,distribution] using
    sequentialValues_reciprocal (0:Fin 3) 1 (by decide) 0 order

example : (reciprocalDistribution (0:Fin 3) 1 1 0).toReal = 1/2 := by
  norm_num

example : (reciprocalDistribution (0:Fin 3) 1 2 1).toReal = 2/3 := by
  norm_num

#print axioms actual_diagonal
#print axioms observedValues_reciprocal
#print axioms sequentialValues_reciprocal

end KFOL.Tests.ScalarDiagonal
