module

import KFOL.Rounds.Public.Nonconvex

open KFOL KFOL.Rounds.Game
open GameTheory.Languages.Bridges.FOSGToEFG
open GameTheory.Math.Probability

def order : ExplicitOrder (Fin 3) := ⟨3,Equiv.refl _⟩

-- The same public support theorem applies at K=2, using the shared tree and
-- round definitions without any global three-role assumption.
example (tree : Strategic.Tree (Fin 2)) :
    possibleWinners ((publicTree tree).sequentialValues ⟨2,Equiv.refl _⟩) =
      (Strategic.value tree).val := possibleWinners_publicTree tree _

-- A distribution omitted by one concrete tree is present in two independently
-- chosen copies; this exercises the distribution observation rather than the
-- weaker winner-set equality proved separately.
example :
    let midpoint := mix (1/2 : ℝ) (by norm_num) (by norm_num)
      (PMF.pure (0 : Fin 3)) (PMF.pure 2)
    midpoint ∉ (Public.nonconvexTree 0 1 2).sequentialValues order ∧
    midpoint ∈ (publicChoice 1 (Public.nonconvexTree 0 1 2)
      (Public.nonconvexTree 0 1 2)).sequentialValues order :=
  ⟨Public.midpoint_not_mem_example 0 1 2 (by decide) (by decide) (by decide) order,
    Public.midpoint_mem_repeated_example 0 1 2 (by decide) (by decide) (by decide) order⟩

/-- info: 'KFOL.Rounds.Game.possibleWinners_publicTree' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Rounds.Game.possibleWinners_publicTree

/-- info: 'KFOL.Rounds.Game.Public.midpoint_mem_repeated_example' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Rounds.Game.Public.midpoint_mem_repeated_example
