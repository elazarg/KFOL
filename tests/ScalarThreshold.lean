module

import KFOL.Rounds.Scalar.Contexts

namespace KFOL.Tests.ScalarThreshold
open KFOL.Rounds KFOL.Rounds.Game KFOL.Rounds.Game.Scalar
open GameTheory.Languages.Bridges.FOSGToEFG

universe u v
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- Complete main-paper threshold statement against canonical serial SE. -/
theorem actual_threshold (a b c : Role) (hab : a ≠ b) (hac : a ≠ c)
    (n m : ℕ) (order : ExplicitOrder Role) :
    possibleWinners ((threshold a b c n m).sequentialValues order) =
      if n < m then {a,b} else if n = m then {a,b,c} else {a,c} :=
  possibleWinners_threshold a b c hab hac n m order

example (order : ExplicitOrder (Fin 3)) :
    possibleWinners ((threshold (0:Fin 3) 1 2 0 1).sequentialValues order) = {0,1} := by
  simpa using actual_threshold (0:Fin 3) 1 2 (by decide) (by decide) 0 1 order

example (order : ExplicitOrder (Fin 3)) :
    possibleWinners ((threshold (0:Fin 3) 1 2 0 0).sequentialValues order) = {0,1,2} := by
  simpa using actual_threshold (0:Fin 3) 1 2 (by decide) (by decide) 0 0 order

example (order : ExplicitOrder (Fin 3)) :
    possibleWinners ((threshold (0:Fin 3) 1 2 1 0).sequentialValues order) = {0,2} := by
  simpa using actual_threshold (0:Fin 3) 1 2 (by decide) (by decide) 1 0 order

/-- The obstruction uses actual games/contexts and arbitrary finite carriers. -/
example (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : ExplicitOrder Role) {Summary : Type v} [Finite Summary]
    (encode : Game Role → Summary)
    (adequate : ∀ (left right : Game Role), encode left = encode right → ∀ context : Context Role,
      (c ∈ possibleWinners ((context.fill left).sequentialValues order) ↔
        c ∈ possibleWinners ((context.fill right).sequentialValues order))) : False :=
  no_finite_contextual_summary a b c hab hac hbc order encode adequate

#print axioms actual_threshold
#print axioms no_finite_winner_algebra
#print axioms no_finite_contextual_summary

end KFOL.Tests.ScalarThreshold
