module
import KFOL.Rounds.Scalar.BooleanInfinite
import KFOL.Rounds.Scalar.Security
namespace KFOL.Tests.BooleanRoundSummary
open KFOL.Rounds.Game
open GameTheory.Languages.Bridges.FOSGToEFG

/-- The semantics has no domain outside Boolean games. Only actual Boolean
public contexts are required, so no extension hypothesis is available. -/
example (order : ExplicitOrder (Fin 3)) {Summary : Type} [Finite Summary]
    (encode : {game : KFOL.Rounds.Game (Fin 3) // game.BooleanMenus} → Summary)
    (adequate : ∀ left right, encode left = encode right →
      ∀ context : Context (Fin 3), context.BooleanMenus →
        ((2 : Fin 3) ∈ possibleWinners ((context.fill left.val).sequentialValues order) ↔
          (2 : Fin 3) ∈ possibleWinners ((context.fill right.val).sequentialValues order))) : False :=
  Scalar.no_finite_boolean_contextual_summary 0 1 2 (by decide) (by decide) (by decide)
    order encode adequate

example (game : KFOL.Rounds.Game (Fin 3)) (hg : game.BooleanMenus)
    (context : Context (Fin 3)) (hc : context.BooleanMenus) :
    (context.fill game).BooleanMenus := hc.fill hg

example (n : ℕ) : (Scalar.thresholdContext (0 : Fin 3) 2 n).BooleanMenus :=
  Scalar.thresholdContext_booleanMenus _ _ _

/-- Literal action-zero probabilities and the actual stage payoff, without
an equilibrium premise or an abstract matrix certificate. -/
example (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hpos : 0 < x+y) :
    ∃ (row : PMF (Fin (binarySizes (0 : Fin 3) 1 0+1)))
      (col : PMF (Fin (binarySizes (0 : Fin 3) 1 1+1))),
      (row 0).toReal = y/(x+y) ∧ (col 0).toReal = y/(x+y) ∧
      ∀ profile : (i : Fin 3) → PMF (Fin (binarySizes (0 : Fin 3) 1 i+1)),
        ((stageForm (binarySizes (0 : Fin 3) 1) (Scalar.diagonalTable (0 : Fin 3) 1
          (Scalar.distribution (0 : Fin 3) 1 x hx0 hx1) (Scalar.distribution (0 : Fin 3) 1 y hy0 hy1))).mixed.play
            (GameTheory.Profile.update (sig := {Strategy := fun i : Fin 3 => PMF (Fin (binarySizes (0 : Fin 3) 1 i+1)), Outcome := Fin 3}) profile 0 row) (0 : Fin 3)).toReal = x*y/(x+y) ∧
        ((stageForm (binarySizes (0 : Fin 3) 1) (Scalar.diagonalTable (0 : Fin 3) 1
          (Scalar.distribution (0 : Fin 3) 1 x hx0 hx1) (Scalar.distribution (0 : Fin 3) 1 y hy0 hy1))).mixed.play
            (GameTheory.Profile.update (sig := {Strategy := fun i : Fin 3 => PMF (Fin (binarySizes (0 : Fin 3) 1 i+1)), Outcome := Fin 3}) profile 1 col) (0 : Fin 3)).toReal = x*y/(x+y) :=
  Scalar.diagonal_security (0 : Fin 3) 1 (by decide) x y hx0 hx1 hy0 hy1 hpos

#print axioms Scalar.no_finite_boolean_winner_algebra
#print axioms Scalar.no_finite_boolean_contextual_summary
#print axioms Scalar.diagonal_security
end KFOL.Tests.BooleanRoundSummary
