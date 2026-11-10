module

public import KFOL.Definitions.Rounds
public import KFOL.Definitions.Quantified
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic
public import KFOL.Algebra.Semilattice

/-! # Mathematical vocabulary for public games and sealed rounds

`Game.value` is defined by actual sequential equilibria, with a fixed player
schedule. Independence of that schedule is a theorem, not part of its meaning.
The summary interface specifies actual Boolean games, composition and the
possible-win observation; it contains no impossibility assertion.
-/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game

universe u v
variable {Role : Type u} [Fintype Role] [DecidableEq Role]

/-- Fix one serialization schedule; every role occurs once. -/
def playerOrder (Role : Type u) [Fintype Role] :
    GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role :=
  ⟨Fintype.card Role,(Fintype.equivFin Role).symm⟩

/-- E(G): winner distributions of behavioral sequential equilibria of the
serial commitment implementation. -/
def value (game : Game Role) : Set (PMF Role) := game.sequentialValues (playerOrder Role)

/-- A component has the unique law x δ_a + (1-x) δ_b. -/
def HasScalarValue (game : Game Role) (a b : Role) (x : ℝ) : Prop :=
  ∃ (h0 : 0 ≤ x) (h1 : x ≤ 1), game.value = {Scalar.distribution a b x h0 h1}

/-- Contextual equivalence for one role's possible victory. Context holes
are filled independently, including repeated occurrences. -/
def ContextuallyEquivalent (observer : Role) (left right : Game Role) : Prop :=
  ∀ context : Context Role,
    observer ∈ possibleWinners (context.fill left).value ↔
      observer ∈ possibleWinners (context.fill right).value

/-- Equal possible-winner sets in every round context. -/
def SameContextualWinners (left right : Game Role) : Prop :=
  ∀ context : Context Role,
    possibleWinners (context.fill left).value = possibleWinners (context.fill right).value

/-- The average of two winner laws. -/
def midpointLaw (left right : PMF Role) : PMF Role :=
  GameTheory.Math.Probability.mix (1/2 : ℝ) (by norm_num) (by norm_num) left right

/-- A finite-algebra candidate for Boolean-menu games. Even this minimal
interface asks only for public choice by one owner and one win observation. -/
structure WinnerSummary (owner observer : Role) (Carrier : Type v) where
  encode : {game : Game Role // game.BooleanMenus} → Carrier
  choose : Carrier → Carrier → Carrier
  observation : Carrier → Prop
  composition : ∀ left right result, result.val = publicChoice owner left.val right.val →
    encode result = choose (encode left) (encode right)
  adequacy : ∀ game, observation (encode game) ↔ observer ∈ possibleWinners game.val.value

end KFOL.Rounds.Game

namespace KFOL.Rounds.Game.TwoPlayers

/-- The actual pair of menu choices, without a padded or duplicated action. -/
def matrixAction (sizes : Fin 2 → Nat) (row : Fin (sizes 0+1)) (col : Fin (sizes 1+1)) :
    (i : Fin 2) → Fin (sizes i+1) :=
  (piFinTwoEquiv (fun i => Fin (sizes i+1))).symm (row,col)

/-- The literal public serialization in which player zero commits first. -/
def serialZero (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) : WinnerSet (Fin 2) :=
  WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
    WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
      g (matrixAction sizes row col)

/-- The literal public serialization in which player one commits first. -/
def serialOne (sizes : Fin 2 → ℕ)
    (g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2)) : WinnerSet (Fin 2) :=
  WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
    WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
      g (matrixAction sizes row col)

end KFOL.Rounds.Game.TwoPlayers
