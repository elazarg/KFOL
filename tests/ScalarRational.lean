module

import KFOL.Rounds.Scalar.FullAbstraction
import KFOL.Rounds.Scalar.Fragment

namespace KFOL.Tests.ScalarRational
open KFOL.Rounds KFOL.Rounds.Game KFOL.Rounds.Game.Scalar
open GameTheory.Languages.Bridges.FOSGToEFG

universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- The complete single-observer full-abstraction statement. -/
theorem actual_scalar_full_abstraction (left right : ScalarTerm) (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (order : ExplicitOrder Role) :
    left.rate = right.rate ↔ ∀ context : Context Role,
      (c ∈ possibleWinners ((context.fill (left.game a b)).sequentialValues order) ↔
        c ∈ possibleWinners ((context.fill (right.game a b)).sequentialValues order)) :=
  scalar_third_full_abstraction left right a b c hab hac hbc order

/-- Synthesis returns an actual C/U-only component with the actual canonical
SE singleton, even when the input fraction is not reduced. -/
example (order : ExplicitOrder (Fin 3)) :
    ∃ term : ScalarTerm, term.UnaryGenerated ∧
      (term.game (0:Fin 3) 1).sequentialValues order =
        {distribution (0:Fin 3) 1 (2/6:ℝ) (by norm_num) (by norm_num)} := by
  simpa only [Rat.cast_div,Rat.cast_ofNat] using
    exists_rational_game (0:Fin 3) 1 (by decide) (2/6) (by norm_num) (by norm_num) order

example : (ScalarTerm.complement (.diagonal (.diagonal .one .one) .one)).rate = 2/3 := by
  norm_num [ScalarTerm.rate]

example : (ScalarTerm.sup .zero (.inf .one (.diagonal .one .one))).rate = 1/2 := by
  norm_num [ScalarTerm.rate]

example (order : ExplicitOrder (Fin 3)) :
    ∃ context : Context (Fin 3),
      (2:Fin 3) ∈ possibleWinners ((context.fill (ScalarTerm.zero.game 0 1)).sequentialValues order) ∧
      (2:Fin 3) ∉ possibleWinners ((context.fill (ScalarTerm.one.game 0 1)).sequentialValues order) := by
  exact scalar_separator .zero .one (0:Fin 3) 1 2 (by decide) (by decide) (by decide) order
    (by norm_num [ScalarTerm.rate])

example (term : ScalarTerm) : (term.game (0:Fin 4) 1).UsesOnly 0 1 :=
  term.usesOnly_game 0 1

example (term : ScalarTerm) : (term.game (0:Fin 4) 1).BooleanMenus :=
  term.booleanMenus_game 0 1

example (n m : ℕ) : (threshold (0:Fin 4) 1 2 n m).BooleanMenus :=
  booleanMenus_threshold 0 1 2 n m

#print axioms actual_scalar_full_abstraction
#print axioms ScalarTerm.synthesize
#print axioms exists_rational_game
#print axioms scalar_full_abstraction

end KFOL.Tests.ScalarRational
