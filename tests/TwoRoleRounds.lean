module

import KFOL.Rounds.TwoPlayers.Support

namespace KFOL.Tests.TwoRoleRounds
open KFOL.Rounds KFOL.Rounds.Game KFOL.Rounds.Game.TwoPlayers
open GameTheory.Languages.Bridges.FOSGToEFG

/-- The complete finite-menu report statement, with actual child readouts
proved to exist and the actual parent canonical SE winner observation. -/
theorem actual_round_folds (sizes : Fin 2 → ℕ)
    (next : ((i : Fin 2) → Fin (sizes i+1)) → Game (Fin 2))
    (order : ExplicitOrder (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2),
      (∀ actions, (g actions).val = possibleWinners ((next actions).sequentialValues order)) ∧
      let Sa := WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
        WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
          g (matrixAction sizes row col)
      let Sb := WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
        WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
          g (matrixAction sizes row col)
      possibleWinners ((Game.round sizes next).sequentialValues order) = (Sa.union Sb).val ∧
        Sa.union Sb = WinnerSet.choice 1 (WinnerSet.choice 0 Sa
          ((WinnerSet.singleton 0).union (WinnerSet.singleton 1))) Sb :=
  exists_round_support_folds sizes next order

/-- Singleton menus, with no effective commitments, are included. -/
example (order : ExplicitOrder (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin (0+1)) → WinnerSet (Fin 2),
      ∀ actions, (g actions).val = possibleWinners ((Game.leaf 0).sequentialValues order) :=
  exists_child_winnerSets (fun _ => 0) (fun _ => .leaf 0) order

/-- Three-row versus one-column actual menus use the same theorem, with no
Boolean padding or separate fixed-arity interpretation. -/
example (order : ExplicitOrder (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin ((if i=0 then 2 else 0)+1)) → WinnerSet (Fin 2),
      ∀ actions, (g actions).val = possibleWinners
        ((if (actions 0).val=0 then Game.leaf 0 else Game.leaf 1).sequentialValues order) :=
  exists_child_winnerSets (fun i => if i=0 then 2 else 0)
    (fun actions => if (actions 0).val=0 then .leaf 0 else .leaf 1) order

example (context : Context (Fin 2)) (left right : Game (Fin 2))
    (order : ExplicitOrder (Fin 2))
    (heq : possibleWinners (left.sequentialValues order) =
      possibleWinners (right.sequentialValues order)) :
    possibleWinners ((context.fill left).sequentialValues order) =
      possibleWinners ((context.fill right).sequentialValues order) :=
  possibleWinners_context_congr context left right order heq

#print axioms actual_round_folds
#print axioms possibleWinners_context_congr
#print axioms WinnerSet.choiceFold_eq_other_iff

end KFOL.Tests.TwoRoleRounds
