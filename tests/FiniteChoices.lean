module
import KFOL.Strategic.FiniteChoices
namespace KFOL.Tests.FiniteChoices
open KFOL.Strategic
private def branches : Fin 3 → Strategic.Tree (Fin 3) := fun i => .leaf i
example : FiniteChoice.possibleWinners (0 : Fin 3) branches = {0} := by
  classical
  rw [FiniteChoice.possibleWinners_eq,ite_eq_left ⟨0,by simp [branches]⟩]
example {Role Index : Type} [Fintype Index] [Nonempty Index]
    (owner : Role) (continuations : Index → Strategic.Tree Role) :
    ∃ binary : Strategic.Tree Role, possibleWinners binary = FiniteChoice.possibleWinners owner continuations :=
  FiniteChoice.exists_binary_tree owner continuations
/-- info: 'KFOL.Strategic.FiniteChoice.possibleWinners_eq_fold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Strategic.FiniteChoice.possibleWinners_eq_fold
end KFOL.Tests.FiniteChoices
