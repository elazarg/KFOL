module

public import KFOL.Definitions.Atomic

/-! # Possible winners under single-winner input valuations -/

@[expose] public section

namespace KFOL.Term

universe u v

/-- A specified role wins under some valuation assigning one winner per input.
This uses the original evaluator, independently of a verifier or reduction. -/
def AtomicPossibleWin {Role : Type u} {Var : Type v}
    (term : Term Role Var) (winner : Role) : Prop :=
  ∃ valuation : Var → Role,
    winner ∈ (term.eval (fun name => WinnerSet.singleton (valuation name))).val

end KFOL.Term
