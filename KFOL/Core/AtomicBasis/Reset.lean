module

public import KFOL.Core.AtomicBasis.Presentation
public import KFOL.Reset.Public
public import Mathlib.Data.List.Fold

/-! # The displayed core reset term denotes the paper's semantic reset -/

@[expose] public section

namespace KFOL.Core.AtomicBasis

universe u

variable {Role : Type u}

/-- The core fold is exactly semantic reset, for every covering enumeration. -/
theorem winner_reset (three : Fin 3 ↪ Role) (rs : List Role) (covers : ∀ r, r ∈ rs)
    (A B : WinnerSet Role) :
    letI := Equational.coreStructure Role
    reset three rs A B = A.reset B := by
  let _ := Equational.coreStructure Role
  have fold (xs : List Role) {Var : Type} (acc base : KFOL.Term Role Var)
      (v : Var → WinnerSet Role) :
      (KFOL.Term.suppress xs acc base).eval v =
        xs.foldr (fun r x => WinnerSet.choice r (base.eval v) x) (acc.eval v) := by
    induction xs with
    | nil => rfl
    | cons r xs ih =>
      change WinnerSet.choice r ((KFOL.Term.suppress xs acc base).eval v) (base.eval v) = _
      rw [ih, WinnerSet.choice_comm]
      rfl
  have he := Reset.Term.eval_resetTerm three rs.reverse (fun r => by simpa using covers r)
    (.var (0 : Fin 2)) (.var 1) ![A, B]
  rw [Reset.Term.resetTerm, fold, KFOL.Term.eval_unionTerm] at he
  unfold reset
  rw [join_winner, List.foldl_eq_foldr_reverse]
  exact he

end KFOL.Core.AtomicBasis
