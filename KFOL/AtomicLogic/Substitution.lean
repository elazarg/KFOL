module

public import KFOL.AtomicLogic.Completeness
public import KFOL.Definitions.Atomic

/-! # Admissible substitutions in the atomic-input logic -/

@[expose] public section

namespace KFOL.AtomicLogic

universe u v w

/-- A native substitution is sound for atomic validity when all its images
are atom-preserving; intermediate winner terms remain unrestricted. -/
theorem valid_subst {Role : Type u} {Var : Type v} {Var' : Type w}
    {s t : KFOL.Term Role Var} (h : Valid s t)
    (replacement : Var → KFOL.Term Role Var')
    (atomic : ∀ x, (replacement x).AtomPreserving) :
    Valid (s.subst replacement) (t.subst replacement) := by
  classical
  intro valuation
  let v x := Classical.choose (atomic x valuation)
  have hv :
      (fun x => (replacement x).eval (fun y => WinnerSet.singleton (valuation y))) =
      (fun x => WinnerSet.singleton (v x)) :=
    funext (fun x => Classical.choose_spec (atomic x valuation))
  rw [KFOL.Term.eval_subst, KFOL.Term.eval_subst, hv]
  exact h v

/-- The whole semantic class of atom-preserving substitutions is admissible
in the finite sorted presentation. -/
theorem derives_subst_atom_preserving {Role : Type u} {n m : ℕ}
    {s t : KFOL.Term Role (Fin n)}
    (h : Derives (WinnerTerm.ofNative s) (WinnerTerm.ofNative t))
    (replacement : Fin n → KFOL.Term Role (Fin m))
    (atomic : ∀ x, (replacement x).AtomPreserving) :
    Derives (WinnerTerm.ofNative (s.subst replacement))
      (WinnerTerm.ofNative (t.subst replacement)) :=
  derives_of_valid _ _ (valid_subst (valid_of_derives h) replacement atomic)

end KFOL.AtomicLogic
