module

public import KFOL.Reset.Selection
public import KFOL.Algebra.TestDomains

/-! # Compile reset terms to the shared owned-choice core

Reset is primitive for its algorithms and equational signature. This explicit
compilation proves its connection to the public-game algebra independently.
-/

@[expose] public section

namespace KFOL.Reset.Term

universe u v

variable {Role : Type u} {Var : Type v}

/-- First union, then suppress once for every role in the supplied list. -/
def resetTerm (three : Fin 3 ↪ Role) (roles : List Role)
    (s t : KFOL.Term Role Var) : KFOL.Term Role Var :=
  KFOL.Term.suppress roles (KFOL.Term.unionTerm three s t) t

theorem eval_resetTerm (three : Fin 3 ↪ Role) (roles : List Role)
    (covers : ∀ r, r ∈ roles) (s t : KFOL.Term Role Var) (v : Var → WinnerSet Role) :
    (resetTerm three roles s t).eval v = (s.eval v).reset (t.eval v) := by
  classical
  by_cases h : (t.eval v).Ambiguous
  · rw [WinnerSet.reset_of_ambiguous _ _ h]
    have he := KFOL.Term.eval_suppress_ambiguous roles (KFOL.Term.unionTerm three s t) t v h
      (by simp only [KFOL.Term.eval_unionTerm]; exact Set.subset_union_right)
    exact he.trans (KFOL.Term.eval_unionTerm three s t v)
  · obtain ⟨r, hr⟩ : ∃ r, t.eval v = WinnerSet.singleton r := by
      simpa only [WinnerSet.Ambiguous, not_forall, not_not] using h
    rw [hr, WinnerSet.reset_singleton]
    exact KFOL.Term.eval_suppress_atom roles _ t v r (covers r) hr

private theorem isCore_suppress (roles : List Role) (s t : KFOL.Term Role Var)
    (hs : s.IsCore) (ht : t.IsCore) : (KFOL.Term.suppress roles s t).IsCore := by
  induction roles with
  | nil => exact hs
  | cons r rest ih => exact ⟨ih, ht⟩

theorem isCore_resetTerm (three : Fin 3 ↪ Role) (roles : List Role)
    (s t : KFOL.Term Role Var) (hs : s.IsCore) (ht : t.IsCore) :
    (resetTerm three roles s t).IsCore :=
  isCore_suppress roles _ _ ⟨⟨hs, ht⟩, ⟨hs, ht⟩⟩ ht

/-- Every reset node expands into actual owned choices; repeated subterms are
independent syntactic copies in the native public language. -/
def compile (three : Fin 3 ↪ Role) (roles : List Role) : Term Var → KFOL.Term Role Var
  | .var j => .var j
  | .func .reset args => resetTerm three roles (compile three roles (args 0))
      (compile three roles (args 1))

@[simp] theorem compile_step (three : Fin 3 ↪ Role) (roles : List Role) (s t : Term Var) :
    compile three roles (step s t) =
      resetTerm three roles (compile three roles s) (compile three roles t) := rfl

theorem isCore_compile (three : Fin 3 ↪ Role) (roles : List Role) (t : Term Var) :
    (compile three roles t).IsCore := by
  induction t using induction_reset with
  | var => trivial
  | step s t hs ht => exact isCore_resetTerm three roles _ _ hs ht

/-- The expansion agrees on every valuation, including mixed atomic inputs. -/
theorem eval_compile (three : Fin 3 ↪ Role) (roles : List Role) (covers : ∀ r, r ∈ roles)
    (t : Term Var) (v : Var → WinnerSet Role) : (compile three roles t).eval v = t.eval v := by
  induction t using induction_reset with
  | var => rfl
  | step s t hs ht => rw [compile_step, eval_resetTerm three roles covers, hs, ht, eval_step]

end KFOL.Reset.Term
