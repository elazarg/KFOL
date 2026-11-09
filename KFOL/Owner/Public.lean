module

public import KFOL.Owner.Completeness
public import KFOL.Reset.Public

/-! # Explicit compilation of the guarded-owner signature into public syntax -/

@[expose] public section

namespace KFOL

universe u v

namespace WinnerSet

variable {Role : Type u}

@[simp] theorem guardedChoice_singleton (r i : Role) (A B : WinnerSet Role) :
    guardedChoice r (singleton i) A B = singleton i := reset_singleton _ _

@[simp] theorem guardedChoice_self (r : Role) (A : WinnerSet Role) :
    guardedChoice r A A A = A := by
  simp only [guardedChoice, choice_self, reset_self]

/-- The main-text example retains a genuine owner test: changing the side
atom from the owner to another root winner changes whether c is possible. -/
theorem guardedChoice_separates (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c ∉ (guardedChoice a ((singleton a).union (singleton b)) (singleton a) (singleton c)).val ∧
    c ∈ (guardedChoice a ((singleton a).union (singleton b)) (singleton b) (singleton c)).val := by
  have hroot : ((singleton a).union (singleton b)).Ambiguous :=
    ambiguous_of_two_mem _ a b hab (Or.inl rfl) (Or.inr rfl)
  constructor
  · simp [guardedChoice, mem_reset, mem_choice_other a c hac, hac.symm, hbc.symm]
  · simp [guardedChoice, mem_reset, mem_choice_other a c hac, hroot, hab.symm, hac.symm]

end WinnerSet

namespace Owner.Term

variable {Role : Type u} {Var : Type v}

/-- Expand reset and H into actual owned-choice syntax. Every duplicated
subterm is a separate syntactic occurrence, as in the paper. -/
def compile (three : Fin 3 ↪ Role) (roles : List Role) : Term Role Var → KFOL.Term Role Var
  | .var j => .var j
  | .func .reset args => Reset.Term.resetTerm three roles (compile three roles (args 0))
      (compile three roles (args 1))
  | .func (.guarded r) args => Reset.Term.resetTerm three roles
      (.choice r (compile three roles (args 1)) (compile three roles (args 2)))
      (compile three roles (args 0))

@[simp] theorem compile_step (three : Fin 3 ↪ Role) (roles : List Role) (s t : Term Role Var) :
    compile three roles (step s t) = Reset.Term.resetTerm three roles
      (compile three roles s) (compile three roles t) := rfl

@[simp] theorem compile_guarded (three : Fin 3 ↪ Role) (roles : List Role) (r : Role)
    (x y z : Term Role Var) : compile three roles (guarded r x y z) =
      Reset.Term.resetTerm three roles (.choice r (compile three roles y) (compile three roles z))
        (compile three roles x) := rfl

theorem eval_compile (three : Fin 3 ↪ Role) (roles : List Role) (covers : ∀ r, r ∈ roles)
    (t : Term Role Var) (v : Var → WinnerSet Role) : (compile three roles t).eval v = t.eval v := by
  induction t using induction_owner with
  | var => rfl
  | step s t hs ht => rw [compile_step, Reset.Term.eval_resetTerm three roles covers, hs, ht, eval_step]
  | guarded r x y z hx hy hz =>
    rw [compile_guarded, Reset.Term.eval_resetTerm three roles covers]
    change WinnerSet.guardedChoice r ((compile three roles x).eval v)
      ((compile three roles y).eval v) ((compile three roles z).eval v) = _
    rw [hx, hy, hz, eval_guarded]

theorem isCore_compile (three : Fin 3 ↪ Role) (roles : List Role) (t : Term Role Var) :
    (compile three roles t).IsCore := by
  induction t using induction_owner with
  | var => trivial
  | step s t hs ht => exact Reset.Term.isCore_resetTerm three roles _ _ hs ht
  | guarded r x y z hx hy hz => exact Reset.Term.isCore_resetTerm three roles _ _ ⟨hy, hz⟩ hx

end Owner.Term
end KFOL
