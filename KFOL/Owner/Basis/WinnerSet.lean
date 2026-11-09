module

public import KFOL.Owner.GuardEncoding
public import KFOL.Owner.Basis.Completeness
public import KFOL.Owner.BasisObstruction

/-! The forty native equations are a basis of the intended one-owner
winner-set algebra, on every carrier with at least three roles. -/

@[expose] public section

namespace KFOL.Owner

universe u v

namespace Term

variable {Role : Type u} {Var : Type v}

theorem ownersIn_withOwner (owner : Role) (t : Term Unit Var) :
    (t.withOwner owner).OwnersIn (fun a => a = owner) := by
  induction t using induction_owner with
  | var => trivial
  | step s t hs ht => exact ⟨hs, ht⟩
  | guarded a x y z hx hy hz => exact ⟨rfl, hx, hy, hz⟩

theorem evalFour_withOwner (owner : Role) (t : Term Unit Var) (v : Var → Four) :
    (t.withOwner owner).evalFour v = t.evalFour v := by
  induction t using induction_owner with
  | var => rfl
  | step s t hs ht => simp only [withOwner_step, evalFour_step, hs, ht]
  | guarded a x y z hx hy hz =>
    cases a
    simp only [withOwner_guarded, evalFour_guarded, hx, hy, hz]

theorem realize_oneOwner_var (owner : Role) (j : Var) (v : Var → WinnerSet Role) :
    letI := oneOwnerStructure owner
    (.var j : Term Unit Var).realize v = v j := rfl

theorem realize_oneOwner_step (owner : Role) (s t : Term Unit Var) (v : Var → WinnerSet Role) :
    letI := oneOwnerStructure owner
    (step s t).realize v = (s.realize v).reset (t.realize v) := rfl

theorem realize_oneOwner_guarded (owner : Role) (s t q : Term Unit Var) (v : Var → WinnerSet Role) :
    letI := oneOwnerStructure owner
    (guarded () s t q).realize v = WinnerSet.guardedChoice owner (s.realize v) (t.realize v) (q.realize v) := rfl

/-- The label transport realizes the independently interpreted Unit signature. -/
theorem eval_withOwner (owner : Role) (t : Term Unit Var) (v : Var → WinnerSet Role) :
    letI := oneOwnerStructure owner
    (t.withOwner owner).eval v = t.realize v := by
  let _ := oneOwnerStructure owner
  induction t using induction_owner with
  | var => rfl
  | step s t hs ht =>
    rw [withOwner_step, eval_step, realize_oneOwner_step, hs, ht]
  | guarded a x y z hx hy hz =>
    cases a
    rw [withOwner_guarded, eval_guarded, realize_oneOwner_guarded, hx, hy, hz]

end Term

namespace FiniteBasis

/-- Exact identity-theory equivalence for the fixed one-owner native signature,
with no conditional outside theorem or representation premise. -/
theorem winnerSet_holds_iff_four {Role : Type u} (three : Fin 3 ↪ Role)
    (owner observer : Role) (ho : observer ≠ owner) (e : Equational.Identity (Symbol Unit)) :
    (letI := oneOwnerStructure owner; e.Holds (WinnerSet Role)) ↔
      (letI := fourStructure (Role := Unit); e.Holds Four) := by
  classical
  have h := Term.four_element_complete three (Term.withOwner owner e.lhs) (Term.withOwner owner e.rhs) owner observer ho
    (Term.ownersIn_withOwner owner e.lhs) (Term.ownersIn_withOwner owner e.rhs)
  let _ := oneOwnerStructure owner
  change (∀ v : Fin e.arity → WinnerSet Role, e.lhs.realize v = e.rhs.realize v) ↔
    ∀ w : Fin e.arity → Four, Term.evalFour e.lhs w = Term.evalFour e.rhs w
  constructor
  · intro he w
    have hws : ∀ v : Fin e.arity → WinnerSet Role,
        (Term.withOwner owner e.lhs).eval v = (Term.withOwner owner e.rhs).eval v := by
      intro v
      rw [Term.eval_withOwner, Term.eval_withOwner]
      exact he v
    calc
      _ = (Term.withOwner owner e.lhs).evalFour w := (Term.evalFour_withOwner owner e.lhs w).symm
      _ = (Term.withOwner owner e.rhs).evalFour w := h.mp hws w
      _ = _ := Term.evalFour_withOwner owner e.rhs w
  · intro he v
    have hfour : ∀ w : Fin e.arity → Four,
        (Term.withOwner owner e.lhs).evalFour w = (Term.withOwner owner e.rhs).evalFour w := by
      intro w
      rw [Term.evalFour_withOwner, Term.evalFour_withOwner]
      exact he w
    calc
      _ = (Term.withOwner owner e.lhs).eval v := (Term.eval_withOwner owner e.lhs v).symm
      _ = (Term.withOwner owner e.rhs).eval v := h.mpr hfour v
      _ = _ := Term.eval_withOwner owner e.rhs v

/-- The displayed forty equations form a complete basis on the intended
winner-set algebra for every three-role embedding and chosen owner. -/
theorem isBasis_winnerSet {Role : Type u} (three : Fin 3 ↪ Role)
    (owner observer : Role) (ho : observer ≠ owner) :
    letI := oneOwnerStructure owner; Equational.IsBasis (WinnerSet Role) theory := by
  intro e
  exact (winnerSet_holds_iff_four three owner observer ho e).trans (isBasis e)

/-- The lower variable bound applies directly to every basis of the intended
fixed one-owner winner-set algebra, including infinite bases. -/
theorem variableBound_ge_four_winnerSet {Role : Type u} (three : Fin 3 ↪ Role)
    (owner observer : Role) (ho : observer ≠ owner) (T : Equational.Theory (Symbol Unit)) (n : ℕ)
    (hbasis : letI := oneOwnerStructure owner; Equational.IsBasis (WinnerSet Role) T)
    (hbound : Equational.HasVariableBound T n) : 4 ≤ n := by
  have hf : letI := fourStructure (Role := Unit); Equational.IsBasis Four T := by
    intro e
    exact (winnerSet_holds_iff_four three owner observer ho e).symm.trans (hbasis e)
  exact BasisObstruction.variableBound_ge_four T n hf hbound

end FiniteBasis
end KFOL.Owner
