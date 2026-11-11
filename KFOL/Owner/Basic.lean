module

public import KFOL.Definitions.Owner
public import KFOL.Reset.Basic
public import KFOL.Algebra.Views

/-! # Root status and structural induction for guarded-owner terms -/

@[expose] public section

namespace KFOL

universe u v

namespace Owner.Term

variable {Role : Type u} {Var : Type v}

@[simp] theorem root_var (j : Var) : root (.var j : Term Role Var) = j := rfl
@[simp] theorem root_step (s t : Term Role Var) : (step s t).root = t.root := rfl
@[simp] theorem root_guarded (r : Role) (x y z : Term Role Var) : (guarded r x y z).root = x.root := rfl

@[simp] theorem eval_var (j : Var) (v : Var → WinnerSet Role) : eval (.var j) v = v j := rfl
@[simp] theorem eval_step (s t : Term Role Var) (v : Var → WinnerSet Role) :
    (step s t).eval v = (s.eval v).reset (t.eval v) := rfl
@[simp] theorem eval_guarded (r : Role) (x y z : Term Role Var) (v : Var → WinnerSet Role) :
    (guarded r x y z).eval v = WinnerSet.guardedChoice r (x.eval v) (y.eval v) (z.eval v) := rfl

@[simp] theorem ownersIn_var (P : Role → Prop) (j : Var) : OwnersIn P (.var j) := trivial
@[simp] theorem ownersIn_step (P : Role → Prop) (s t : Term Role Var) :
    (step s t).OwnersIn P ↔ s.OwnersIn P ∧ t.OwnersIn P := Iff.rfl
@[simp] theorem ownersIn_guarded (P : Role → Prop) (r : Role) (x y z : Term Role Var) :
    (guarded r x y z).OwnersIn P ↔ P r ∧ x.OwnersIn P ∧ y.OwnersIn P ∧ z.OwnersIn P := Iff.rfl

@[simp] theorem leafCount_var (j : Var) : leafCount (.var j : Term Role Var) = 1 := rfl
@[simp] theorem leafCount_step (s t : Term Role Var) : (step s t).leafCount = s.leafCount + t.leafCount := rfl
@[simp] theorem leafCount_guarded (r : Role) (x y z : Term Role Var) :
    (guarded r x y z).leafCount = x.leafCount + y.leafCount + z.leafCount := rfl

/-- Ordinary reset/ternary guarded induction over mathlib's generic terms. -/
@[elab_as_elim] theorem induction_owner {P : Term Role Var → Prop}
    (var : ∀ j, P (.var j))
    (step : ∀ s t, P s → P t → P (Term.step s t))
    (guarded : ∀ r x y z, P x → P y → P z → P (Term.guarded r x y z))
    (t : Term Role Var) : P t := by
  induction t with
  | var j => exact var j
  | @func n f args ih =>
    cases f with
    | reset =>
      have he : FirstOrder.Language.Term.func Symbol.reset args = Term.step (args 0) (args 1) := by
        congr 1
        funext i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;> rfl
      rw [he]
      exact step _ _ (ih 0) (ih 1)
    | guarded r =>
      have he : FirstOrder.Language.Term.func (Symbol.guarded r) args =
          Term.guarded r (args 0) (args 1) (args 2) := by
        congr 1
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi with rfl | rfl | rfl <;> rfl
      rw [he]
      exact guarded _ _ _ _ (ih 0) (ih 1) (ih 2)

/-- Ambiguity depends exactly on the distinguished root variable. -/
theorem ambiguous_iff (t : Term Role Var) (v : Var → WinnerSet Role) :
    (t.eval v).Ambiguous ↔ (v t.root).Ambiguous := by
  induction t using induction_owner with
  | var => rfl
  | step s t _ ht => exact (WinnerSet.ambiguous_reset _ _).trans ht
  | guarded r x y z hx _ _ => exact (WinnerSet.ambiguous_reset _ _).trans hx

/-- Every atomic output is precisely the atom at the root variable. -/
theorem eq_singleton_iff (t : Term Role Var) (v : Var → WinnerSet Role) (r : Role) :
    t.eval v = WinnerSet.singleton r ↔ v t.root = WinnerSet.singleton r := by
  induction t using induction_owner with
  | var => rfl
  | step s t _ ht => exact (WinnerSet.reset_eq_singleton _ _ r).trans ht
  | guarded owner x y z hx _ _ => exact (WinnerSet.reset_eq_singleton _ _ r).trans hx

theorem owners_mono (t : Term Role Var) (P Q : Role → Prop)
    (ht : t.OwnersIn P) (hpq : ∀ r, P r → Q r) : t.OwnersIn Q := by
  induction t using induction_owner with
  | var => trivial
  | step s t hs ht' => exact ⟨hs ht.1, ht' ht.2⟩
  | guarded r x y z hx hy hz => exact ⟨hpq r ht.1, hx ht.2.1, hy ht.2.2.1, hz ht.2.2.2⟩

end Owner.Term
end KFOL
