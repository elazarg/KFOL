module

public import KFOL.Algebra.Atomic.OneConstant

/-! # Support and surviving atoms in core contexts -/

@[expose] public section

namespace KFOL

universe u v



namespace Term

variable {Role : Type u} {Var : Type v} [DecidableEq Var]

/-- Agreement on the actual syntactic support suffices to fix a core term. -/
theorem IsCore.eval_eq_of_support {t : Term Role Var} (ht : t.IsCore)
    (v : Var → WinnerSet Role) (A : WinnerSet Role)
    (h : ∀ x ∈ t.vars, v x = A) : t.eval v = A := by
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x => exact h x (Finset.mem_singleton_self _)
  | choice r s t hs ht' =>
    rw [eval,hs ht.1 (fun x hx => h x (Finset.mem_union_left _ hx)),
      ht' ht.2 (fun x hx => h x (Finset.mem_union_right _ hx)),WinnerSet.choice_idempotent]

/-- Every output lies in any set containing all actual input leaves. -/
theorem IsCore.eval_subset_of_support {t : Term Role Var} (ht : t.IsCore)
    (v : Var → WinnerSet Role) (U : Set Role) (h : ∀ x ∈ t.vars, (v x).val ⊆ U) :
    (t.eval v).val ⊆ U := by
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x => exact h x (Finset.mem_singleton_self _)
  | choice r s t hs ht' =>
    exact (WinnerSet.choice_subset_union r _ _).trans (Set.union_subset
      (hs ht.1 (fun x hx => h x (Finset.mem_union_left _ hx)))
      (ht' ht.2 (fun x hx => h x (Finset.mem_union_right _ hx))))

omit [DecidableEq Var] in
/-- If all singleton inputs have the same label, every singleton intermediate
output has that same label. Ambiguous inputs are unrestricted. -/
theorem IsCore.singleton_label {t : Term Role Var} (ht : t.IsCore)
    (v : Var → WinnerSet Role) (r : Role)
    (hv : ∀ x, (v x).Ambiguous ∨ v x = WinnerSet.singleton r)
    (q : Role) (he : t.eval v = WinnerSet.singleton q) : q = r := by
  classical
  induction t generalizing q with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x =>
    rcases hv x with hx | hx
    · exact False.elim (hx q he)
    · exact WinnerSet.singleton_inj.mp (he.symm.trans hx)
  | choice p s t hs ht' =>
    by_cases hp : s.eval v = WinnerSet.singleton p ∨ t.eval v = WinnerSet.singleton p
    · have hpr : p = r := hp.elim (hs ht.1 p) (ht' ht.2 p)
      have hqp : q = p := WinnerSet.singleton_inj.mp
        (he.symm.trans (by simp [eval,WinnerSet.choice,hp]))
      exact hqp.trans hpr
    · have hu : (s.eval v).union (t.eval v) = WinnerSet.singleton q := by
        simpa only [eval,WinnerSet.choice,hp,ite_false] using he
      exact hs ht.1 q (WinnerSet.union_eq_singleton_iff _ _ q |>.mp hu).1

/-- An occurring input equal to the unique available atom cannot be suppressed. -/
theorem IsCore.atom_mem_of_occurs {t : Term Role Var} (ht : t.IsCore)
    (v : Var → WinnerSet Role) (r : Role)
    (hv : ∀ x, (v x).Ambiguous ∨ v x = WinnerSet.singleton r)
    (x : Var) (hx : x ∈ t.vars) (he : v x = WinnerSet.singleton r) :
    r ∈ (t.eval v).val := by
  classical
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var y =>
    have hxy : x = y := Finset.mem_singleton.mp hx
    subst x
    simp [eval,he]
  | choice p s t hs ht' =>
    by_cases hp : s.eval v = WinnerSet.singleton p ∨ t.eval v = WinnerSet.singleton p
    · have hpr : p = r := hp.elim
        (fun h => ht.1.singleton_label v r hv p h)
        (fun h => ht.2.singleton_label v r hv p h)
      simp only [eval,WinnerSet.choice,ite_eq_left hp]
      change r = p
      exact hpr.symm
    · simp only [eval,WinnerSet.choice,hp,ite_false,WinnerSet.val_union,Set.mem_union]
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Or.inl (hs ht.1 hx)
      · exact Or.inr (ht' ht.2 hx)

end Term

end KFOL
