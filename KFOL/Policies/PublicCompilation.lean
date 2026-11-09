module

public import KFOL.Policies.Basic
public import KFOL.Reset.Public
public import KFOL.Algebra.PairTests

/-! Proof-level expansion of native policies into the existing full public
language. Original valuations and variable names are preserved exactly. -/

@[expose] public section

namespace KFOL.Policies.Term

universe u v w

variable {Role : Type u} {Label : Type w} {Var : Type v}

private theorem foldr_eq_suppress (roles : List Role) (s t : KFOL.Term Role Var) :
    roles.foldr (fun r acc => .choice r acc t) s = KFOL.Term.suppress roles s t := by
  induction roles with
  | nil => rfl
  | cons r roles ih => simp only [List.foldr_cons, KFOL.Term.suppress, ih]

private theorem eval_suppress_unblocked (roles : List Role) (acc base : KFOL.Term Role Var)
    (v : Var → WinnerSet Role) (hbase : ∀ r ∈ roles, base.eval v ≠ WinnerSet.singleton r)
    (hsub : (base.eval v).val ⊆ (acc.eval v).val) :
    (KFOL.Term.suppress roles acc base).eval v = acc.eval v := by
  classical
  induction roles with
  | nil => rfl
  | cons r roles ih =>
    have hb := hbase r (List.mem_cons_self ..)
    have ha : acc.eval v ≠ WinnerSet.singleton r := by
      intro he
      exact hb (WinnerSet.eq_singleton_of_subset _ r (by simpa only [he, WinnerSet.val_singleton] using hsub))
    have hrest := ih (fun s hs => hbase s (List.mem_cons_of_mem _ hs))
    simp only [KFOL.Term.suppress, KFOL.Term.eval, hrest, WinnerSet.choice, hb, ha, or_self, ite_false]
    apply Subtype.ext
    exact Set.union_eq_left.mpr hsub

private theorem eval_policy_suppress (three : Fin 3 ↪ Role) (D : Finset Role)
    (y z : KFOL.Term Role Var) (v : Var → WinnerSet Role) :
    (KFOL.Term.suppress D.toList (KFOL.Term.unionTerm three y z) y).eval v =
      WinnerSet.selective (D : Set Role) (z.eval v) (y.eval v) := by
  classical
  by_cases hblock : WinnerSet.PolicyBlocks (D : Set Role) (y.eval v)
  · obtain ⟨r, hr, hyr⟩ := hblock
    have he := KFOL.Term.eval_suppress_atom D.toList (KFOL.Term.unionTerm three y z) y v r
      (Finset.mem_toList.mpr hr) hyr
    have hb : WinnerSet.PolicyBlocks (D : Set Role) (y.eval v) := ⟨r, hr, hyr⟩
    rw [WinnerSet.selective, ite_eq_left hb, hyr]
    exact he
  · rw [eval_suppress_unblocked D.toList _ y v]
    · simp only [WinnerSet.selective, hblock, ite_false, KFOL.Term.eval_unionTerm]
    · intro r hr hyr
      exact hblock ⟨r, Finset.mem_toList.mp hr, hyr⟩
    · simp only [KFOL.Term.eval_unionTerm]
      exact Set.subset_union_left

/-- The complete native interpretation agrees on every valuation; the
compiler leaves each original variable name unchanged. -/
theorem eval_toPublic (three : Fin 3 ↪ Role) (roles : List Role) (hroles : ∀ r, r ∈ roles)
    (D : Label → Finset Role) (t : Term Label Var) (v : Var → WinnerSet Role) :
    (t.toPublic three roles D).eval v = t.eval (fun d => (D d : Set Role)) v := by
  induction t using induction_policy with
  | var => rfl
  | step s t hs ht =>
    change (roles.foldr (fun r acc => .choice r acc (t.toPublic three roles D))
      (KFOL.Term.unionTerm three (s.toPublic three roles D) (t.toPublic three roles D))).eval v = _
    rw [foldr_eq_suppress]
    change (Reset.Term.resetTerm three roles (s.toPublic three roles D) (t.toPublic three roles D)).eval v = _
    rw [Reset.Term.eval_resetTerm three roles hroles, hs, ht, eval_step]
  | selective d x y z hx hy hz =>
    let selected := KFOL.Term.suppress (D d).toList
      (KFOL.Term.unionTerm three (y.toPublic three roles D) (z.toPublic three roles D)) (y.toPublic three roles D)
    have he : (toPublic three roles D (selective d x y z)) =
        Reset.Term.resetTerm three roles selected (x.toPublic three roles D) := by
      change roles.foldr (fun r acc => .choice r acc (x.toPublic three roles D))
        (KFOL.Term.unionTerm three
          ((D d).toList.foldr (fun r acc => .choice r acc (y.toPublic three roles D))
            (KFOL.Term.unionTerm three (y.toPublic three roles D) (z.toPublic three roles D)))
          (x.toPublic three roles D)) = _
      rw [foldr_eq_suppress, foldr_eq_suppress]
      rfl
    rw [he, Reset.Term.eval_resetTerm three roles hroles, eval_policy_suppress, hx, hy, hz]
    rfl

private theorem core_foldr_choices (roles : List Role) (acc base : KFOL.Term Role Var)
    (hacc : acc.IsCore) (hbase : base.IsCore) :
    (roles.foldr (fun r t => .choice r t base) acc).IsCore := by
  induction roles with
  | nil => exact hacc
  | cons r roles ih => exact ⟨ih, hbase⟩

/-- The proof expansion uses only actual owned choices and the original
variable leaves, with neither winner constants nor role switches. -/
theorem isCore_toPublic (three : Fin 3 ↪ Role) (roles : List Role) (D : Label → Finset Role)
    (t : Term Label Var) : (t.toPublic three roles D).IsCore := by
  induction t using induction_policy with
  | var => trivial
  | step s t hs ht =>
    change (roles.foldr (fun r acc => .choice r acc (t.toPublic three roles D))
      (KFOL.Term.unionTerm three (s.toPublic three roles D) (t.toPublic three roles D))).IsCore
    exact core_foldr_choices roles _ _ ⟨⟨hs, ht⟩, ⟨hs, ht⟩⟩ ht
  | selective d x y z hx hy hz =>
    let selected := (D d).toList.foldr (fun r acc => .choice r acc (y.toPublic three roles D))
      (KFOL.Term.unionTerm three (y.toPublic three roles D) (z.toPublic three roles D))
    have hselected : selected.IsCore := core_foldr_choices _ _ _ ⟨⟨hy, hz⟩, ⟨hy, hz⟩⟩ hy
    change (roles.foldr (fun r acc => .choice r acc (x.toPublic three roles D))
      (KFOL.Term.unionTerm three selected (x.toPublic three roles D))).IsCore
    exact core_foldr_choices roles _ _ ⟨⟨hselected, hx⟩, ⟨hselected, hx⟩⟩ hx

/-- Every failed native policy equation has a pair-valued countervaluation,
for every finite role set and every finite policy interpretation. No
tractability criterion is required. -/
theorem exists_pair_val_countervaluation [Finite Role] (three : Fin 3 ↪ Role)
    (D : Label → Finset Role) (s t : Term Label Var)
    (failure : ∃ v : Var → WinnerSet Role,
      s.eval (fun d => (D d : Set Role)) v ≠ t.eval (fun d => (D d : Set Role)) v) :
    ∃ v : Var → WinnerSet Role, (∀ i, ∃ a b, (v i).val = {a, b}) ∧
      s.eval (fun d => (D d : Set Role)) v ≠ t.eval (fun d => (D d : Set Role)) v := by
  classical
  let _ := Fintype.ofFinite Role
  let roles := (Finset.univ : Finset Role).toList
  have hroles : ∀ r, r ∈ roles := by simp [roles]
  have hfailure : ∃ v : Var → WinnerSet Role,
      (s.toPublic three roles D).eval v ≠ (t.toPublic three roles D).eval v := by
    obtain ⟨v, hv⟩ := failure
    exact ⟨v, by simpa only [eval_toPublic three roles hroles] using hv⟩
  obtain ⟨v, hpairs, hne⟩ := KFOL.Term.exists_pair_countervaluation
    (s.toPublic three roles D) (t.toPublic three roles D) hfailure
  exact ⟨v, hpairs, by simpa only [eval_toPublic three roles hroles] using hne⟩

/-- Failure is witnessed on the original native syntax by singleton-or-pair
inputs at every variable, with no assumption on the family criterion. -/
theorem exists_pair_countervaluation [Finite Role] (D : Label → Finset Role)
    (three : Fin 3 ↪ Role) (s t : Term Label Var)
    (failure : ∃ v : Var → WinnerSet Role,
      s.eval (fun d => (D d : Set Role)) v ≠ t.eval (fun d => (D d : Set Role)) v) :
    ∃ v : Var → WinnerSet Role,
      (s.eval (fun d => (D d : Set Role)) v ≠ t.eval (fun d => (D d : Set Role)) v) ∧
      ∀ i, ∃ a b, v i = (WinnerSet.singleton a).union (WinnerSet.singleton b) := by
  obtain ⟨v, hpairs, hne⟩ := exists_pair_val_countervaluation three D s t failure
  refine ⟨v, hne, ?_⟩
  intro i
  obtain ⟨a, b, he⟩ := hpairs i
  exact ⟨a, b, Subtype.ext he⟩

end KFOL.Policies.Term
