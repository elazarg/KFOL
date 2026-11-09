module

public import KFOL.Owner.Public

/-! # A four-element algebra with exactly the one-owner identities -/

@[expose] public section

namespace KFOL.Owner

universe u v

namespace Four

@[simp] theorem card : Fintype.card Four = 4 := by decide

private theorem ext (x y : Four) (hw : (x = .winning ↔ y = .winning))
    (ho : (x = .owner ↔ y = .owner)) (ha : (x = .ambiguous ↔ y = .ambiguous)) : x = y := by
  cases x <;> cases y <;> simp_all

@[simp] theorem reset_winning (x y : Four) :
    reset x y = .winning ↔ y = .winning ∨ (y = .ambiguous ∧ x = .winning) := by
  cases x <;> cases y <;> decide
@[simp] theorem reset_owner (x y : Four) : reset x y = .owner ↔ y = .owner := by
  cases x <;> cases y <;> decide
@[simp] theorem reset_ambiguous (x y : Four) :
    reset x y = .ambiguous ↔ y = .ambiguous ∧ x ≠ .winning := by
  cases x <;> cases y <;> decide
@[simp] theorem guarded_winning (x y z : Four) :
    guarded x y z = .winning ↔ x = .winning ∨
      (x = .ambiguous ∧ y ≠ .owner ∧ z ≠ .owner ∧ (y = .winning ∨ z = .winning)) := by
  cases x <;> cases y <;> cases z <;> decide
@[simp] theorem guarded_owner (x y z : Four) : guarded x y z = .owner ↔ x = .owner := by
  cases x <;> cases y <;> cases z <;> decide
@[simp] theorem guarded_ambiguous (x y z : Four) :
    guarded x y z = .ambiguous ↔ x = .ambiguous ∧
      ¬(y ≠ .owner ∧ z ≠ .owner ∧ (y = .winning ∨ z = .winning)) := by
  cases x <;> cases y <;> cases z <;> decide

@[simp] theorem project_winning {Role : Type u} (owner observer : Role) (A : WinnerSet Role) :
    project owner observer A = .winning ↔ observer ∈ A.val := by
  classical
  by_cases hw : observer ∈ A.val <;> by_cases ho : A = WinnerSet.singleton owner <;>
    by_cases ha : A.Ambiguous <;> simp [project, hw, ho, ha]

@[simp] theorem project_owner {Role : Type u} (owner observer : Role) (hne : observer ≠ owner)
    (A : WinnerSet Role) : project owner observer A = .owner ↔ A = WinnerSet.singleton owner := by
  classical
  by_cases ho : A = WinnerSet.singleton owner
  · subst A
    simp [project, hne]
  · by_cases hw : observer ∈ A.val <;> by_cases ha : A.Ambiguous <;>
      simp [project, hw, ho, ha]


@[simp] theorem project_ambiguous {Role : Type u} (owner observer : Role) (A : WinnerSet Role) :
    project owner observer A = .ambiguous ↔ A.Ambiguous ∧ observer ∉ A.val := by
  classical
  by_cases hw : observer ∈ A.val
  · simp [project, hw]
  · by_cases ho : A = WinnerSet.singleton owner
    · subst A
      have hno : observer ≠ owner := by simpa only [WinnerSet.val_singleton, Set.mem_singleton_iff] using hw
      have ha : ¬(WinnerSet.singleton owner).Ambiguous := fun h => h owner rfl
      simp [project, hno, ha]
    · by_cases ha : A.Ambiguous <;> simp [project, hw, ho, ha]

/-- The quotient remembers enough information to preserve reset, even
though observed atoms and observed ambiguous values share one state. -/
theorem project_reset {Role : Type u} (owner observer : Role) (hne : observer ≠ owner)
    (A B : WinnerSet Role) :
    project owner observer (A.reset B) = reset (project owner observer A) (project owner observer B) := by
  apply ext
  · simp only [project_winning, reset_winning, project_ambiguous, WinnerSet.mem_reset]
    tauto
  · simp only [project_owner owner observer hne, reset_owner, WinnerSet.reset_eq_singleton]
  · simp only [ne_eq, project_ambiguous, reset_ambiguous, project_winning,
      WinnerSet.ambiguous_reset, WinnerSet.mem_reset]
    tauto

/-- The projection preserves the unique owner's H operation. -/
theorem project_guarded {Role : Type u} (owner observer : Role) (hne : observer ≠ owner)
    (A B C : WinnerSet Role) :
    project owner observer (WinnerSet.guardedChoice owner A B C) =
      guarded (project owner observer A) (project owner observer B) (project owner observer C) := by
  apply ext
  · simp only [ne_eq, project_winning, guarded_winning, project_ambiguous,
      project_owner owner observer hne, WinnerSet.guardedChoice, WinnerSet.mem_reset,
      WinnerSet.mem_choice_other owner observer hne.symm]
    tauto
  · simp only [project_owner owner observer hne, guarded_owner,
      WinnerSet.guardedChoice, WinnerSet.reset_eq_singleton]
  · simp only [ne_eq, project_ambiguous, guarded_ambiguous,
      project_owner owner observer hne, project_winning, WinnerSet.guardedChoice,
      WinnerSet.ambiguous_reset, WinnerSet.mem_reset,
      WinnerSet.mem_choice_other owner observer hne.symm]
    tauto

theorem project_embed {Role : Type u} (owner observer background : Role)
    (hko : observer ≠ owner) (hkb : observer ≠ background) (hob : owner ≠ background) (x : Four) :
    project owner observer (embed owner observer background x) = x := by
  classical
  have ha : ((WinnerSet.singleton owner).union (WinnerSet.singleton background)).Ambiguous :=
    WinnerSet.ambiguous_of_two_mem _ owner background hob (Or.inl rfl) (Or.inr rfl)
  cases x with
  | owner => simp [embed, project, hko]
  | other => simp [embed, project, hkb, WinnerSet.singleton_inj, hob.symm, WinnerSet.Ambiguous]
  | ambiguous => simp [embed, project, hko, hkb, ha, WinnerSet.union_eq_singleton_iff,
      WinnerSet.singleton_inj, hob.symm]
  | winning => simp [embed, project]

/-- The displayed four concrete values are closed under both operations. -/
theorem embed_reset {Role : Type u} (owner observer background : Role) (hob : owner ≠ background)
    (x y : Four) : embed owner observer background (reset x y) =
      (embed owner observer background x).reset (embed owner observer background y) := by
  classical
  have ha : ((WinnerSet.singleton owner).union (WinnerSet.singleton background)).Ambiguous :=
    WinnerSet.ambiguous_of_two_mem _ owner background hob (Or.inl rfl) (Or.inr rfl)
  have ht : (((WinnerSet.singleton owner).union (WinnerSet.singleton background)).union
      (WinnerSet.singleton observer)).Ambiguous := ha.union_left
  have howner : ¬(WinnerSet.singleton owner).Ambiguous := fun h => h owner rfl
  have hother : ¬(WinnerSet.singleton background).Ambiguous := fun h => h background rfl
  cases x <;> cases y
  all_goals simp only [reset, embed, WinnerSet.reset, ha, ht, howner, hother, ite_true, ite_false,
    and_self, false_and, true_and, reduceCtorEq]
  all_goals apply Subtype.ext; ext r; simp only [WinnerSet.val_union, WinnerSet.val_singleton,
    Set.mem_union, Set.mem_singleton_iff]; tauto

/-- Closure agrees with the complete ternary multiplication table of Four. -/
theorem embed_guarded {Role : Type u} (owner observer background : Role) (hob : owner ≠ background)
    (x y z : Four) : embed owner observer background (guarded x y z) =
      WinnerSet.guardedChoice owner (embed owner observer background x)
        (embed owner observer background y) (embed owner observer background z) := by
  classical
  have ha : ((WinnerSet.singleton owner).union (WinnerSet.singleton background)).Ambiguous :=
    WinnerSet.ambiguous_of_two_mem _ owner background hob (Or.inl rfl) (Or.inr rfl)
  have ht : (((WinnerSet.singleton owner).union (WinnerSet.singleton background)).union
      (WinnerSet.singleton observer)).Ambiguous := ha.union_left
  have howner : ¬(WinnerSet.singleton owner).Ambiguous := fun h => h owner rfl
  have hother : ¬(WinnerSet.singleton background).Ambiguous := fun h => h background rfl
  have hne : WinnerSet.singleton background ≠ WinnerSet.singleton owner := by
    simpa only [ne_eq, WinnerSet.singleton_inj] using hob.symm
  cases x <;> cases y <;> cases z
  all_goals simp [guarded, embed, WinnerSet.guardedChoice, WinnerSet.reset,
    WinnerSet.choice, ha, ht, howner, hother, hne, ha owner, ht owner]
  all_goals apply Subtype.ext; ext r; simp only [WinnerSet.val_union, WinnerSet.val_singleton,
    Set.mem_union, Set.mem_singleton_iff]; tauto

end Four

namespace Term

variable {Role : Type u} {Var : Type v}

@[simp] theorem evalFour_var (j : Var) (v : Var → Four) : evalFour (.var j : Term Role Var) v = v j := rfl
@[simp] theorem evalFour_step (s t : Term Role Var) (v : Var → Four) :
    (step s t).evalFour v = Four.reset (s.evalFour v) (t.evalFour v) := rfl
@[simp] theorem evalFour_guarded (r : Role) (x y z : Term Role Var) (v : Var → Four) :
    (guarded r x y z).evalFour v = Four.guarded (x.evalFour v) (y.evalFour v) (z.evalFour v) := rfl

theorem project_eval (t : Term Role Var) (owner observer : Role) (ho : observer ≠ owner)
    (ht : t.OwnersIn (fun r => r = owner)) (v : Var → WinnerSet Role) :
    Four.project owner observer (t.eval v) = t.evalFour (fun j => Four.project owner observer (v j)) := by
  induction t using induction_owner with
  | var => rfl
  | step s t hs ht' => simp only [eval_step, evalFour_step, Four.project_reset owner observer ho, hs ht.1, ht' ht.2]
  | guarded r x y z hx hy hz =>
    have hr : r = owner := ht.1
    subst r
    simp only [eval_guarded, evalFour_guarded, Four.project_guarded owner observer ho,
      hx ht.2.1, hy ht.2.2.1, hz ht.2.2.2]

/-- The four-element algebra has precisely the one-owner identities for any
role set containing three distinct roles. This does not assert minimum size. -/
theorem four_element_complete [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (s t : Term Role Var) (owner observer : Role) (ho : observer ≠ owner)
    (hs : s.OwnersIn (fun r => r = owner)) (ht : t.OwnersIn (fun r => r = owner)) :
    (∀ v : Var → WinnerSet Role, s.eval v = t.eval v) ↔
      ∀ w : Var → Four, s.evalFour w = t.evalFour w := by
  obtain ⟨background, hbo, hbk⟩ := exists_role_outside_pair three owner observer
  constructor
  · intro he w
    have h := congrArg (Four.project owner observer) (he (fun j => Four.embed owner observer background (w j)))
    rw [s.project_eval owner observer ho hs, t.project_eval owner observer ho ht] at h
    simpa only [Four.project_embed owner observer background ho hbk.symm hbo.symm] using h
  · intro he
    rw [s.single_table_equation_iff three t owner observer ho hs ht]
    have hl := s.owners_mono _ (fun r => r = observer ∨ r = owner) hs (fun _ h => Or.inr h)
    have hr := t.owners_mono _ (fun r => r = observer ∨ r = owner) ht (fun _ h => Or.inr h)
    apply (s.observation_equation_iff t observer owner background ho hbk.symm hbo.symm hl hr).mpr
    intro v
    have h := he (fun j => Four.project owner observer (v j))
    rw [← s.project_eval owner observer ho hs, ← t.project_eval owner observer ho ht] at h
    rw [← Four.project_winning owner observer, ← Four.project_winning owner observer, h]

end Term
end KFOL.Owner
