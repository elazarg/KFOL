module

public import KFOL.Reset.Basic

/-! # Exact mixed-input selection semantics for reset terms -/

@[expose] public section

namespace KFOL.Reset.Term

universe u v

variable {Var : Type v} {Role : Type u}

@[simp] theorem selected_var (i j : Var) (B : Set Var) :
    Selected (.var i) B j ↔ j = i := Iff.rfl

@[simp] theorem root_var (i : Var) :
    root (.var i) = i := rfl

/-- The rightmost input determines precisely whether a reset term is ambiguous. -/
@[simp] theorem ambiguous_eval (t : Term Var) (v : Var → WinnerSet Role) :
    (t.eval v).Ambiguous ↔ (v t.root).Ambiguous := by
  induction t using induction_reset with
  | var => rfl
  | step s t _ ih => simpa only [eval_step, root_step, WinnerSet.ambiguous_reset] using ih

/-- Every term selects its actual rightmost variable. -/
theorem selected_root (t : Term Var) (B : Set Var) : t.Selected B t.root := by
  induction t using induction_reset with
  | var => rfl
  | step s t _ ih => exact Or.inl ih

/-- Enabling more ambiguity statuses can only add selected inputs. -/
theorem selected_mono (t : Term Var) {B C : Set Var} (hBC : B ⊆ C) (j : Var) :
    t.Selected B j → t.Selected C j := by
  induction t using induction_reset with
  | var => exact id
  | step s t hs ht =>
    rintro (hj | ⟨hr, hj⟩)
    · exact Or.inl (ht hj)
    · exact Or.inr ⟨hBC hr, hs hj⟩

/-- Selection of j is independent of j's own ambiguity status. -/
theorem selected_self_independent (t : Term Var) (B C : Set Var) (j : Var)
    (h : ∀ i, i ≠ j → (i ∈ B ↔ i ∈ C)) : t.Selected B j ↔ t.Selected C j := by
  induction t using induction_reset with
  | var => rfl
  | step s t hs ht =>
    by_cases he : j = t.root
    · subst j
      exact ⟨fun _ => Or.inl (t.selected_root C), fun _ => Or.inl (t.selected_root B)⟩
    · exact or_congr ht (and_congr (h t.root (Ne.symm he)) hs)

/-- A concrete membership is the union of exactly the selected input values. -/
theorem mem_eval (t : Term Var) (v : Var → WinnerSet Role) (r : Role) :
    r ∈ (t.eval v).val ↔ ∃ j, t.Selected {i | (v i).Ambiguous} j ∧ r ∈ (v j).val := by
  induction t using induction_reset with
  | var i => simp [Selected]
  | step s t hs ht =>
    simp only [eval_step, WinnerSet.mem_reset, ambiguous_eval, hs, ht, selected_step]
    constructor
    · rintro (⟨j, hj, hr⟩ | ⟨ha, j, hj, hr⟩)
      · exact ⟨j, Or.inl hj, hr⟩
      · exact ⟨j, Or.inr ⟨ha, hj⟩, hr⟩
    · rintro ⟨j, hj | ⟨ha, hj⟩, hr⟩
      · exact Or.inl ⟨j, hj, hr⟩
      · exact Or.inr ⟨ha, j, hj, hr⟩

/-- At the all-atomic status, precisely the root position is selected. -/
@[simp] theorem selected_empty (t : Term Var) (j : Var) :
    t.Selected ∅ j ↔ j = t.root := by
  induction t using induction_reset with
  | var => rfl
  | step s t _ ht => simpa only [selected_step, Set.mem_empty_iff_false, false_and,
      or_false, root_step] using ht

/-- Thus all-atomic input valuations are projected to the root. -/
theorem eval_singletons (t : Term Var) (v : Var → Role) :
    t.eval (fun j => WinnerSet.singleton (v j)) = WinnerSet.singleton (v t.root) := by
  induction t using induction_reset with
  | var => rfl
  | step s t _ ht => simp only [eval_step, ht, WinnerSet.reset_singleton, root_step]

/-- Actual substitution replaces the root by the corresponding inner root. -/
@[simp] theorem root_subst {Var' : Type u} (t : Term Var) (s : Var → Term Var') :
    root (t.subst s) = (s t.root).root := by
  induction t using induction_reset with
  | var => rfl
  | step l r _ ih => exact ih

/-- The selector substitution law retains both outer and inner selection. -/
theorem selected_subst {Var' : Type u} (t : Term Var) (s : Var → Term Var')
    (B : Set Var') (j : Var') :
    Selected (t.subst s) B j ↔
      ∃ i, t.Selected {k | (s k).root ∈ B} i ∧ (s i).Selected B j := by
  induction t using induction_reset with
  | var i =>
    simp only [FirstOrder.Language.Term.subst, selected_var]
    exact ⟨fun h => ⟨i, rfl, h⟩, by rintro ⟨_, rfl, h⟩; exact h⟩
  | step l r hl hr =>
    change Selected (r.subst s) B j ∨
      (root (r.subst s) ∈ B ∧ Selected (l.subst s) B j) ↔ _
    rw [hl, hr, root_subst]
    simp only [selected_step, Set.mem_ofPred_eq]
    constructor
    · rintro (⟨i, hi, hj⟩ | ⟨ha, i, hi, hj⟩)
      · exact ⟨i, Or.inl hi, hj⟩
      · exact ⟨i, Or.inr ⟨ha, hi⟩, hj⟩
    · rintro ⟨i, hi | ⟨ha, hi⟩, hj⟩
      · exact Or.inl ⟨i, hi, hj⟩
      · exact Or.inr ⟨ha, i, hi, hj⟩

end KFOL.Reset.Term
