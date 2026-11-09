module

public import KFOL.Reset.Basic

@[expose] public section

namespace KFOL.Reductions

universe u

namespace WinnerSetFold

variable {Role : Type u}

@[simp] theorem ambiguous_right (xs : List (WinnerSet Role)) (base : WinnerSet Role) :
    (xs.foldr WinnerSet.reset base).Ambiguous ↔ base.Ambiguous := by
  induction xs <;> simp_all

theorem mem_right (xs : List (WinnerSet Role)) (base : WinnerSet Role)
    (hb : base.Ambiguous) (i : Role) :
    i ∈ (xs.foldr WinnerSet.reset base).val ↔
      i ∈ base.val ∨ ∃ A ∈ xs, i ∈ A.val := by
  induction xs with
  | nil => simp
  | cons A xs ih =>
    simp only [List.foldr_cons, WinnerSet.mem_reset, ambiguous_right, hb, true_and,
      ih, List.mem_cons]
    grind

theorem right_singleton (xs : List (WinnerSet Role)) (r : Role) :
    xs.foldr WinnerSet.reset (WinnerSet.singleton r) = WinnerSet.singleton r := by
  induction xs <;> simp_all

theorem mem_union (xs : List (WinnerSet Role)) (base : WinnerSet Role) (i : Role) :
    i ∈ (xs.foldl WinnerSet.union base).val ↔
      i ∈ base.val ∨ ∃ A ∈ xs, i ∈ A.val := by
  induction xs generalizing base with
  | nil => simp
  | cons A xs ih =>
    simp only [List.foldl_cons, ih, WinnerSet.val_union, Set.mem_union, List.mem_cons]
    grind

theorem union_eq_singleton (xs : List (WinnerSet Role)) (base : WinnerSet Role) (r : Role) :
    xs.foldl WinnerSet.union base = WinnerSet.singleton r ↔
      base = WinnerSet.singleton r ∧ ∀ A ∈ xs, A = WinnerSet.singleton r := by
  induction xs generalizing base with
  | nil => simp
  | cons A xs ih =>
    rw [List.foldl_cons, ih, WinnerSet.union_eq_singleton_iff]
    simp only [List.forall_mem_cons]
    tauto

/-- Outside the baseline every left-comb guard is a pure ambiguity test. -/
theorem mem_left_outside (guards : List (WinnerSet Role)) (marker : WinnerSet Role)
    (baseline : Set Role) (i : Role) (hi : i ∉ baseline)
    (hg : ∀ g ∈ guards, g.val ⊆ baseline) :
    i ∈ (guards.foldl WinnerSet.reset marker).val ↔
      i ∈ marker.val ∧ ∀ g ∈ guards, g.Ambiguous := by
  induction guards generalizing marker with
  | nil => simp
  | cons g gs ih =>
    have hgi : i ∉ g.val := fun h => hi (hg g (List.mem_cons_self ..) h)
    have hrest : ∀ g ∈ gs, g.val ⊆ baseline := fun g h => hg g (List.mem_cons_of_mem _ h)
    rw [List.foldl_cons, ih _ hrest, WinnerSet.mem_reset]
    simp only [hgi, false_or, List.forall_mem_cons]
    tauto

/-- The consistency branch carries a foreign marker exactly when both
literal guards are ambiguous. -/
theorem mem_branch_outside (c positive negative : WinnerSet Role) (i : Role)
    (hp : i ∉ positive.val) (hn : i ∉ negative.val) :
    i ∈ ((c.reset positive).reset negative).val ↔
      i ∈ c.val ∧ positive.Ambiguous ∧ negative.Ambiguous := by
  simp only [WinnerSet.mem_reset, hp, hn, false_or]
  tauto

end WinnerSetFold
end KFOL.Reductions
