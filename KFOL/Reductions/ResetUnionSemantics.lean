module

public import KFOL.Definitions.Reductions
public import KFOL.Reductions.ValueFolds

/-! # Semantic folds and support for the native CNF reduction -/

@[expose] public section

namespace KFOL.ResetUnion.Term

universe u v

variable {Role : Type u} {Var : Type v}

@[simp] theorem eval_var (j : Var) (v : Var → WinnerSet Role) :
    eval (.var j) v = v j := rfl

@[simp] theorem eval_reset (s t : Term Var) (v : Var → WinnerSet Role) :
    (reset s t).eval v = (s.eval v).reset (t.eval v) := rfl

@[simp] theorem eval_union (s t : Term Var) (v : Var → WinnerSet Role) :
    (union s t).eval v = (s.eval v).union (t.eval v) := rfl

theorem eval_rightComb (xs : List (Term Var)) (base : Term Var) (v : Var → WinnerSet Role) :
    (rightComb xs base).eval v = (xs.map (fun t => t.eval v)).foldr WinnerSet.reset (base.eval v) := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    change (reset t (rightComb xs base)).eval v = _
    rw [eval_reset, ih]
    rfl

theorem eval_leftComb (xs : List (Term Var)) (base : Term Var) (v : Var → WinnerSet Role) :
    (leftComb base xs).eval v = (xs.map (fun t => t.eval v)).foldl WinnerSet.reset (base.eval v) := by
  induction xs generalizing base with
  | nil => rfl
  | cons t xs ih =>
    change (leftComb (reset base t) xs).eval v = _
    rw [ih, eval_reset]
    rfl

theorem eval_unionFold (xs : List (Term Var)) (base : Term Var) (v : Var → WinnerSet Role) :
    (unionFold base xs).eval v = (xs.map (fun t => t.eval v)).foldl WinnerSet.union (base.eval v) := by
  induction xs generalizing base with
  | nil => rfl
  | cons t xs ih =>
    change (unionFold (union base t) xs).eval v = _
    rw [ih, eval_union]
    rfl

end KFOL.ResetUnion.Term

namespace KFOL.Reductions.ResetUnion

universe u

open KFOL.ResetUnion

@[simp] theorem zero_mem_support (formula : CNF) : 0 ∈ support formula := by
  simp [support]

theorem literal_mem_support (formula : CNF) (C : Clause) (hC : C ∈ formula)
    (literal : Literal) (hl : literal ∈ C) : literal.1 ∈ support formula := by
  simp only [support, List.mem_dedup, List.mem_cons, List.mem_map]
  exact Or.inr ⟨literal, List.mem_flatten.mpr ⟨C, hC, hl⟩, rfl⟩

theorem literalName_injective : Function.Injective literalName := by
  rintro ⟨i, p⟩ ⟨j, q⟩ he
  cases p <;> cases q <;> simp only [literalName, Bool.false_eq_true, ite_false, ite_true] at he
  · congr 1; omega
  · omega
  · omega
  · congr 1; omega

theorem literalName_ge_three (literal : Literal) : 3 ≤ literalName literal := by
  rcases literal with ⟨i, p⟩
  cases p <;> simp only [literalName, Bool.false_eq_true, ite_false, ite_true] <;> omega

@[simp] theorem eval_literalTerm {Role : Type u} (v : ℕ → WinnerSet Role) (literal : Literal) :
    (literalTerm literal).eval v = v (literalName literal) := rfl

theorem eval_clauseGuard_mem {Role : Type u} (v : ℕ → WinnerSet Role) (C : Clause) (i : Role) :
    i ∈ ((clauseGuard C).eval v).val ↔
      i ∈ (v 0).val ∨ ∃ literal ∈ C, i ∈ (v (literalName literal)).val := by
  rw [clauseGuard, Term.eval_unionFold]
  simp only [List.map_map, Function.comp_def, eval_literalTerm, Term.eval_var]
  rw [WinnerSetFold.mem_union]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨A, ⟨literal, hl, rfl⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨literal, hl, h⟩
  · rintro (h | ⟨literal, hl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨literal, hl, rfl⟩, h⟩

theorem clauseGuard_eq_singleton {Role : Type u} (v : ℕ → WinnerSet Role) (C : Clause)
    (r : Role) (h0 : v 0 = WinnerSet.singleton r) :
    (clauseGuard C).eval v = WinnerSet.singleton r ↔
      ∀ literal ∈ C, v (literalName literal) = WinnerSet.singleton r := by
  rw [clauseGuard, Term.eval_unionFold, WinnerSetFold.union_eq_singleton]
  simp only [Term.eval_var, h0, true_and, List.forall_mem_map, eval_literalTerm]

@[simp] theorem baseline_ambiguous {Role : Type u} (v : ℕ → WinnerSet Role) (formula : CNF) :
    ((baseline formula).eval v).Ambiguous ↔ (v 1).Ambiguous := by
  rw [baseline, Term.eval_rightComb, WinnerSetFold.ambiguous_right, Term.eval_var]

@[simp] theorem right_ambiguous {Role : Type u} (v : ℕ → WinnerSet Role) (formula : CNF) :
    ((right formula).eval v).Ambiguous ↔ (v 1).Ambiguous := by
  rw [right, Term.eval_rightComb, WinnerSetFold.ambiguous_right, baseline_ambiguous]

theorem mem_baseline {Role : Type u} (v : ℕ → WinnerSet Role) (formula : CNF)
    (hz : (v 1).Ambiguous) (i : Role) :
    i ∈ ((baseline formula).eval v).val ↔
      i ∈ (v 1).val ∨ i ∈ (v 0).val ∨
        ∃ j ∈ support formula, i ∈ (v (literalName (j, true))).val ∨
          i ∈ (v (literalName (j, false))).val := by
  rw [baseline, Term.eval_rightComb, Term.eval_var, WinnerSetFold.mem_right _ _ hz]
  simp only [List.mem_map, List.mem_append, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | ⟨A, ⟨t, (⟨j, hj, ht | ht⟩ | ht), rfl⟩, h⟩)
    · exact Or.inl h
    · subst t
      exact Or.inr (Or.inr ⟨j, hj, Or.inl h⟩)
    · subst t
      exact Or.inr (Or.inr ⟨j, hj, Or.inr h⟩)
    · subst t
      exact Or.inr (Or.inl h)
  · rintro (h | h | ⟨j, hj, h | h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨.var 0, Or.inr rfl, rfl⟩, h⟩
    · exact Or.inr ⟨_, ⟨literalTerm (j, true), Or.inl ⟨j, hj, Or.inl rfl⟩, rfl⟩, h⟩
    · exact Or.inr ⟨_, ⟨literalTerm (j, false), Or.inl ⟨j, hj, Or.inr rfl⟩, rfl⟩, h⟩

theorem clauseGuard_subset_baseline {Role : Type u} (v : ℕ → WinnerSet Role)
    (formula : CNF) (hz : (v 1).Ambiguous) (C : Clause) (hC : C ∈ formula) :
    ((clauseGuard C).eval v).val ⊆ ((baseline formula).eval v).val := by
  intro i hi
  apply (mem_baseline v formula hz i).mpr
  rcases (eval_clauseGuard_mem v C i).mp hi with hi | ⟨⟨j, b⟩, hl, hi⟩
  · exact Or.inr (Or.inl hi)
  · refine Or.inr (Or.inr ⟨j, literal_mem_support formula C hC (j, b) hl, ?_⟩)
    cases b with
    | false => exact Or.inr hi
    | true => exact Or.inl hi

theorem baseline_subset_right {Role : Type u} (v : ℕ → WinnerSet Role)
    (formula : CNF) (hz : (v 1).Ambiguous) :
    ((baseline formula).eval v).val ⊆ ((right formula).eval v).val := by
  intro i hi
  rw [right, Term.eval_rightComb, WinnerSetFold.mem_right _ _ ((baseline_ambiguous v formula).mpr hz)]
  exact Or.inl hi

theorem equation_holds_of_atomic_z {Role : Type u} (v : ℕ → WinnerSet Role)
    (formula : CNF) (r : Role) (hz : v 1 = WinnerSet.singleton r) :
    (equation formula).1.eval v = (equation formula).2.eval v := by
  have hw : (baseline formula).eval v = WinnerSet.singleton r := by
    rw [baseline, Term.eval_rightComb, Term.eval_var, hz, WinnerSetFold.right_singleton]
  have hr : (right formula).eval v = WinnerSet.singleton r := by
    rw [right, Term.eval_rightComb, hw, WinnerSetFold.right_singleton]
  change (Term.reset (left formula) (right formula)).eval v = (right formula).eval v
  rw [Term.eval_reset, hr, WinnerSet.reset_singleton]

end KFOL.Reductions.ResetUnion
