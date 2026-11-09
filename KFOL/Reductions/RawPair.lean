module

public import KFOL.Reductions.RawFolds

/-! A single native binary-pair signature, retaining both original trees. -/

@[expose] public section

namespace KFOL.RawPair

universe u v

namespace Term

variable {Var : Type v} {Role : Type u}

@[simp] theorem eval_var (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role)
    (j : Var) (v : Var → WinnerSet Role) : eval first second (.var j) v = v j := rfl
@[simp] theorem eval_node (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role)
    (sign : Bool) (s t : Term Var) (v : Var → WinnerSet Role) :
    (node sign s t).eval first second v = (if sign then first else second)
      (s.eval first second v) (t.eval first second v) := rfl
@[simp] theorem eval_fold (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role)
    (sign : Bool) (terms : List (Term Var)) (base : Term Var) (v : Var → WinnerSet Role) :
    (fold sign terms base).eval first second v =
      (terms.map (fun t => t.eval first second v)).foldr (if sign then first else second)
        (base.eval first second v) := by
  induction terms with
  | nil => rfl
  | cons t terms ih => simp only [fold, List.foldr_cons, eval_node, List.map_cons] at *; rw [ih]

end Term
end KFOL.RawPair

namespace KFOL.Reductions.RawPair

universe u

/- The optional second owner distinguishes choice/union from two choices. -/

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

private theorem outer_fold_subset (mode : Option Role) (xs : List (WinnerSet Role))
    (base W : WinnerSet Role) (hbase : base.val ⊆ W.val) (hx : ∀ X ∈ xs, X.val ⊆ W.val) :
    (xs.foldr (outerOp mode) base).val ⊆ W.val := by
  induction xs with
  | nil => exact hbase
  | cons X xs ih =>
    have hrest := ih (fun Y h => hx Y (List.mem_cons_of_mem _ h))
    have hX := hx X (List.mem_cons_self ..)
    cases mode with
    | none => exact Set.union_subset hX hrest
    | some b => exact (WinnerSet.choice_subset_union b X _).trans (Set.union_subset hX hrest)

theorem clause_subset (a : Role) (mode : Option Role) (C : Clause) (hne : C ≠ [])
    (v : ℕ → WinnerSet Role) (W : WinnerSet Role)
    (h : ∀ literal ∈ C, (v (ResetUnion.literalName literal)).val ⊆ W.val) :
    ((clause C).eval (WinnerSet.choice a) (outerOp mode) v).val ⊆ W.val := by
  cases C with
  | nil => exact False.elim (hne rfl)
  | cons literal rest =>
    rw [clause, KFOL.RawPair.Term.eval_fold]
    simp only [literalTerm, KFOL.RawPair.Term.eval_var, Bool.false_eq_true, ite_false]
    apply outer_fold_subset mode _ _ W (h literal (List.mem_cons_self ..))
    intro X hX
    obtain ⟨term, ht, rfl⟩ := List.mem_map.mp hX
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ht
    exact h l (List.mem_cons_of_mem _ hl)

theorem clause_eq_owner (a : Role) (mode : Option Role) (hmode : ∀ b ∈ mode, b ≠ a)
    (C : Clause) (hne : C ≠ []) (v : ℕ → WinnerSet Role) :
    (clause C).eval (WinnerSet.choice a) (outerOp mode) v = WinnerSet.singleton a ↔
      ∀ literal ∈ C, v (ResetUnion.literalName literal) = WinnerSet.singleton a := by
  cases C with
  | nil => exact False.elim (hne rfl)
  | cons literal rest =>
    rw [clause, KFOL.RawPair.Term.eval_fold]
    simp only [literalTerm, KFOL.RawPair.Term.eval_var, Bool.false_eq_true, ite_false]
    cases mode with
    | none =>
      change unions _ (v (ResetUnion.literalName literal)) = WinnerSet.singleton a ↔ _
      rw [unions_eq_singleton]
      simp only [List.forall_mem_map, List.forall_mem_cons, literalTerm, KFOL.RawPair.Term.eval_var]
    | some b =>
      change choiceFold b _ (v (ResetUnion.literalName literal)) = WinnerSet.singleton a ↔ _
      rw [choiceFold_eq_other b a (hmode b (by simp))]
      simp only [List.forall_mem_map, List.forall_mem_cons, literalTerm, KFOL.RawPair.Term.eval_var]

/-- Every UNSAT instance with no atomic clause has a genuinely inconsistent
pair of rails. This is proved for the native clause values, not an oracle. -/
theorem exists_conflicting_rails (a : Role) (mode : Option Role) (hmode : ∀ b ∈ mode, b ≠ a)
    (formula : CNF) (hnonempty : ∀ C ∈ formula, C ≠ []) (hu : ¬Satisfiable formula)
    (v : ℕ → WinnerSet Role)
    (hclauses : ∀ C ∈ formula, (clause C).eval (WinnerSet.choice a) (outerOp mode) v ≠ WinnerSet.singleton a) :
    ∃ i ∈ ResetUnion.support formula,
      v (ResetUnion.literalName (i, true)) ≠ WinnerSet.singleton a ∧
        v (ResetUnion.literalName (i, false)) ≠ WinnerSet.singleton a := by
  classical
  by_contra hno
  let assignment : ℕ → Bool := fun i => decide (v (ResetUnion.literalName (i, true)) ≠ WinnerSet.singleton a)
  have hf : ¬∀ C ∈ formula, ∃ literal ∈ C, assignment literal.1 = literal.2 :=
    fun h => hu ⟨assignment, h⟩
  push Not at hf
  obtain ⟨C, hc, hfalse⟩ := hf
  apply hclauses C hc
  apply (clause_eq_owner a mode hmode C (hnonempty C hc) v).mpr
  intro literal hl
  have hf := hfalse literal hl
  cases literal with
  | mk i sign =>
    cases sign with
    | true => simpa [assignment] using hf
    | false =>
      have hp : v (ResetUnion.literalName (i, true)) ≠ WinnerSet.singleton a := by
        simpa [assignment] using hf
      by_contra hn
      exact hno ⟨i, ResetUnion.literal_mem_support formula C hc (i, false) hl, hp, hn⟩

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

@[simp] theorem satisfyingValuation_literal {Role : Type u} (a marker c : Role)
    (assignment : ℕ → Bool) (literal : Literal) :
    satisfyingValuation a marker c assignment (ResetUnion.literalName literal) =
      WinnerSet.singleton (if assignment literal.1 = literal.2 then c else a) :=
  ResetUnion.literalName_injective.extend_apply _ _ literal

@[simp] theorem satisfyingValuation_zero {Role : Type u} (a marker c : Role) (assignment : ℕ → Bool) :
    satisfyingValuation a marker c assignment 0 = WinnerSet.singleton marker := by
  apply Function.extend_apply'
  rintro ⟨literal, he⟩
  have h := ResetUnion.literalName_ge_three literal
  omega

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

end KFOL.Reductions.RawPair
