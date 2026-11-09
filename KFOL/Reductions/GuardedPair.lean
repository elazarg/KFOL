module

public import KFOL.Reductions.ResetUnionCorrectness
public import KFOL.Owner.Basic
public import Mathlib.Tactic.Linarith

/-! The actual pure two-guarded-owner native CNF equation. -/

@[expose] public section

namespace KFOL.GuardedPair

universe u v

namespace Term

variable {Var : Type v} {Role : Type u}

@[simp] theorem eval_var (a b : Role) (j : Var) (v : Var → WinnerSet Role) : eval a b (.var j) v = v j := rfl
@[simp] theorem eval_guarded (a b : Role) (sign : Bool) (x y z : Term Var) (v : Var → WinnerSet Role) :
    (guarded sign x y z).eval a b v = WinnerSet.guardedChoice (if sign then a else b)
      (x.eval a b v) (y.eval a b v) (z.eval a b v) := rfl
@[simp] theorem eval_reset (a b : Role) (s t : Term Var) (v : Var → WinnerSet Role) :
    (reset s t).eval a b v = (s.eval a b v).reset (t.eval a b v) := by
  simp only [reset, eval_guarded, ite_true, WinnerSet.guardedChoice, WinnerSet.choice_self]
@[simp] theorem eval_rightComb (a b : Role) (terms : List (Term Var)) (base : Term Var)
    (v : Var → WinnerSet Role) :
    (rightComb terms base).eval a b v = (terms.map (fun t => t.eval a b v)).foldr WinnerSet.reset (base.eval a b v) := by
  induction terms with
  | nil => rfl
  | cons t terms ih => simp only [rightComb, List.foldr_cons, eval_reset, List.map_cons] at *; rw [ih]

end Term
end KFOL.GuardedPair

namespace KFOL.Reductions.GuardedPair

universe u

open KFOL.GuardedPair

variable {Role : Type u}

/-- The owner itself is also covered: outside the baseline its singleton
cannot be a tested input. -/
theorem guarded_marker (s : Role) (Z Y U W : WinnerSet Role) (w : Role)
    (hz : Z.Ambiguous) (hZW : Z.val ⊆ W.val) (hYW : Y.val ⊆ W.val) (hw : w ∉ W.val) :
    w ∈ (WinnerSet.guardedChoice s Z Y U).val ↔ Y ≠ WinnerSet.singleton s ∧ w ∈ U.val := by
  have hzW : w ∉ Z.val := fun h => hw (hZW h)
  have hyW : w ∉ Y.val := fun h => hw (hYW h)
  rw [WinnerSet.guardedChoice, WinnerSet.mem_reset]
  simp only [hzW, hz, false_or, true_and]
  by_cases hws : s = w
  · subst s
    have hy : Y ≠ WinnerSet.singleton w := by
      intro he
      apply hyW
      rw [he]
      rfl
    rw [WinnerSet.mem_choice_owner]
    simp only [hyW, false_or]
    exact ⟨fun h => ⟨hy, h⟩, And.right⟩
  · rw [WinnerSet.mem_choice_other s w hws]
    have hu : w ∈ U.val → U ≠ WinnerSet.singleton s := by
      intro hU he
      rw [he] at hU
      exact hws (Set.mem_singleton_iff.mp hU).symm
    simp only [hyW, false_or]
    tauto

theorem mem_baseline (a b : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (hz : (v 0).Ambiguous) (w : Role) :
    w ∈ ((baseline formula).eval a b v).val ↔ w ∈ (v 0).val ∨
      ∃ i ∈ ResetUnion.support formula, w ∈ (v (booleanName i)).val := by
  rw [baseline, KFOL.GuardedPair.Term.eval_rightComb, KFOL.GuardedPair.Term.eval_var, WinnerSetFold.mem_right _ _ hz]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, hi, h⟩
  · rintro (h | ⟨i, hi, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, h⟩

@[simp] theorem baseline_ambiguous (a b : Role) (formula : CNF) (v : ℕ → WinnerSet Role) :
    ((baseline formula).eval a b v).Ambiguous ↔ (v 0).Ambiguous := by
  simp only [baseline, KFOL.GuardedPair.Term.eval_rightComb, KFOL.GuardedPair.Term.eval_var, WinnerSetFold.ambiguous_right]

@[simp] theorem right_ambiguous (a b : Role) (formula : CNF) (v : ℕ → WinnerSet Role) :
    ((right formula).eval a b v).Ambiguous ↔ (v 0).Ambiguous := by
  simp only [right, KFOL.GuardedPair.Term.eval_rightComb, WinnerSetFold.ambiguous_right, baseline_ambiguous]

theorem mem_right (a b : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (hz : (v 0).Ambiguous) (w : Role) :
    w ∈ ((right formula).eval a b v).val ↔ w ∈ ((baseline formula).eval a b v).val ∨
      ∃ C ∈ formula, w ∈ ((clause C).eval a b v).val := by
  rw [right, KFOL.GuardedPair.Term.eval_rightComb, WinnerSetFold.mem_right _ _ ((baseline_ambiguous a b formula v).mpr hz)]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨_, ⟨_, ⟨C, hc, rfl⟩, rfl⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨C, hc, h⟩
  · rintro (h | ⟨C, hc, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨_, ⟨C, hc, rfl⟩, rfl⟩, h⟩

theorem clause_marker (a b : Role) (C : Clause) (v : ℕ → WinnerSet Role)
    (W : WinnerSet Role) (hz : (v 0).Ambiguous) (hZW : (v 0).val ⊆ W.val)
    (hY : ∀ literal ∈ C, (v (booleanName literal.1)).val ⊆ W.val) (w : Role) (hw : w ∉ W.val) :
    w ∈ ((clause C).eval a b v).val ↔ w ∈ (v 1).val ∧
      ∀ literal ∈ C, v (booleanName literal.1) ≠ WinnerSet.singleton (if literal.2 then a else b) := by
  induction C with
  | nil => simp [clause]
  | cons literal rest ih =>
    rw [clause, KFOL.GuardedPair.Term.eval_guarded, KFOL.GuardedPair.Term.eval_var, KFOL.GuardedPair.Term.eval_var,
      guarded_marker _ _ _ _ W w hz hZW (hY literal (List.mem_cons_self ..)) hw,
      ih (fun l hl => hY l (List.mem_cons_of_mem _ hl))]
    simp only [List.forall_mem_cons]
    tauto

end KFOL.Reductions.GuardedPair

namespace KFOL.Reductions.GuardedPair

universe u

variable {Role : Type u}

theorem valid_of_unsatisfiable (a b : Role) (hab : a ≠ b) (formula : CNF)
    (hu : ¬Satisfiable formula) (v : ℕ → WinnerSet Role) :
    (equation formula).1.eval a b v = (equation formula).2.eval a b v := by
  classical
  by_cases hz : (v 0).Ambiguous
  · apply Subtype.ext
    ext w
    change w ∈ (KFOL.GuardedPair.Term.eval a b (KFOL.GuardedPair.Term.reset (.var 1) (right formula)) v).val ↔
      w ∈ ((right formula).eval a b v).val
    rw [KFOL.GuardedPair.Term.eval_reset, KFOL.GuardedPair.Term.eval_var, WinnerSet.mem_reset]
    simp only [(right_ambiguous a b formula v).mpr hz, true_and]
    constructor
    · rintro (hR | hC)
      · exact hR
      · apply (mem_right a b formula v hz w).mpr
        by_cases hw : w ∈ ((baseline formula).eval a b v).val
        · exact Or.inl hw
        · let assignment : ℕ → Bool := fun i => decide (v (booleanName i) = WinnerSet.singleton a)
          have hfail : ¬∀ C ∈ formula, ∃ literal ∈ C, assignment literal.1 = literal.2 :=
            fun h => hu ⟨assignment, h⟩
          push Not at hfail
          obtain ⟨C, hc, hfalse⟩ := hfail
          refine Or.inr ⟨C, hc, ?_⟩
          apply (clause_marker a b C v ((baseline formula).eval a b v) hz
            (fun _ h => (mem_baseline a b formula v hz _).mpr (Or.inl h))
            (fun literal hl _ h => (mem_baseline a b formula v hz _).mpr
              (Or.inr ⟨literal.1, ResetUnion.literal_mem_support formula C hc literal hl, h⟩)) w hw).mpr
          refine ⟨hC, ?_⟩
          intro literal hl
          have hf := hfalse literal hl
          cases hb : literal.2
          · have hy : v (booleanName literal.1) = WinnerSet.singleton a := by
              simpa [assignment, hb] using hf
            simpa only [hb, Bool.false_eq_true, ↓reduceIte, hy, ne_eq, WinnerSet.singleton_inj] using hab
          · simpa [assignment, hb] using hf
    · exact Or.inl
  · unfold WinnerSet.Ambiguous at hz
    push Not at hz
    obtain ⟨r, hr⟩ := hz
    have hbase : (baseline formula).eval a b v = WinnerSet.singleton r := by
      rw [baseline, KFOL.GuardedPair.Term.eval_rightComb, KFOL.GuardedPair.Term.eval_var, hr]
      exact WinnerSetFold.right_singleton _ r
    have hright : (right formula).eval a b v = WinnerSet.singleton r := by
      rw [right, KFOL.GuardedPair.Term.eval_rightComb, hbase]
      exact WinnerSetFold.right_singleton _ r
    simp only [equation, KFOL.GuardedPair.Term.eval_reset, hright, WinnerSet.reset_singleton]

/-- The separating marker is the specified third role, establishing the
observational hardness clause as well as ordinary equation nonvalidity. -/
theorem satisfying_assignment_separates (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (formula : CNF) (assignment : ℕ → Bool)
    (hsat : ∀ C ∈ formula, ∃ literal ∈ C, assignment literal.1 = literal.2) :
    let v := satisfyingValuation a b d assignment
    d ∈ ((equation formula).1.eval a b v).val ∧ d ∉ ((equation formula).2.eval a b v).val := by
  classical
  let v := satisfyingValuation a b d assignment
  have hz : (v 0).Ambiguous :=
    WinnerSet.ambiguous_of_two_mem _ a b hab (Or.inl rfl) (Or.inr rfl)
  have hw : d ∉ ((baseline formula).eval a b v).val := by
    rw [mem_baseline a b formula v hz]
    rintro (h | ⟨i, _, h⟩)
    · exact h.elim had.symm hbd.symm
    · change d ∈ (WinnerSet.singleton (if assignment i then a else b)).val at h
      cases hi : assignment i
      · have he : d = b := by simpa only [hi, Bool.false_eq_true, ↓reduceIte,
          WinnerSet.val_singleton, Set.mem_singleton_iff] using h
        exact hbd he.symm
      · have he : d = a := by simpa only [hi, ↓reduceIte,
          WinnerSet.val_singleton, Set.mem_singleton_iff] using h
        exact had he.symm
  have hclause : ∀ C ∈ formula, d ∉ ((clause C).eval a b v).val := by
    intro C hc hmem
    have hall := ((clause_marker a b C v ((baseline formula).eval a b v) hz
      (fun _ h => (mem_baseline a b formula v hz _).mpr (Or.inl h))
      (fun literal hl _ h => (mem_baseline a b formula v hz _).mpr
        (Or.inr ⟨literal.1, ResetUnion.literal_mem_support formula C hc literal hl, h⟩)) d hw).mp hmem).2
    obtain ⟨literal, hl, htruth⟩ := hsat C hc
    have hn := hall literal hl
    have he : v (booleanName literal.1) = WinnerSet.singleton (if literal.2 then a else b) := by
      change WinnerSet.singleton (if assignment literal.1 then a else b) = _
      rw [htruth]
    exact hn he
  have hR : d ∉ ((right formula).eval a b v).val := by
    rw [mem_right a b formula v hz]
    rintro (h | ⟨C, hc, h⟩)
    · exact hw h
    · exact hclause C hc h
  refine ⟨?_, hR⟩
  rw [show (equation formula).1 = KFOL.GuardedPair.Term.reset (.var 1) (right formula) from rfl,
    KFOL.GuardedPair.Term.eval_reset, KFOL.GuardedPair.Term.eval_var, WinnerSet.mem_reset]
  exact Or.inr ⟨(right_ambiguous a b formula v).mpr hz, rfl⟩

theorem equation_valid_iff_unsatisfiable (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (formula : CNF) :
    (∀ v : ℕ → WinnerSet Role, (equation formula).1.eval a b v = (equation formula).2.eval a b v) ↔
      ¬Satisfiable formula := by
  constructor
  · intro hv ⟨assignment, ha⟩
    obtain ⟨hl, hr⟩ := satisfying_assignment_separates a b d hab had hbd formula assignment ha
    exact hr ((hv _).symm ▸ hl)
  · exact fun h => valid_of_unsatisfiable a b hab formula h

theorem third_role_observation_valid_iff_unsatisfiable (a b d : Role)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (formula : CNF) :
    (∀ v : ℕ → WinnerSet Role,
      d ∈ ((equation formula).1.eval a b v).val ↔ d ∈ ((equation formula).2.eval a b v).val) ↔
      ¬Satisfiable formula := by
  constructor
  · intro hv ⟨assignment, ha⟩
    obtain ⟨hl, hr⟩ := satisfying_assignment_separates a b d hab had hbd formula assignment ha
    exact hr ((hv _).mp hl)
  · intro h v
    rw [valid_of_unsatisfiable a b hab formula h v]

end KFOL.Reductions.GuardedPair

namespace KFOL.GuardedPair.Term

universe v

variable {Var : Type v}

@[simp] theorem size_var (j : Var) : size (.var j) = 1 := rfl
@[simp] theorem size_guarded (sign : Bool) (x y z : Term Var) :
    (guarded sign x y z).size = 1 + x.size + y.size + z.size := rfl
@[simp] theorem size_reset (s t : Term Var) : (reset s t).size = 1 + t.size + s.size + s.size := rfl

theorem size_rightComb (terms : List (Term Var)) (base : Term Var) :
    (rightComb terms base).size = base.size + terms.length + 2 * (terms.map size).sum := by
  induction terms with
  | nil => simp [rightComb]
  | cons t terms ih =>
    change 1 + (rightComb terms base).size + t.size + t.size = _
    rw [ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem size_variable_rightComb (inputs : List Var) (root : Var) :
    (rightComb (inputs.map (fun i => .var i)) (.var root)).size = 1 + 3 * inputs.length := by
  induction inputs with
  | nil => rfl
  | cons i inputs ih =>
    change 1 + (rightComb (inputs.map (fun i => .var i)) (.var root)).size + 1 + 1 = _
    rw [ih]
    simp only [List.length_cons]
    omega

end KFOL.GuardedPair.Term

namespace KFOL.Reductions.GuardedPair

@[simp] theorem size_clause (C : Clause) : (clause C).size = 1 + 3 * C.length := by
  induction C with
  | nil => rfl
  | cons literal rest ih =>
    rw [clause, KFOL.GuardedPair.Term.size_guarded, KFOL.GuardedPair.Term.size_var,
      KFOL.GuardedPair.Term.size_var, ih, List.length_cons]
    omega

@[simp] theorem size_baseline (formula : CNF) :
    (baseline formula).size = 1 + 3 * (ResetUnion.support formula).length := by
  simpa only [baseline, List.map_map, List.length_map, Function.comp_def] using
    KFOL.GuardedPair.Term.size_variable_rightComb ((ResetUnion.support formula).map booleanName) 0

private theorem sum_clause_size (formula : CNF) :
    ((formula.map clause).map KFOL.GuardedPair.Term.size).sum =
      formula.length + 3 * (formula.map List.length).sum := by
  induction formula with
  | nil => rfl
  | cons C formula ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, size_clause, ih]
    omega

/-- Exact native size, including the two expanded copies of every clause
branch and each occurrence of its original variable labels. -/
theorem size_right (formula : CNF) : (right formula).size =
    1 + 3 * (ResetUnion.support formula).length + 3 * formula.length +
      6 * (formula.map List.length).sum := by
  rw [right, KFOL.GuardedPair.Term.size_rightComb, size_baseline,
    List.length_map, sum_clause_size]
  omega

/-- The ternary-only equation is linear in sparse support and literal count,
without even requiring the source clauses to have bounded width. -/
theorem equation_size (formula : CNF) :
    (equation formula).1.size + (equation formula).2.size =
      5 + 6 * (ResetUnion.support formula).length + 6 * formula.length +
        12 * (formula.map List.length).sum := by
  change 1 + (right formula).size + 1 + 1 + (right formula).size = _
  rw [size_right]
  omega

end KFOL.Reductions.GuardedPair

namespace KFOL.Reductions.GuardedPair

universe u

/-- The report's observational implication lower bound uses the same actual
third-role marker as observational equivalence and full equation hardness. -/
theorem third_role_observation_implication_valid_iff_unsatisfiable {Role : Type u}
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (formula : CNF) :
    (∀ v : ℕ → WinnerSet Role,
      d ∈ ((equation formula).1.eval a b v).val → d ∈ ((equation formula).2.eval a b v).val) ↔
      ¬Satisfiable formula := by
  constructor
  · intro hv ⟨assignment, ha⟩
    obtain ⟨hl, hr⟩ := satisfying_assignment_separates a b d hab had hbd formula assignment ha
    exact hr (hv _ hl)
  · intro hu v hl
    exact valid_of_unsatisfiable a b hab formula hu v ▸ hl

end KFOL.Reductions.GuardedPair
