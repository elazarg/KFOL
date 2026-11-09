module

public import KFOL.Reductions.ResetUnionMarkers

/-! # Correctness of the actual native reset/union SAT reduction -/

@[expose] public section

namespace KFOL.Reductions.ResetUnion

universe u

open KFOL.ResetUnion

private theorem ambiguous_union_singleton {Role : Type u} (A : WinnerSet Role) (b : Role) :
    (A.union (WinnerSet.singleton b)).Ambiguous ↔ A ≠ WinnerSet.singleton b := by
  constructor
  · intro ha he
    rw [he, WinnerSet.union_self] at ha
    exact ha b rfl
  · intro h k he
    obtain ⟨hk, hbk⟩ := (WinnerSet.union_eq_singleton_iff _ _ k).mp he
    exact h (hk.trans hbk.symm)

/-- An actual three-role countervaluation. Literal names are extended by their
proved injective map; the three anchors lie outside its image. -/
noncomputable def satisfyingValuation {Role : Type u} (b d e : Role)
    (assignment : ℕ → Bool) : ℕ → WinnerSet Role :=
  Function.extend literalName
    (fun literal => if assignment literal.1 = literal.2 then WinnerSet.singleton d else WinnerSet.singleton b)
    (fun j => if j = 0 then WinnerSet.singleton b else if j = 1 then
      (WinnerSet.singleton b).union (WinnerSet.singleton d) else WinnerSet.singleton e)

@[simp] theorem satisfyingValuation_literal {Role : Type u} (b d e : Role)
    (assignment : ℕ → Bool) (literal : Literal) :
    satisfyingValuation b d e assignment (literalName literal) =
      if assignment literal.1 = literal.2 then WinnerSet.singleton d else WinnerSet.singleton b :=
  literalName_injective.extend_apply _ _ literal

private theorem satisfyingValuation_small {Role : Type u} (b d e : Role)
    (assignment : ℕ → Bool) (j : ℕ) (hj : j < 3) :
    satisfyingValuation b d e assignment j =
      if j = 0 then WinnerSet.singleton b else if j = 1 then
        (WinnerSet.singleton b).union (WinnerSet.singleton d) else WinnerSet.singleton e := by
  apply Function.extend_apply'
  rintro ⟨literal, he⟩
  have h := literalName_ge_three literal
  omega

@[simp] theorem satisfyingValuation_zero {Role : Type u} (b d e : Role) (a : ℕ → Bool) :
    satisfyingValuation b d e a 0 = WinnerSet.singleton b :=
  satisfyingValuation_small b d e a 0 (by decide)

@[simp] theorem satisfyingValuation_one {Role : Type u} (b d e : Role) (a : ℕ → Bool) :
    satisfyingValuation b d e a 1 = (WinnerSet.singleton b).union (WinnerSet.singleton d) :=
  satisfyingValuation_small b d e a 1 (by decide)

@[simp] theorem satisfyingValuation_two {Role : Type u} (b d e : Role) (a : ℕ → Bool) :
    satisfyingValuation b d e a 2 = WinnerSet.singleton e :=
  satisfyingValuation_small b d e a 2 (by decide)

theorem satisfying_guard_ambiguous {Role : Type u} (b d e : Role) (hbd : b ≠ d)
    (a : ℕ → Bool) (literal : Literal) :
    ((satisfyingValuation b d e a (literalName literal)).union
      (satisfyingValuation b d e a 0)).Ambiguous ↔ a literal.1 = literal.2 := by
  rw [satisfyingValuation_zero, ambiguous_union_singleton, satisfyingValuation_literal]
  split_ifs with h
  · simp only [ne_eq, WinnerSet.singleton_inj, hbd.symm, h, not_false_eq_true]
  · simp only [h, not_true_eq_false, ne_eq]

/-- A satisfying Boolean assignment produces a failing valuation using only
three distinct roles, with one singleton or pair at every input. -/
theorem failure_of_satisfying_assignment {Role : Type u} (b d e : Role)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (formula : CNF) (a : ℕ → Bool)
    (hsat : ∀ C ∈ formula, ∃ literal ∈ C, a literal.1 = literal.2) :
    (equation formula).1.eval (satisfyingValuation b d e a) ≠
      (equation formula).2.eval (satisfyingValuation b d e a) := by
  classical
  let v := satisfyingValuation b d e a
  have hz : (v 1).Ambiguous := by
    rw [show v 1 = (WinnerSet.singleton b).union (WinnerSet.singleton d) from satisfyingValuation_one b d e a]
    exact WinnerSet.ambiguous_of_two_mem _ b d hbd (Or.inl rfl) (Or.inr rfl)
  have hforeign : e ∉ ((baseline formula).eval v).val := by
    rw [mem_baseline v formula hz]
    rintro (h | h | ⟨j, _, h | h⟩)
    · simp [v, WinnerSet.union, WinnerSet.singleton, hbe.symm, hde.symm] at h
    · simp [v, WinnerSet.singleton, hbe.symm] at h
    · change e ∈ (satisfyingValuation b d e a (literalName (j, true))).val at h
      rw [satisfyingValuation_literal] at h
      split_ifs at h <;> simp_all [WinnerSet.singleton]
    · change e ∈ (satisfyingValuation b d e a (literalName (j, false))).val at h
      rw [satisfyingValuation_literal] at h
      split_ifs at h <;> simp_all [WinnerSet.singleton]
  have hclauses : ∀ C ∈ formula, ((clauseGuard C).eval v).Ambiguous := by
    intro C hC
    obtain ⟨literal, hl, ht⟩ := hsat C hC
    have hliteral : v (literalName literal) = WinnerSet.singleton d := by
      simp [v, ht]
    have hb : b ∈ ((clauseGuard C).eval v).val :=
      (eval_clauseGuard_mem v C b).mpr (Or.inl (by simp [v, WinnerSet.singleton]))
    have hd : d ∈ ((clauseGuard C).eval v).val := by
      apply (eval_clauseGuard_mem v C d).mpr
      exact Or.inr ⟨literal, hl, by rw [hliteral]; rfl⟩
    exact WinnerSet.ambiguous_of_two_mem _ b d hbd hb hd
  have hpairs : ∀ j ∈ support formula,
      ¬(((v (literalName (j, true))).union (v 0)).Ambiguous ∧
        ((v (literalName (j, false))).union (v 0)).Ambiguous) := by
    intro j _ h
    have ht := (satisfying_guard_ambiguous b d e hbd a (j, true)).mp h.1
    have hf := (satisfying_guard_ambiguous b d e hbd a (j, false)).mp h.2
    exact Bool.false_ne_true (hf.symm.trans ht)
  have hc : e ∈ (v 2).val := by simp [v, WinnerSet.singleton]
  have hleft := (left_marker v formula hz e hforeign).mpr ⟨hc, hclauses⟩
  have hright : e ∉ ((right formula).eval v).val := by
    intro h
    obtain ⟨_, j, hj, hp⟩ := (right_marker v formula hz e hforeign).mp h
    exact hpairs j hj hp
  intro heq
  have hmem : e ∈ ((equation formula).1.eval v).val := by
    change e ∈ (((left formula).eval v).reset ((right formula).eval v)).val
    exact (WinnerSet.mem_reset _ _ e).mpr (Or.inr ⟨(right_ambiguous v formula).mpr hz, hleft⟩)
  rw [heq] at hmem
  exact hright hmem

/-- The complete paper-specific reduction: a native equation is valid on every
winner-set valuation exactly when the original CNF is unsatisfiable. Sparse
names, empty clauses and variable-free formulas require no side condition. -/
theorem valid_equation_iff {Role : Type u} (three : Fin 3 ↪ Role) (formula : CNF) :
    Valid Role (equation formula) ↔ ¬ Satisfiable formula := by
  classical
  constructor
  · intro hvalid hsat
    obtain ⟨a, ha⟩ := hsat
    have hbd := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
    have hbe := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
    have hde := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
    exact failure_of_satisfying_assignment (three 0) (three 1) (three 2)
      hbd hbe hde formula a ha (hvalid _)
  · intro hunsat v
    by_contra hf
    exact hunsat (satisfiable_of_failure v formula hf)

end KFOL.Reductions.ResetUnion
