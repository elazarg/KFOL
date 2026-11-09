module

public import KFOL.Reductions.ResetUnionSemantics

/-! # Exact marker and consistency semantics of the reduction equation -/

@[expose] public section

namespace KFOL.Reductions.ResetUnion

universe u

open KFOL.ResetUnion

variable {Role : Type u}

theorem literal_guard_subset_baseline (v : ℕ → WinnerSet Role) (formula : CNF)
    (hz : (v 1).Ambiguous) (j : ℕ) (hj : j ∈ support formula) (b : Bool) :
    ((v (literalName (j, b))).union (v 0)).val ⊆ ((baseline formula).eval v).val := by
  intro i hi
  apply (mem_baseline v formula hz i).mpr
  rcases hi with hi | hi
  · refine Or.inr (Or.inr ⟨j, hj, ?_⟩)
    cases b with
    | false => exact Or.inr hi
    | true => exact Or.inl hi
  · exact Or.inr (Or.inl hi)

theorem right_marker (v : ℕ → WinnerSet Role) (formula : CNF) (hz : (v 1).Ambiguous)
    (i : Role) (hi : i ∉ ((baseline formula).eval v).val) :
    i ∈ ((right formula).eval v).val ↔
      i ∈ (v 2).val ∧ ∃ j ∈ support formula,
        ((v (literalName (j, true))).union (v 0)).Ambiguous ∧
        ((v (literalName (j, false))).union (v 0)).Ambiguous := by
  have hbranch (j : ℕ) (hj : j ∈ support formula) :
      i ∈ ((branch j).eval v).val ↔
        i ∈ (v 2).val ∧
        ((v (literalName (j, true))).union (v 0)).Ambiguous ∧
        ((v (literalName (j, false))).union (v 0)).Ambiguous := by
    rw [branch, Term.eval_reset, Term.eval_reset, Term.eval_union, Term.eval_union,
      eval_literalTerm, eval_literalTerm, Term.eval_var, Term.eval_var]
    exact WinnerSetFold.mem_branch_outside _ _ _ i
      (fun h => hi (literal_guard_subset_baseline v formula hz j hj true h))
      (fun h => hi (literal_guard_subset_baseline v formula hz j hj false h))
  rw [right, Term.eval_rightComb, WinnerSetFold.mem_right _ _ ((baseline_ambiguous v formula).mpr hz)]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨A, ⟨t, ⟨j, hj, rfl⟩, rfl⟩, h⟩)
    · exact (hi h).elim
    · obtain ⟨hc, hp, hn⟩ := (hbranch j hj).mp h
      exact ⟨hc, j, hj, hp, hn⟩
  · rintro ⟨hc, j, hj, hp, hn⟩
    exact Or.inr ⟨_, ⟨branch j, ⟨j, hj, rfl⟩, rfl⟩, (hbranch j hj).mpr ⟨hc, hp, hn⟩⟩

theorem left_marker (v : ℕ → WinnerSet Role) (formula : CNF) (hz : (v 1).Ambiguous)
    (i : Role) (hi : i ∉ ((baseline formula).eval v).val) :
    i ∈ ((left formula).eval v).val ↔
      i ∈ (v 2).val ∧ ∀ C ∈ formula, ((clauseGuard C).eval v).Ambiguous := by
  rw [left, Term.eval_leftComb]
  have hguards : ∀ g ∈ ((formula.map clauseGuard).map (fun t => t.eval v)),
      g.val ⊆ ((baseline formula).eval v).val := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨t, ht, rfl⟩
    rcases List.mem_map.mp ht with ⟨C, hC, rfl⟩
    exact clauseGuard_subset_baseline v formula hz C hC
  simpa only [Term.eval_var, List.forall_mem_map] using
    WinnerSetFold.mem_left_outside _ _ ((baseline formula).eval v).val i hi hguards

/-- Every failed equation supplies a marker, satisfied clause guards and
pairwise-consistent literal guards. This quantifies over all winner valuations. -/
theorem failure_marker (v : ℕ → WinnerSet Role) (formula : CNF)
    (hf : (equation formula).1.eval v ≠ (equation formula).2.eval v) :
    (v 1).Ambiguous ∧ ∃ i : Role,
      i ∉ ((baseline formula).eval v).val ∧ i ∈ (v 2).val ∧
      (∀ C ∈ formula, ((clauseGuard C).eval v).Ambiguous) ∧
      (∀ j ∈ support formula,
        ¬(((v (literalName (j, true))).union (v 0)).Ambiguous ∧
          ((v (literalName (j, false))).union (v 0)).Ambiguous)) := by
  classical
  have hz : (v 1).Ambiguous := by
    by_contra h
    simp only [WinnerSet.Ambiguous, not_forall, not_not] at h
    obtain ⟨r, hr⟩ := h
    exact hf (equation_holds_of_atomic_z v formula r hr)
  have hR : ((right formula).eval v).Ambiguous := (right_ambiguous v formula).mpr hz
  have hsub : ¬((left formula).eval v).val ⊆ ((right formula).eval v).val := by
    intro hs
    apply hf
    change ((left formula).eval v).reset ((right formula).eval v) = (right formula).eval v
    rw [WinnerSet.reset_of_ambiguous _ _ hR]
    apply Subtype.ext
    exact Set.union_eq_right.mpr hs
  obtain ⟨i, hi, hn⟩ := Set.not_subset.mp hsub
  have hW : i ∉ ((baseline formula).eval v).val := fun h => hn (baseline_subset_right v formula hz h)
  obtain ⟨hc, hclauses⟩ := (left_marker v formula hz i hW).mp hi
  refine ⟨hz, i, hW, hc, hclauses, ?_⟩
  intro j hj hpair
  exact hn ((right_marker v formula hz i hW).mpr ⟨hc, j, hj, hpair⟩)

/-- A foreign marker with consistent literal guards forces the calibration
input to be atomic, because the explicit support is never empty. -/
theorem atomic_calibration (v : ℕ → WinnerSet Role) (formula : CNF)
    (hpair : ∀ j ∈ support formula,
      ¬(((v (literalName (j, true))).union (v 0)).Ambiguous ∧
        ((v (literalName (j, false))).union (v 0)).Ambiguous)) :
    ∃ r : Role, v 0 = WinnerSet.singleton r := by
  classical
  by_contra h
  have ha : (v 0).Ambiguous := by intro r hr; exact h ⟨r, hr⟩
  apply hpair 0 (zero_mem_support formula)
  constructor
  · rw [WinnerSet.union_comm]
    exact ha.union_left
  · rw [WinnerSet.union_comm]
    exact ha.union_left

/-- This is the sound Boolean reading of every countervaluation. -/
theorem satisfiable_of_failure {Role : Type u} (v : ℕ → WinnerSet Role) (formula : CNF)
    (hf : (equation formula).1.eval v ≠ (equation formula).2.eval v) : Satisfiable formula := by
  classical
  obtain ⟨_, _, _, _, hclauses, hpairs⟩ := failure_marker v formula hf
  obtain ⟨r, hr⟩ := atomic_calibration v formula hpairs
  let assignment : ℕ → Bool := fun j => decide (v (literalName (j, true)) ≠ v 0)
  refine ⟨assignment, fun C hC => ?_⟩
  have hguard := hclauses C hC
  have hsome : ∃ literal ∈ C, v (literalName literal) ≠ v 0 := by
    by_contra hn
    push Not at hn
    apply hguard r
    apply (clauseGuard_eq_singleton v C r hr).mpr
    intro literal hl
    exact (hn literal hl).trans hr
  obtain ⟨⟨j, b⟩, hl, hdiff⟩ := hsome
  refine ⟨(j, b), hl, ?_⟩
  cases b with
  | true => exact decide_eq_true hdiff
  | false =>
    have hpositive : v (literalName (j, true)) = v 0 := by
      by_contra hpos
      have hguard_of_diff (b : Bool) (hb : v (literalName (j, b)) ≠ v 0) :
          ((v (literalName (j, b))).union (v 0)).Ambiguous := by
        intro k he
        obtain ⟨hk, hk'⟩ := (WinnerSet.union_eq_singleton_iff _ _ k).mp he
        exact hb (hk.trans hk'.symm)
      exact hpairs j (literal_mem_support formula C hC (j, false) hl)
        ⟨hguard_of_diff true hpos, hguard_of_diff false hdiff⟩
    exact decide_eq_false (not_not.mpr hpositive)

end KFOL.Reductions.ResetUnion
