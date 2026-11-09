module

public import KFOL.Reductions.RawPair

/-! Correctness of native raw-owner/union and two-raw-owner CNF equations. -/

@[expose] public section

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

theorem literalTerm_mem_rails (formula : CNF) (i : ℕ) (hi : i ∈ ResetUnion.support formula) (sign : Bool) :
    literalTerm (i, sign) ∈ rails formula := by
  apply List.mem_flatMap.mpr
  refine ⟨i, hi, ?_⟩
  cases sign <;> simp

theorem literal_subset_baseline_union (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (i : ℕ) (hi : i ∈ ResetUnion.support formula) (sign : Bool) :
    (v (ResetUnion.literalName (i, sign))).val ⊆
      ((baseline formula).eval (WinnerSet.choice a) WinnerSet.union v).val := by
  intro w hw
  rw [baseline, KFOL.RawPair.Term.eval_fold]
  change w ∈ (unions _ (v (ResetUnion.literalName (0, true)))).val
  apply (mem_unions _ _ _).mpr
  exact Or.inr ⟨_, List.mem_map.mpr ⟨literalTerm (i, sign), literalTerm_mem_rails formula i hi sign, rfl⟩, hw⟩

theorem core_union_valid_of_unsatisfiable (a : Role) (formula : CNF)
    (hnonempty : ∀ C ∈ formula, C ≠ []) (hu : ¬Satisfiable formula) (v : ℕ → WinnerSet Role) :
    (coreEquation formula).1.eval (WinnerSet.choice a) WinnerSet.union v =
      (coreEquation formula).2.eval (WinnerSet.choice a) WinnerSet.union v := by
  let pairs := (ResetUnion.support formula).map
    (fun i => (v (ResetUnion.literalName (i, true)), v (ResetUnion.literalName (i, false))))
  let clauses := formula.map (fun C => (clause C).eval (WinnerSet.choice a) WinnerSet.union v)
  let W := (baseline formula).eval (WinnerSet.choice a) WinnerSet.union v
  have hpairs : pairs ≠ [] := by
    have hmem : (v (ResetUnion.literalName (0, true)), v (ResetUnion.literalName (0, false))) ∈ pairs :=
      List.mem_map.mpr ⟨0, ResetUnion.zero_mem_support formula, rfl⟩
    intro he
    rw [he] at hmem
    exact List.not_mem_nil hmem
  have hc : ∀ C ∈ clauses, C.val ⊆ W.val := by
    intro C hC
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
    apply clause_subset a none C' (hnonempty C' hC') v W
    intro literal hl
    exact literal_subset_baseline_union a formula v literal.1
      (ResetUnion.literal_mem_support formula C' hC' literal hl) literal.2
  have hlogic : (∀ C ∈ clauses, C ≠ WinnerSet.singleton a) →
      ∃ pair ∈ pairs, pair.1 ≠ WinnerSet.singleton a ∧ pair.2 ≠ WinnerSet.singleton a := by
    intro hcs
    obtain ⟨i, hi, hp, hn⟩ := exists_conflicting_rails a none (by simp) formula hnonempty hu v
      (fun C hC => hcs _ (List.mem_map.mpr ⟨C, hC, rfl⟩))
    exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, hp, hn⟩
  have hs := raw_absorption a pairs clauses (v 0) W hpairs hc hlogic
  have hleft : (left formula).eval (WinnerSet.choice a) WinnerSet.union v = choiceFold a clauses (v 0) := by
    simp only [left, KFOL.RawPair.Term.eval_fold, ite_true, KFOL.RawPair.Term.eval_var,
      clauses, choiceFold, List.map_map, Function.comp_def]
  have hright : (right formula).eval (WinnerSet.choice a) WinnerSet.union v =
      unions (pairs.map (fun pair => WinnerSet.choice a (v 0) (WinnerSet.choice a pair.1 pair.2))) W := by
    simp only [right, KFOL.RawPair.Term.eval_fold, branch, KFOL.RawPair.Term.eval_node,
      literalTerm, KFOL.RawPair.Term.eval_var, Bool.false_eq_true, ite_false, ite_true,
      pairs, unions, W, List.map_map, Function.comp_def]
  change WinnerSet.union ((left formula).eval (WinnerSet.choice a) WinnerSet.union v)
    ((right formula).eval (WinnerSet.choice a) WinnerSet.union v) = _
  apply Subtype.ext
  apply Set.union_eq_right.mpr
  rw [hleft, hright]
  exact hs

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

theorem satisfying_literal_not_marker (a marker c : Role) (ham : a ≠ marker) (hcm : c ≠ marker)
    (assignment : ℕ → Bool) (literal : Literal) :
    marker ∉ (satisfyingValuation a marker c assignment (ResetUnion.literalName literal)).val := by
  rw [satisfyingValuation_literal]
  split_ifs with h
  · exact hcm.symm
  · exact ham.symm

/-- Explicit native choice/union SAT witness, using three roles and no
constants in the equation itself. -/
theorem core_union_satisfying_separates (a marker c : Role)
    (ham : a ≠ marker) (hac : a ≠ c) (hcm : c ≠ marker)
    (formula : CNF) (assignment : ℕ → Bool)
    (hsat : ∀ C ∈ formula, ∃ literal ∈ C, assignment literal.1 = literal.2) :
    let v := satisfyingValuation a marker c assignment
    marker ∈ ((coreEquation formula).1.eval (WinnerSet.choice a) WinnerSet.union v).val ∧
      marker ∉ ((coreEquation formula).2.eval (WinnerSet.choice a) WinnerSet.union v).val := by
  classical
  let v := satisfyingValuation a marker c assignment
  have hclause : ∀ C ∈ formula, (clause C).eval (WinnerSet.choice a) WinnerSet.union v ≠ WinnerSet.singleton a := by
    intro C hc he
    obtain ⟨literal, hl, htruth⟩ := hsat C hc
    have hne : C ≠ [] := List.ne_nil_of_mem hl
    have h := (clause_eq_owner a none (by simp) C hne v).mp he literal hl
    dsimp only [v] at h
    rw [satisfyingValuation_literal, ite_eq_left htruth, WinnerSet.singleton_inj] at h
    exact hac h.symm
  have hA : marker ∈ ((left formula).eval (WinnerSet.choice a) WinnerSet.union v).val := by
    rw [left, KFOL.RawPair.Term.eval_fold]
    change marker ∈ (choiceFold a _ (v 0)).val
    rw [choiceFold_union]
    · exact (mem_unions _ _ _).mpr (Or.inl (by simp only [v, satisfyingValuation_zero, WinnerSet.val_singleton, Set.mem_singleton_iff]))
    · simpa only [v, satisfyingValuation_zero, ne_eq, WinnerSet.singleton_inj] using ham.symm
    · intro X hX
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
      obtain ⟨C, hc, rfl⟩ := List.mem_map.mp ht
      exact hclause C hc
  have hW : marker ∉ ((baseline formula).eval (WinnerSet.choice a) WinnerSet.union v).val := by
    rw [baseline, KFOL.RawPair.Term.eval_fold]
    change marker ∉ (unions _ (v (ResetUnion.literalName (0, true)))).val
    rw [mem_unions]
    rintro (h | ⟨X, hX, h⟩)
    · exact satisfying_literal_not_marker a marker c ham hcm assignment _ h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
      obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact satisfying_literal_not_marker a marker c ham hcm assignment _ h
      · have he := List.mem_singleton.mp ht
        subst t
        exact satisfying_literal_not_marker a marker c ham hcm assignment _ h
  have hbranch (i : ℕ) : (branch i).eval (WinnerSet.choice a) WinnerSet.union v = WinnerSet.singleton a := by
    rw [branch, KFOL.RawPair.Term.eval_node]
    simp only [ite_true]
    apply (WinnerSet.choice_eq_owner_iff _ _ a).mpr
    right
    rw [KFOL.RawPair.Term.eval_node]
    simp only [ite_true]
    apply (WinnerSet.choice_eq_owner_iff _ _ a).mpr
    cases hi : assignment i
    · left
      change v (ResetUnion.literalName (i, true)) = _
      simp only [v, satisfyingValuation_literal, hi, Bool.false_eq_true, ite_false]
    · right
      change v (ResetUnion.literalName (i, false)) = _
      simp only [v, satisfyingValuation_literal, hi, Bool.true_eq_false, ite_false]
  have hR : marker ∉ ((right formula).eval (WinnerSet.choice a) WinnerSet.union v).val := by
    rw [right, KFOL.RawPair.Term.eval_fold]
    change marker ∉ (unions _ ((baseline formula).eval (WinnerSet.choice a) WinnerSet.union v)).val
    rw [mem_unions]
    rintro (h | ⟨X, hX, h⟩)
    · exact hW h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
      rw [hbranch i] at h
      exact ham (Set.mem_singleton_iff.mp h).symm
  refine ⟨?_, hR⟩
  change marker ∈ (((left formula).eval (WinnerSet.choice a) WinnerSet.union v).union
    ((right formula).eval (WinnerSet.choice a) WinnerSet.union v)).val
  exact Or.inl hA

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

theorem unsatisfiable_of_empty_clause (formula : CNF)
    (he : formula.any List.isEmpty = true) : ¬Satisfiable formula := by
  obtain ⟨C, hc, he⟩ := List.any_eq_true.mp he
  cases C with
  | nil =>
    rintro ⟨assignment, hall⟩
    obtain ⟨literal, hl, _⟩ := hall [] hc
    exact List.not_mem_nil hl
  | cons literal C => simp at he

theorem clauses_nonempty_of_no_empty (formula : CNF)
    (he : formula.any List.isEmpty ≠ true) : ∀ C ∈ formula, C ≠ [] := by
  intro C hc hnil
  apply he
  apply List.any_eq_true.mpr
  exact ⟨C, hc, by simp [hnil]⟩

/-- Complete native choice/union reduction, including empty clauses and the
empty conjunction, with no retained certificate hypothesis. -/
theorem union_equation_valid_iff_unsatisfiable (a marker c : Role)
    (ham : a ≠ marker) (hac : a ≠ c) (hcm : c ≠ marker) (formula : CNF) :
    (∀ v : ℕ → WinnerSet Role,
      (equation formula).1.eval (WinnerSet.choice a) WinnerSet.union v =
        (equation formula).2.eval (WinnerSet.choice a) WinnerSet.union v) ↔ ¬Satisfiable formula := by
  classical
  by_cases he : formula.any List.isEmpty = true
  · have hu := unsatisfiable_of_empty_clause formula he
    simp only [equation, he, ite_true]
    exact ⟨fun _ => hu, fun _ _ => trivial⟩
  · have hnonempty := clauses_nonempty_of_no_empty formula he
    simp only [equation, he]
    constructor
    · intro hv ⟨assignment, ha⟩
      obtain ⟨hl, hr⟩ := core_union_satisfying_separates a marker c ham hac hcm formula assignment ha
      exact hr ((hv _).symm ▸ hl)
    · intro hu
      exact core_union_valid_of_unsatisfiable a formula hnonempty hu

end KFOL.Reductions.RawPair
