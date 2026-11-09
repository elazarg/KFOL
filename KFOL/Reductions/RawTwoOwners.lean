module

public import KFOL.Reductions.RawCorrectness

/-! The two-owned-choice reduction with the outer absorbing cases separated. -/

@[expose] public section

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

private theorem clause_twoOwners_eq_union (a b : Role) (C : Clause) (hne : C ≠ [])
    (v : ℕ → WinnerSet Role) (havoid : ∀ literal ∈ C, v (ResetUnion.literalName literal) ≠ WinnerSet.singleton b) :
    (clause C).eval (WinnerSet.choice a) (WinnerSet.choice b) v =
      (clause C).eval (WinnerSet.choice a) WinnerSet.union v := by
  cases C with
  | nil => exact False.elim (hne rfl)
  | cons literal rest =>
    simp only [clause, KFOL.RawPair.Term.eval_fold, literalTerm, KFOL.RawPair.Term.eval_var,
      List.map_map, Function.comp_def, Bool.false_eq_true, ite_false]
    apply choiceFold_union b _ _ (havoid literal (List.mem_cons_self ..))
    intro X hX
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hX
    exact havoid l (List.mem_cons_of_mem _ hl)

private theorem clause_twoOwners_ne_b (a b : Role) (C : Clause) (hne : C ≠ [])
    (v : ℕ → WinnerSet Role) (havoid : ∀ literal ∈ C, v (ResetUnion.literalName literal) ≠ WinnerSet.singleton b) :
    (clause C).eval (WinnerSet.choice a) (WinnerSet.choice b) v ≠ WinnerSet.singleton b := by
  cases C with
  | nil => exact False.elim (hne rfl)
  | cons literal rest =>
    simp only [clause, KFOL.RawPair.Term.eval_fold, literalTerm, KFOL.RawPair.Term.eval_var,
      List.map_map, Function.comp_def, Bool.false_eq_true, ite_false]
    change choiceFold b _ _ ≠ WinnerSet.singleton b
    intro he
    rcases (choiceFold_eq_owner b _ _).mp he with he | ⟨X, hX, he⟩
    · exact havoid literal (List.mem_cons_self ..) he
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hX
      exact havoid l (List.mem_cons_of_mem _ hl) he

private theorem branch_second_independent (a : Role) (second : WinnerSet Role → WinnerSet Role → WinnerSet Role)
    (i : ℕ) (v : ℕ → WinnerSet Role) :
    (branch i).eval (WinnerSet.choice a) second v =
      WinnerSet.choice a (v 0) (WinnerSet.choice a (v (ResetUnion.literalName (i, true)))
        (v (ResetUnion.literalName (i, false)))) := by
  simp only [branch, KFOL.RawPair.Term.eval_node, literalTerm, KFOL.RawPair.Term.eval_var, ite_true]

private theorem branch_ne_other (a b : Role) (hab : a ≠ b) (i : ℕ) (v : ℕ → WinnerSet Role)
    (hpos : v (ResetUnion.literalName (i, true)) ≠ WinnerSet.singleton b) :
    (branch i).eval (WinnerSet.choice a) (WinnerSet.choice b) v ≠ WinnerSet.singleton b := by
  rw [branch_second_independent]
  intro he
  have hi := (WinnerSet.choice_eq_other_iff (r := a) (A := v 0) (B := WinnerSet.choice a
    (v (ResetUnion.literalName (i, true))) (v (ResetUnion.literalName (i, false)))) hab).mp he
  exact hpos ((WinnerSet.choice_eq_other_iff (r := a)
    (A := v (ResetUnion.literalName (i, true))) (B := v (ResetUnion.literalName (i, false))) hab).mp hi.2).1

private theorem baseline_twoOwners_eq_union (a b : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b) :
    (baseline formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v =
      (baseline formula).eval (WinnerSet.choice a) WinnerSet.union v := by
  have hvalues : ((rails formula).map (fun t => t.eval (WinnerSet.choice a) (WinnerSet.choice b) v)) =
      (rails formula).map (fun t => t.eval (WinnerSet.choice a) WinnerSet.union v) := by
    simp only [rails, List.map_flatMap, List.map_cons, List.map_nil, literalTerm, KFOL.RawPair.Term.eval_var]
  simp only [baseline, KFOL.RawPair.Term.eval_fold, Bool.false_eq_true, ite_false]
  rw [hvalues]
  apply choiceFold_union b _ _ (havoid 0 (ResetUnion.zero_mem_support formula) true)
  intro X hX
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
  obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact havoid i hi true
  · have he := List.mem_singleton.mp ht
    subst t
    exact havoid i hi false

private theorem baseline_twoOwners_ne_b (a b : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b) :
    (baseline formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v ≠ WinnerSet.singleton b := by
  rw [baseline, KFOL.RawPair.Term.eval_fold]
  change choiceFold b _ _ ≠ WinnerSet.singleton b
  intro he
  rcases (choiceFold_eq_owner b _ _).mp he with he | ⟨X, hX, he⟩
  · exact havoid 0 (ResetUnion.zero_mem_support formula) true he
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
    obtain ⟨i, hi, ht⟩ := List.mem_flatMap.mp ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact havoid i hi true he
    · have ht := List.mem_singleton.mp ht
      subst t
      exact havoid i hi false he

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

private theorem right_twoOwners_eq_union (a b : Role) (hab : a ≠ b) (formula : CNF)
    (v : ℕ → WinnerSet Role) (havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b) :
    (right formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v =
      (right formula).eval (WinnerSet.choice a) WinnerSet.union v := by
  have hb := baseline_twoOwners_eq_union a b formula v havoid
  have hbn := baseline_twoOwners_ne_b a b formula v havoid
  simp only [right, KFOL.RawPair.Term.eval_fold, Bool.false_eq_true, ite_false,
    List.map_map, Function.comp_def, branch_second_independent]
  rw [hb]
  apply choiceFold_union b _ _ (hb ▸ hbn)
  intro X hX
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
  have hn := branch_ne_other a b hab i v (havoid i hi true)
  simpa only [branch_second_independent] using hn

private theorem right_twoOwners_ne_b (a b : Role) (hab : a ≠ b) (formula : CNF)
    (v : ℕ → WinnerSet Role) (havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b) :
    (right formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v ≠ WinnerSet.singleton b := by
  rw [right, KFOL.RawPair.Term.eval_fold]
  change choiceFold b _ _ ≠ WinnerSet.singleton b
  intro he
  rcases (choiceFold_eq_owner b _ _).mp he with he | ⟨X, hX, he⟩
  · exact baseline_twoOwners_ne_b a b formula v havoid he
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ht
    exact branch_ne_other a b hab i v (havoid i hi true) he

private theorem left_twoOwners_eq_union (a b : Role) (formula : CNF)
    (hnonempty : ∀ C ∈ formula, C ≠ []) (v : ℕ → WinnerSet Role)
    (havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b) :
    (left formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v =
      (left formula).eval (WinnerSet.choice a) WinnerSet.union v := by
  have hvalues : (formula.map clause).map (fun t => t.eval (WinnerSet.choice a) (WinnerSet.choice b) v) =
      (formula.map clause).map (fun t => t.eval (WinnerSet.choice a) WinnerSet.union v) := by
    simp only [List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro C hc
    apply clause_twoOwners_eq_union a b C (hnonempty C hc) v
    intro literal hl
    exact havoid literal.1 (ResetUnion.literal_mem_support formula C hc literal hl) literal.2
  simp only [left, KFOL.RawPair.Term.eval_fold, ite_true, KFOL.RawPair.Term.eval_var]
  rw [hvalues]

private theorem left_twoOwners_ne_b (a b : Role) (hab : a ≠ b) (formula : CNF) (hformula : formula ≠ [])
    (hnonempty : ∀ C ∈ formula, C ≠ []) (v : ℕ → WinnerSet Role)
    (havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b) :
    (left formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v ≠ WinnerSet.singleton b := by
  rw [left, KFOL.RawPair.Term.eval_fold]
  change choiceFold a _ _ ≠ WinnerSet.singleton b
  intro he
  have hall := ((choiceFold_eq_other a b hab _ _).mp he).2
  obtain ⟨C, hc⟩ := List.exists_mem_of_ne_nil formula hformula
  have hvalue := hall _ (List.mem_map.mpr ⟨clause C, List.mem_map.mpr ⟨C, hc, rfl⟩, rfl⟩)
  apply clause_twoOwners_ne_b a b C (hnonempty C hc) v _ hvalue
  intro literal hl
  exact havoid literal.1 (ResetUnion.literal_mem_support formula C hc literal hl) literal.2

/-- After the outer absorbing rails are excluded, both actual native sides
agree with the choice/union construction. No expansion or finite sample is used. -/
theorem core_twoOwners_eq_union (a b : Role) (hab : a ≠ b) (formula : CNF) (hformula : formula ≠ [])
    (hnonempty : ∀ C ∈ formula, C ≠ []) (v : ℕ → WinnerSet Role)
    (havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b) :
    (coreEquation formula).1.eval (WinnerSet.choice a) (WinnerSet.choice b) v =
        (coreEquation formula).1.eval (WinnerSet.choice a) WinnerSet.union v ∧
      (coreEquation formula).2.eval (WinnerSet.choice a) (WinnerSet.choice b) v =
        (coreEquation formula).2.eval (WinnerSet.choice a) WinnerSet.union v := by
  refine ⟨?_, right_twoOwners_eq_union a b hab formula v havoid⟩
  change WinnerSet.choice b ((left formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v)
    ((right formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v) =
    WinnerSet.union ((left formula).eval (WinnerSet.choice a) WinnerSet.union v)
      ((right formula).eval (WinnerSet.choice a) WinnerSet.union v)
  simp only [WinnerSet.choice, left_twoOwners_ne_b a b hab formula hformula hnonempty v havoid,
    right_twoOwners_ne_b a b hab formula v havoid, or_self, ite_false]
  rw [left_twoOwners_eq_union a b formula hnonempty v havoid,
    right_twoOwners_eq_union a b hab formula v havoid]

theorem core_twoOwners_valid_of_absorbing_rail (a b : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (i : ℕ) (hi : i ∈ ResetUnion.support formula) (sign : Bool)
    (he : v (ResetUnion.literalName (i, sign)) = WinnerSet.singleton b) :
    (coreEquation formula).1.eval (WinnerSet.choice a) (WinnerSet.choice b) v =
      (coreEquation formula).2.eval (WinnerSet.choice a) (WinnerSet.choice b) v := by
  have hW : (baseline formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v = WinnerSet.singleton b := by
    rw [baseline, KFOL.RawPair.Term.eval_fold]
    apply (choiceFold_eq_owner b _ _).mpr
    right
    exact ⟨_, List.mem_map.mpr ⟨literalTerm (i, sign), literalTerm_mem_rails formula i hi sign, rfl⟩, he⟩
  have hR : (right formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v = WinnerSet.singleton b := by
    rw [right, KFOL.RawPair.Term.eval_fold]
    apply (choiceFold_eq_owner b _ _).mpr
    exact Or.inl hW
  change WinnerSet.choice b ((left formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v)
    ((right formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v) =
      (right formula).eval (WinnerSet.choice a) (WinnerSet.choice b) v
  rw [hR]
  apply (WinnerSet.choice_eq_owner_iff _ _ b).mpr
  exact Or.inr rfl

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

universe u

variable {Role : Type u}

theorem core_twoOwners_valid_of_unsatisfiable (a b : Role) (hab : a ≠ b) (formula : CNF)
    (hformula : formula ≠ []) (hnonempty : ∀ C ∈ formula, C ≠ []) (hu : ¬Satisfiable formula)
    (v : ℕ → WinnerSet Role) :
    (coreEquation formula).1.eval (WinnerSet.choice a) (WinnerSet.choice b) v =
      (coreEquation formula).2.eval (WinnerSet.choice a) (WinnerSet.choice b) v := by
  classical
  by_cases hex : ∃ i ∈ ResetUnion.support formula, ∃ sign,
      v (ResetUnion.literalName (i, sign)) = WinnerSet.singleton b
  · obtain ⟨i, hi, sign, he⟩ := hex
    exact core_twoOwners_valid_of_absorbing_rail a b formula v i hi sign he
  · have havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
        v (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b := by
      intro i hi sign he
      exact hex ⟨i, hi, sign, he⟩
    obtain ⟨heL, heR⟩ := core_twoOwners_eq_union a b hab formula hformula hnonempty v havoid
    rw [heL, heR]
    exact core_union_valid_of_unsatisfiable a formula hnonempty hu v

theorem core_twoOwners_satisfying_separates (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (formula : CNF) (hformula : formula ≠ [])
    (assignment : ℕ → Bool)
    (hsat : ∀ C ∈ formula, ∃ literal ∈ C, assignment literal.1 = literal.2) :
    let v := satisfyingValuation a b c assignment
    b ∈ ((coreEquation formula).1.eval (WinnerSet.choice a) (WinnerSet.choice b) v).val ∧
      b ∉ ((coreEquation formula).2.eval (WinnerSet.choice a) (WinnerSet.choice b) v).val := by
  have hnonempty : ∀ C ∈ formula, C ≠ [] := by
    intro C hc he
    obtain ⟨literal, hl, _⟩ := hsat C hc
    simp only [he, List.not_mem_nil] at hl
  have havoid : ∀ i ∈ ResetUnion.support formula, ∀ sign,
      satisfyingValuation a b c assignment (ResetUnion.literalName (i, sign)) ≠ WinnerSet.singleton b := by
    intro i _ sign he
    have hn := satisfying_literal_not_marker a b c hab hcb assignment (i, sign)
    apply hn
    rw [he]
    rfl
  obtain ⟨heL, heR⟩ := core_twoOwners_eq_union a b hab formula hformula hnonempty
    (satisfyingValuation a b c assignment) havoid
  dsimp only
  rw [heL, heR]
  exact core_union_satisfying_separates a b c hab hac hcb formula assignment hsat

/-- Full ordinary natural-variable native reduction for two raw owners.
Both exceptional CNF cases are handled by actual fixed equation outputs. -/
theorem twoOwners_equation_valid_iff_unsatisfiable (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (formula : CNF) :
    (∀ v : ℕ → WinnerSet Role,
      (twoOwnerEquation formula).1.eval (WinnerSet.choice a) (WinnerSet.choice b) v =
        (twoOwnerEquation formula).2.eval (WinnerSet.choice a) (WinnerSet.choice b) v) ↔ ¬Satisfiable formula := by
  classical
  by_cases hf : formula = []
  · subst formula
    simp only [twoOwnerEquation, List.isEmpty_nil, ite_true]
    constructor
    · intro hv
      have he := hv (fun j => if j = 0 then WinnerSet.singleton a else WinnerSet.singleton b)
      have heab : a = b := by simpa only [KFOL.RawPair.Term.eval_var, ite_true,
        Nat.one_ne_zero, ite_false, WinnerSet.singleton_inj] using he
      exact False.elim (hab heab)
    · intro hu
      exact False.elim (hu ⟨fun _ => false, by simp⟩)
  · have hbool : formula.isEmpty = false := by cases formula <;> simp_all
    simp only [twoOwnerEquation, hbool, Bool.false_eq_true, ite_false]
    by_cases he : formula.any List.isEmpty = true
    · have hu := unsatisfiable_of_empty_clause formula he
      simp only [equation, he, ite_true]
      exact ⟨fun _ => hu, fun _ _ => trivial⟩
    · have hnonempty := clauses_nonempty_of_no_empty formula he
      simp only [equation, he]
      constructor
      · intro hv ⟨assignment, hs⟩
        obtain ⟨hl, hr⟩ := core_twoOwners_satisfying_separates a b c hab hac hcb formula hf assignment hs
        exact hr ((hv _).symm ▸ hl)
      · intro hu
        exact core_twoOwners_valid_of_unsatisfiable a b hab formula hf hnonempty hu

end KFOL.Reductions.RawPair
