module

public import KFOL.Policies.Hardness

/-! Sparse native-tree CNF equations for finite policy families. -/

@[expose] public section

namespace KFOL.Policies.Hardness

universe u v w x

open KFOL.Reductions

namespace Plan

variable {Role : Type u} {Label : Type v}

@[simp] theorem eval_rightComb (D : Label → Set Role)
    (trees : List (Tree (Role := Role) (Label := Label)))
    (base : Tree (Role := Role) (Label := Label)) (valuation : Variable Role → WinnerSet Role) :
    (rightComb trees base).eval D valuation =
      (trees.map (fun tree => tree.eval D valuation)).foldr WinnerSet.reset (base.eval D valuation) := by
  induction trees with
  | nil => rfl
  | cons tree trees ih => simp only [rightComb, List.foldr_cons, Term.eval_step, List.map_cons] at *; rw [ih]

@[simp] theorem eval_clause (plan : Plan Role Label) (D : Label → Set Role)
    (clause : Clause) (valuation : Variable Role → WinnerSet Role) :
    (plan.clause clause).eval D valuation =
      clauseValue (plan.zero.eval D) (plan.one.eval D) (valuation .root)
        (fun i => valuation (.boolean i)) (valuation .marker) clause := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
    rw [Plan.clause, PolicyExpr.eval_gate, ih, clauseValue]
    cases literal.2 <;> rfl

@[simp] theorem root_rightComb (trees : List (Tree (Role := Role) (Label := Label)))
    (base : Tree (Role := Role) (Label := Label)) : (rightComb trees base).root = base.root := by
  induction trees <;> simp_all [rightComb]

@[simp] theorem root_baseline (plan : Plan Role Label) (formula : CNF) :
    (plan.baseline formula).root = .root := by simp [baseline]

@[simp] theorem root_right (plan : Plan Role Label) (formula : CNF) :
    (plan.right formula).root = .root := by simp [right]

end Plan
end KFOL.Policies.Hardness

namespace KFOL.Policies.Hardness.Plan

universe u v w x

open KFOL.Reductions

variable {Role : Type u} {Label : Type v}

@[simp] theorem eval_gates_nil (D : Label → Set Role) (valuation : Variable Role → WinnerSet Role) :
    (gates ([] : List (Label × Variable Role))).eval D valuation = valuation .marker := rfl

@[simp] theorem eval_gates_cons (D : Label → Set Role) (valuation : Variable Role → WinnerSet Role)
    (test : Label × Variable Role) (tests : List (Label × Variable Role)) :
    (gates (test :: tests)).eval D valuation =
      WinnerSet.policyReset (D test.1) (valuation .root) (valuation test.2) ((gates tests).eval D valuation) := by
  rfl

theorem mem_gates_outside (D : Label → Set Role) (tests : List (Label × Variable Role))
    (valuation : Variable Role → WinnerSet Role) (W : WinnerSet Role) (w : Role)
    (hz : (valuation .root).Ambiguous) (hZW : (valuation .root).val ⊆ W.val)
    (ht : ∀ test ∈ tests, (valuation test.2).val ⊆ W.val) (hw : w ∉ W.val) :
    w ∈ ((gates tests).eval D valuation).val ↔ w ∈ (valuation .marker).val ∧
      ∀ test ∈ tests, WinnerSet.PolicyPasses (D test.1) w (valuation test.2) := by
  induction tests with
  | nil => simp
  | cons test tests ih =>
    rw [eval_gates_cons, WinnerSet.policyReset_marker _ _ _ _ W w hz hZW
      (ht test (List.mem_cons_self ..)) hw,
      ih (fun t h => ht t (List.mem_cons_of_mem _ h))]
    simp only [List.forall_mem_cons]
    tauto

theorem mem_baseline (plan : Plan Role Label) (D : Label → Set Role) (formula : CNF)
    (valuation : Variable Role → WinnerSet Role) (hz : (valuation .root).Ambiguous) (w : Role) :
    w ∈ ((plan.baseline formula).eval D valuation).val ↔
      w ∈ (valuation .root).val ∨ ∃ input ∈ plan.inputs formula, w ∈ (valuation input).val := by
  rw [baseline, eval_rightComb, Term.eval_var, KFOL.Reductions.WinnerSetFold.mem_right _ _ hz]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨_, ⟨tree, ⟨input, hi, rfl⟩, rfl⟩, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨input, hi, hw⟩
  · rintro (h | ⟨input, hi, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨valuation input, ⟨.var input, ⟨input, hi, rfl⟩, rfl⟩, hw⟩

theorem positiveTest_input (plan : Plan Role Label) (formula : CNF)
    (test : Label × Variable Role) (ht : test ∈ plan.positiveTests formula) :
    test.2 ∈ plan.inputs formula := by
  simp only [positiveTests, List.mem_append, List.mem_flatMap, List.mem_map] at ht
  rcases ht with ⟨i, hi, d, _, rfl⟩ | ⟨item, hi, d, _, rfl⟩
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨item, hi, rfl⟩)

@[simp] theorem ambiguous_baseline (plan : Plan Role Label) (D : Label → Set Role)
    (formula : CNF) (valuation : Variable Role → WinnerSet Role) :
    ((plan.baseline formula).eval D valuation).Ambiguous ↔ (valuation .root).Ambiguous := by
  rw [Term.ambiguous_iff, root_baseline]

@[simp] theorem ambiguous_right (plan : Plan Role Label) (D : Label → Set Role)
    (formula : CNF) (valuation : Variable Role → WinnerSet Role) :
    ((plan.right formula).eval D valuation).Ambiguous ↔ (valuation .root).Ambiguous := by
  rw [Term.ambiguous_iff, root_right]

theorem mem_right (plan : Plan Role Label) (D : Label → Set Role) (formula : CNF)
    (valuation : Variable Role → WinnerSet Role) (hz : (valuation .root).Ambiguous) (w : Role) :
    w ∈ ((plan.right formula).eval D valuation).val ↔
      w ∈ ((plan.baseline formula).eval D valuation).val ∨
      (∃ clause ∈ formula, w ∈ ((plan.clause clause).eval D valuation).val) ∨
      ∃ branch ∈ plan.calibrationBranches, w ∈ (branch.eval D valuation).val := by
  rw [right, eval_rightComb, KFOL.Reductions.WinnerSetFold.mem_right _ _
    ((plan.ambiguous_baseline D formula valuation).mpr hz)]
  simp only [List.map_append, List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨_, (⟨_, ⟨clause, hc, rfl⟩, rfl⟩ | ⟨branch, hb, rfl⟩), hw⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨clause, hc, hw⟩)
    · exact Or.inr (Or.inr ⟨branch, hb, hw⟩)
  · rintro (h | ⟨clause, hc, hw⟩ | ⟨branch, hb, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, Or.inl ⟨_, ⟨clause, hc, rfl⟩, rfl⟩, hw⟩
    · exact Or.inr ⟨_, Or.inr ⟨branch, hb, rfl⟩, hw⟩

end KFOL.Policies.Hardness.Plan

namespace KFOL.Policies.Hardness.Plan

universe u v w x

open KFOL.Reductions

variable {Role : Type u} {Label : Type v}

/-- Incidence certificate for a fixed family. Subsequent construction obtains
this certificate from the negation of `FamilyEasy`; it is not an assumption
exported by the dichotomy theorem. -/
theorem baseline_subset_right (plan : Plan Role Label) (D : Label → Set Role)
    (formula : CNF) (valuation : Variable Role → WinnerSet Role)
    (hz : (valuation .root).Ambiguous) :
    ((plan.baseline formula).eval D valuation).val ⊆ ((plan.right formula).eval D valuation).val :=
  fun _ h => (plan.mem_right D formula valuation hz _).mpr (Or.inl h)

theorem input_subset_baseline (plan : Plan Role Label) (D : Label → Set Role)
    (formula : CNF) (valuation : Variable Role → WinnerSet Role)
    (hz : (valuation .root).Ambiguous) (input : Variable Role) (hi : input ∈ plan.inputs formula) :
    (valuation input).val ⊆ ((plan.baseline formula).eval D valuation).val :=
  fun _ h => (plan.mem_baseline D formula valuation hz _).mpr (Or.inr ⟨input, hi, h⟩)

theorem root_subset_baseline (plan : Plan Role Label) (D : Label → Set Role)
    (formula : CNF) (valuation : Variable Role → WinnerSet Role)
    (hz : (valuation .root).Ambiguous) :
    (valuation .root).val ⊆ ((plan.baseline formula).eval D valuation).val :=
  fun _ h => (plan.mem_baseline D formula valuation hz _).mpr (Or.inl h)

theorem calibration_identified (plan : Plan Role Label) (D : Label → Set Role)
    (cert : Certificate D plan) (formula : CNF) (valuation : Variable Role → WinnerSet Role)
    (hz : (valuation .root).Ambiguous) (w : Role)
    (hP : w ∈ ((gates (plan.positiveTests formula)).eval D valuation).val)
    (hR : w ∉ ((plan.right formula).eval D valuation).val)
    (item : Role × List Label × List Label) (hitem : item ∈ plan.calibration) :
    valuation (.calibration item.1) = WinnerSet.singleton item.1 := by
  let W := (plan.baseline formula).eval D valuation
  have hw : w ∉ W.val := fun h => hR (plan.baseline_subset_right D formula valuation hz h)
  have hZW := plan.root_subset_baseline D formula valuation hz
  have htests : ∀ test ∈ plan.positiveTests formula, (valuation test.2).val ⊆ W.val :=
    fun test ht => plan.input_subset_baseline D formula valuation hz _ (plan.positiveTest_input formula test ht)
  obtain ⟨hC, hpos⟩ := (mem_gates_outside D _ valuation W w hz hZW htests hw).mp hP
  have hUrW : (valuation (.calibration item.1)).val ⊆ W.val :=
    plan.input_subset_baseline D formula valuation hz _
      (List.mem_append_right _ (List.mem_map.mpr ⟨item, hitem, rfl⟩))
  have hUr : w ∉ (valuation (.calibration item.1)).val := fun h => hw (hUrW h)
  have hbranch : ∀ branch ∈ plan.calibrationBranches, w ∉ (branch.eval D valuation).val := by
    intro branch hb hmem
    exact hR ((plan.mem_right D formula valuation hz w).mpr (Or.inr (Or.inr ⟨branch, hb, hmem⟩)))
  have htestbranch : Term.step (.var .marker) (.var (.calibration item.1)) ∈ plan.calibrationBranches := by
    exact List.mem_flatMap.mpr ⟨item, hitem, List.mem_cons_self ..⟩
  have hm : ¬(valuation (.calibration item.1)).Ambiguous := by
    intro hm
    apply hbranch _ htestbranch
    rw [Term.eval_step, Term.eval_var, Term.eval_var, WinnerSet.mem_reset]
    exact Or.inr ⟨hm, hC⟩
  apply calibration_eq_singleton D (cert.calibration_injective item hitem) item.1 w _ hUr hm
  intro d
  by_cases hd : item.1 ∈ D d
  · have hdneg := (cert.calibration_negative item hitem d).mpr hd
    have hb : Term.selective d (.var .root) (.var (.calibration item.1)) (.var .marker) ∈
        plan.calibrationBranches :=
      List.mem_flatMap.mpr ⟨item, hitem, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨d, hdneg, rfl⟩)⟩
    have hn : ¬WinnerSet.PolicyPasses (D d) w (valuation (.calibration item.1)) := by
      intro hp
      apply hbranch _ hb
      rw [Term.eval_selective, Term.eval_var, Term.eval_var, Term.eval_var,
        WinnerSet.policyReset_marker _ _ _ _ W w hz hZW hUrW hw]
      exact ⟨hp, hC⟩
    exact iff_of_false hn (not_not_intro hd)
  · have hdpos := (cert.calibration_positive item hitem d).mpr hd
    have ht : (d, Variable.calibration item.1) ∈ plan.positiveTests formula :=
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨item, hitem, List.mem_map.mpr ⟨d, hdpos, rfl⟩⟩)
    exact iff_of_true (hpos _ ht) hd

end KFOL.Policies.Hardness.Plan

namespace KFOL.Policies.Hardness.Plan

universe u v w x

open KFOL.Reductions

variable {Role : Type u} {Label : Type v}

/-- Unconditional correctness of the constructed native equation in the UNSAT
direction once the fixed-family incidence certificate has been constructed. -/
theorem valid_of_unsatisfiable (plan : Plan Role Label) (D : Label → Set Role)
    (cert : Certificate D plan) (formula : CNF) (hunsat : ¬Satisfiable formula)
    (valuation : Variable Role → WinnerSet Role) :
    (plan.left formula).eval D valuation = (plan.right formula).eval D valuation := by
  classical
  by_cases hz : (valuation .root).Ambiguous
  · apply Subtype.ext
    ext w
    rw [left, Term.eval_step, WinnerSet.mem_reset]
    simp only [(plan.ambiguous_right D formula valuation).mpr hz, true_and]
    constructor
    · rintro (h | hP)
      · exact h
      · by_contra hR
        let W := (plan.baseline formula).eval D valuation
        have hw : w ∉ W.val := fun h => hR (plan.baseline_subset_right D formula valuation hz h)
        have hZW := plan.root_subset_baseline D formula valuation hz
        have htests : ∀ test ∈ plan.positiveTests formula, (valuation test.2).val ⊆ W.val :=
          fun test ht => plan.input_subset_baseline D formula valuation hz _ (plan.positiveTest_input formula test ht)
        obtain ⟨hC, hpos⟩ := (mem_gates_outside D _ valuation W w hz hZW htests hw).mp hP
        have hexcluded : ∀ item ∈ plan.calibration, w ≠ item.1 := by
          intro item hi he
          have hcal := plan.calibration_identified D cert formula valuation hz w hP hR item hi
          apply hw
          apply plan.input_subset_baseline D formula valuation hz (.calibration item.1)
            (List.mem_append_right _ (List.mem_map.mpr ⟨item, hi, rfl⟩))
          rw [hcal]
          simpa only [WinnerSet.val_singleton, Set.mem_singleton_iff] using he
        have hpairs : ∀ i ∈ KFOL.Reductions.ResetUnion.support formula,
            WinnerSet.PolicyPasses (plan.zero.eval D) w (valuation (.boolean i)) ∨
              WinnerSet.PolicyPasses (plan.one.eval D) w (valuation (.boolean i)) := by
          intro i hi
          apply (WinnerSet.policyPasses_inter _ _ w _).mp
          intro r hr hrw hY
          have hclear : ∀ d ∈ plan.preliminary, r ∉ D d := by
            intro d hd hrD
            have ht : (d, Variable.boolean i) ∈ plan.positiveTests formula :=
              List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, hi, List.mem_map.mpr ⟨d, hd, rfl⟩⟩)
            exact hpos _ ht r hrD hrw hY
          exact hrw (cert.intersection w hexcluded r hr.1 hr.2 hclear)
        obtain ⟨clause, hc, hpass⟩ := exists_passing_clause _ _ formula
          (fun i => valuation (.boolean i)) w hpairs hunsat
        have hclause : w ∈ ((plan.clause clause).eval D valuation).val := by
          rw [eval_clause, mem_clauseValue_outside _ _ _ W _ _ clause w hz hZW _ hw]
          · exact ⟨hC, hpass⟩
          · intro literal hl
            exact plan.input_subset_baseline D formula valuation hz (.boolean literal.1)
              (List.mem_append_left _ (List.mem_map.mpr ⟨literal.1,
                literal_mem_support formula clause hc literal hl, rfl⟩))
        exact hR ((plan.mem_right D formula valuation hz w).mpr
          (Or.inr (Or.inl ⟨clause, hc, hclause⟩)))
    · exact Or.inl
  · unfold WinnerSet.Ambiguous at hz
    push Not at hz
    obtain ⟨r, hr⟩ := hz
    have hR : (plan.right formula).eval D valuation = WinnerSet.singleton r := by
      apply ((plan.right formula).eq_singleton_iff D valuation r).mpr
      simpa only [root_right] using hr
    simp only [left, Term.eval_step, hR, WinnerSet.reset_singleton]

end KFOL.Policies.Hardness.Plan

namespace KFOL.Policies.Hardness.Plan

universe u v w x

open KFOL.Reductions

variable {Role : Type u} {Label : Type v}

/- Every satisfying assignment supplies a concrete singleton-or-pair
valuation. Calibration leaves receive their actual role's singleton. -/

/-- The SAT direction exhibits a separating valuation of the actual native
tree equation, including every calibration branch. -/
theorem exists_separating_valuation (plan : Plan Role Label) (D : Label → Set Role)
    (cert : Certificate D plan) (formula : CNF) (hsat : Satisfiable formula) :
    ∃ valuation : Variable Role → WinnerSet Role,
      (plan.left formula).eval D valuation ≠ (plan.right formula).eval D valuation := by
  classical
  obtain ⟨assignment, hassignment⟩ := hsat
  let valuation := satisfyingValuation cert assignment
  have hz : (valuation .root).Ambiguous :=
    WinnerSet.ambiguous_of_two_mem _ cert.a cert.b cert.a_ne_b (Or.inl rfl) (Or.inr rfl)
  let W := (plan.baseline formula).eval D valuation
  have hZW := plan.root_subset_baseline D formula valuation hz
  have hinput (input : Variable Role) (hi : input ∈ plan.inputs formula) :
      cert.marker ∉ (valuation input).val := by
    simp only [inputs, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨i, _, rfl⟩ | ⟨item, hi, rfl⟩
    · cases h : assignment i <;>
        simp only [valuation, satisfyingValuation, h, Bool.false_eq_true, ↓reduceIte,
          WinnerSet.val_singleton, Set.mem_singleton_iff]
      · exact cert.b_ne_marker.symm
      · exact cert.a_ne_marker.symm
    · simpa only [valuation, satisfyingValuation, WinnerSet.val_singleton, Set.mem_singleton_iff]
        using (cert.calibration_marker item hi).symm
  have hw : cert.marker ∉ W.val := by
    rw [mem_baseline _ D _ _ hz]
    rintro (h | ⟨input, hi, hmem⟩)
    · exact h.elim cert.a_ne_marker.symm cert.b_ne_marker.symm
    · exact hinput input hi hmem
  have htests : ∀ test ∈ plan.positiveTests formula, (valuation test.2).val ⊆ W.val :=
    fun test ht => plan.input_subset_baseline D formula valuation hz _ (plan.positiveTest_input formula test ht)
  have hpositive : ∀ test ∈ plan.positiveTests formula,
      WinnerSet.PolicyPasses (D test.1) cert.marker (valuation test.2) := by
    intro test ht
    simp only [positiveTests, List.mem_append, List.mem_flatMap, List.mem_map] at ht
    rcases ht with ⟨i, _, d, hd, rfl⟩ | ⟨item, hi, d, hd, rfl⟩
    · have hc := cert.preliminary_clear d hd
      cases h : assignment i <;>
        simp only [valuation, satisfyingValuation, h, Bool.false_eq_true, ↓reduceIte,
          WinnerSet.policyPasses_singleton]
      · exact Or.inl hc.2
      · exact Or.inl hc.1
    · apply (WinnerSet.policyPasses_singleton _ _ _).mpr
      exact Or.inl ((cert.calibration_positive item hi d).mp hd)
  have hP : cert.marker ∈ ((gates (plan.positiveTests formula)).eval D valuation).val := by
    apply (mem_gates_outside D _ valuation W cert.marker hz hZW htests hw).mpr
    exact ⟨rfl, hpositive⟩
  have hclauses : ∀ clause ∈ formula, cert.marker ∉ ((plan.clause clause).eval D valuation).val := by
    intro clause hc hmem
    have hall := ((mem_clauseValue_outside _ _ _ W _ _ clause cert.marker hz hZW
      (fun literal hl => plan.input_subset_baseline D formula valuation hz (.boolean literal.1)
        (List.mem_append_left _ (List.mem_map.mpr ⟨literal.1,
          literal_mem_support formula clause hc literal hl, rfl⟩))) hw).mp
      ((congrArg (fun A : WinnerSet Role => cert.marker ∈ A.val) (plan.eval_clause D clause valuation)).mp hmem)).2
    obtain ⟨literal, hl, htruth⟩ := hassignment clause hc
    have hp := hall literal hl
    cases hb : literal.2
    · have hi : assignment literal.1 = false := htruth.trans hb
      have he : cert.b = cert.marker := by
        simpa only [hb, Bool.false_eq_true, ↓reduceIte, valuation, satisfyingValuation, hi,
          WinnerSet.policyPasses_singleton, cert.b_one, not_true_eq_false, false_or] using hp
      exact cert.b_ne_marker he
    · have hi : assignment literal.1 = true := htruth.trans hb
      have he : cert.a = cert.marker := by
        simpa only [hb, ↓reduceIte, valuation, satisfyingValuation, hi,
          WinnerSet.policyPasses_singleton, cert.a_zero, not_true_eq_false, false_or] using hp
      exact cert.a_ne_marker he
  have hcalibration : ∀ branch ∈ plan.calibrationBranches, cert.marker ∉ (branch.eval D valuation).val := by
    intro branch hb
    obtain ⟨item, hi, hb⟩ := List.mem_flatMap.mp hb
    rcases List.mem_cons.mp hb with rfl | hb
    · simp only [Term.eval_step, Term.eval_var, valuation, satisfyingValuation, WinnerSet.reset_singleton]
      simpa only [WinnerSet.val_singleton, Set.mem_singleton_iff] using (cert.calibration_marker item hi).symm
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
      have hUrW : (valuation (.calibration item.1)).val ⊆ W.val :=
        plan.input_subset_baseline D formula valuation hz _
          (List.mem_append_right _ (List.mem_map.mpr ⟨item, hi, rfl⟩))
      rw [Term.eval_selective, Term.eval_var, Term.eval_var, Term.eval_var,
        WinnerSet.policyReset_marker _ _ _ _ W cert.marker hz hZW hUrW hw]
      rintro ⟨hp, _⟩
      have hdD := (cert.calibration_negative item hi d).mp hd
      have he : item.1 = cert.marker := by
        simpa only [valuation, satisfyingValuation, WinnerSet.policyPasses_singleton,
          hdD, not_true_eq_false, false_or] using hp
      exact cert.calibration_marker item hi he
  have hR : cert.marker ∉ ((plan.right formula).eval D valuation).val := by
    rw [plan.mem_right D formula valuation hz]
    rintro (h | ⟨clause, hc, hmem⟩ | ⟨branch, hb, hmem⟩)
    · exact hw h
    · exact hclauses clause hc hmem
    · exact hcalibration branch hb hmem
  refine ⟨valuation, ?_⟩
  intro he
  apply hR
  rw [← he, left, Term.eval_step, WinnerSet.mem_reset]
  exact Or.inr ⟨(plan.ambiguous_right D formula valuation).mpr hz, hP⟩

/-- Exact reduction correctness, valid for every CNF including empty formulas
and empty clauses; size bounds use the separate width-three source gate. -/
theorem valid_iff_unsatisfiable (plan : Plan Role Label) (D : Label → Set Role)
    (cert : Certificate D plan) (formula : CNF) :
    (∀ valuation : Variable Role → WinnerSet Role,
      (plan.equation formula).1.eval D valuation = (plan.equation formula).2.eval D valuation) ↔
      ¬Satisfiable formula := by
  constructor
  · intro hv hs
    obtain ⟨valuation, hne⟩ := plan.exists_separating_valuation D cert formula hs
    exact hne (hv valuation)
  · exact plan.valid_of_unsatisfiable D cert formula

end KFOL.Policies.Hardness.Plan

namespace KFOL.Policies.Term

universe u v w x

variable {Role : Type u} {Label : Type v} {Var : Type w} {Var' : Type x}

@[simp] theorem eval_relabel (D : Label → Set Role) (t : Term Label Var) (f : Var → Var')
    (valuation : Var' → WinnerSet Role) :
    eval D (t.relabel f) valuation = t.eval D (valuation ∘ f) := by
  let _ := structureOf D
  exact FirstOrder.Language.Term.realize_relabel

@[simp] theorem size_relabel (t : Term Label Var) (f : Var → Var') :
    size (t.relabel f) = t.size := by
  induction t using induction_policy with
  | var => rfl
  | step s t hs ht =>
    change 1 + size (s.relabel f) + size (t.relabel f) = 1 + s.size + t.size
    rw [hs, ht]
  | selective d x y z hx hy hz =>
    change 1 + size (x.relabel f) + size (y.relabel f) + size (z.relabel f) =
      1 + x.size + y.size + z.size
    rw [hx, hy, hz]

theorem relabel_equation_valid_iff (D : Label → Set Role) (s t : Term Label Var) (f : Var ↪ Var') :
    (∀ valuation : Var' → WinnerSet Role,
      eval D (s.relabel f) valuation = eval D (t.relabel f) valuation) ↔
    (∀ valuation : Var → WinnerSet Role, s.eval D valuation = t.eval D valuation) := by
  constructor
  · intro h valuation
    have he := h (Function.extend f valuation (fun _ => valuation s.root))
    rw [eval_relabel, eval_relabel] at he
    have hcomp : Function.extend f valuation (fun _ => valuation s.root) ∘ f = valuation := by
      funext x
      exact f.injective.extend_apply _ _ x
    simpa only [hcomp] using he
  · intro h valuation
    simpa only [eval_relabel] using h (valuation ∘ f)

end KFOL.Policies.Term

namespace KFOL.Policies.Hardness.Variable

universe u v w x

variable {Role : Type u}

/-- Sparse binary names preserve arbitrary source Boolean labels. The finite
role dictionary only supplies the disjoint odd calibration names. -/
theorem toNat_injective (code : Role ↪ ℕ) : Function.Injective (toNat code) := by
  intro x y he
  cases x <;> cases y <;> simp only [toNat] at he
  all_goals first
    | rfl
    | exact False.elim (by omega)
    | (apply congrArg Variable.boolean; omega)
    | (apply congrArg Variable.calibration; apply code.injective; omega)

def embeddingNat (code : Role ↪ ℕ) : Variable Role ↪ ℕ := ⟨toNat code, toNat_injective code⟩

end KFOL.Policies.Hardness.Variable
