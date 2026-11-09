module

public import KFOL.Reductions.Circuits.ResetCNF

/-! Marker semantics of shared reset clause gates. -/

@[expose] public section

namespace KFOL.Circuit.ResetCNF

open KFOL.Reductions

universe u

variable {Role : Type u}

noncomputable local instance : (Equational.language Reset.Symbol).Structure (WinnerSet Role) :=
  Reset.structureOf WinnerSet.reset

/- A clause uses one shared preceding output at each literal test. -/
@[simp] theorem clauseValue_ambiguous (root previous : WinnerSet Role) (literals : List (WinnerSet Role)) :
    (clauseValue root previous literals).Ambiguous ↔ root.Ambiguous := WinnerSetFold.ambiguous_right _ _

theorem clauseValue_marker (root previous : WinnerSet Role) (literals : List (WinnerSet Role))
    (hz : root.Ambiguous) (marker : Role) (hroot : marker ∉ root.val)
    (hliterals : ∀ literal ∈ literals, marker ∉ literal.val) :
    marker ∈ (clauseValue root previous literals).val ↔
      marker ∈ previous.val ∧ ∃ literal ∈ literals, literal.Ambiguous := by
  rw [clauseValue, WinnerSetFold.mem_right _ _ hz]
  simp only [hroot, false_or, List.mem_map]
  constructor
  · rintro ⟨_, ⟨literal, hl, rfl⟩, hm⟩
    obtain ⟨ha, hm⟩ := ((WinnerSet.mem_reset _ _ marker).mp hm).resolve_left (hliterals literal hl)
    exact ⟨hm, literal, hl, ha⟩
  · rintro ⟨hm, literal, hl, ha⟩
    exact ⟨_, ⟨literal, hl, rfl⟩, (WinnerSet.mem_reset _ _ marker).mpr (Or.inr ⟨ha, hm⟩)⟩

theorem cnfValue_marker (root previous : WinnerSet Role) (clauses : List (List (WinnerSet Role)))
    (hz : root.Ambiguous) (marker : Role) (hroot : marker ∉ root.val)
    (hliterals : ∀ clause ∈ clauses, ∀ literal ∈ clause, marker ∉ literal.val) :
    marker ∈ (clauses.foldl (clauseValue root) previous).val ↔
      marker ∈ previous.val ∧ ∀ clause ∈ clauses, ∃ literal ∈ clause, literal.Ambiguous := by
  induction clauses generalizing previous with
  | nil => simp
  | cons clause clauses ih =>
    rw [List.foldl_cons, ih _ (fun c hc => hliterals c (List.mem_cons_of_mem _ hc)),
      clauseValue_marker _ _ _ hz marker hroot (hliterals clause (List.mem_cons_self ..))]
    simp only [List.forall_mem_cons]
    tauto

theorem leftValue_eq (valuation : ℕ → WinnerSet Role) (formula : CNF) :
    leftValue valuation formula =
      (formula.map (fun clause => clause.map (fun literal => valuation (ResetUnion.literalName literal)))).foldl
        (clauseValue (valuation 0)) (valuation 1) := by
  unfold leftValue
  change _ = List.foldl (fun (previous : WinnerSet Role) (clause : List (WinnerSet Role)) =>
    (clause.map (WinnerSet.reset previous)).foldr WinnerSet.reset (valuation 0)) _ _
  congr 1
  unfold clauseRefs
  rw [List.map_map]
  apply List.map_congr_left
  intro clause hc
  dsimp only [Function.comp_apply]
  rw [List.map_map]
  apply List.map_congr_left
  intro literal hl
  exact inputValue_literalRef valuation formula literal.1
    (ResetUnion.literal_mem_support formula clause hc literal hl) literal.2

theorem rightValue_eq (valuation : ℕ → WinnerSet Role) (formula : CNF) :
    rightValue valuation formula =
      ((ResetUnion.support formula).map (fun i =>
        ((valuation 1).reset (valuation (ResetUnion.literalName (i, true)))).reset
          (valuation (ResetUnion.literalName (i, false))))).foldr WinnerSet.reset (baselineValue valuation formula) := by
  unfold rightValue pairs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, inputValue_literalRef valuation formula i hi]
  rfl

theorem baselineValue_eq (valuation : ℕ → WinnerSet Role) (formula : CNF) :
    baselineValue valuation formula =
      ((ResetUnion.support formula).flatMap (fun i =>
        [valuation (ResetUnion.literalName (i, true)), valuation (ResetUnion.literalName (i, false))])).foldr
          WinnerSet.reset (valuation 0) := by
  unfold baselineValue railRefs pairs
  rw [List.flatMap_map, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro i hi
  simp only [List.map_cons, List.map_nil, inputValue_literalRef valuation formula i hi]

@[simp] theorem baselineValue_ambiguous (valuation : ℕ → WinnerSet Role) (formula : CNF) :
    (baselineValue valuation formula).Ambiguous ↔ (valuation 0).Ambiguous := by
  rw [baselineValue_eq, WinnerSetFold.ambiguous_right]

@[simp] theorem rightValue_ambiguous (valuation : ℕ → WinnerSet Role) (formula : CNF) :
    (rightValue valuation formula).Ambiguous ↔ (valuation 0).Ambiguous := by
  rw [rightValue_eq, WinnerSetFold.ambiguous_right, baselineValue_ambiguous]

theorem mem_baselineValue (valuation : ℕ → WinnerSet Role) (formula : CNF)
    (hz : (valuation 0).Ambiguous) (marker : Role) :
    marker ∈ (baselineValue valuation formula).val ↔ marker ∈ (valuation 0).val ∨
      ∃ i ∈ ResetUnion.support formula, marker ∈ (valuation (ResetUnion.literalName (i, true))).val ∨
        marker ∈ (valuation (ResetUnion.literalName (i, false))).val := by
  rw [baselineValue_eq, WinnerSetFold.mem_right _ _ hz]
  constructor
  · rintro (hr | ⟨literal, hl, hm⟩)
    · exact Or.inl hr
    · obtain ⟨i, hi, hl⟩ := List.mem_flatMap.mp hl
      rcases List.mem_cons.mp hl with rfl | hl
      · exact Or.inr ⟨i, hi, Or.inl hm⟩
      · have he := List.mem_singleton.mp hl
        subst literal
        exact Or.inr ⟨i, hi, Or.inr hm⟩
  · rintro (hr | ⟨i, hi, hp | hn⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨_, List.mem_flatMap.mpr ⟨i, hi, List.mem_cons_self ..⟩, hp⟩
    · exact Or.inr ⟨_, List.mem_flatMap.mpr ⟨i, hi, by simp⟩, hn⟩


theorem literal_subset_baselineValue (valuation : ℕ → WinnerSet Role) (formula : CNF)
    (hz : (valuation 0).Ambiguous) (i : ℕ) (hi : i ∈ ResetUnion.support formula) (sign : Bool) :
    (valuation (ResetUnion.literalName (i, sign))).val ⊆ (baselineValue valuation formula).val := by
  intro marker hm
  apply (mem_baselineValue valuation formula hz marker).mpr
  apply Or.inr
  refine ⟨i, hi, ?_⟩
  cases sign with
  | true => exact Or.inl hm
  | false => exact Or.inr hm

theorem baseline_subset_rightValue (valuation : ℕ → WinnerSet Role) (formula : CNF)
    (hz : (valuation 0).Ambiguous) :
    (baselineValue valuation formula).val ⊆ (rightValue valuation formula).val := by
  intro marker hm
  rw [rightValue_eq, WinnerSetFold.mem_right _ _ ((baselineValue_ambiguous valuation formula).mpr hz)]
  exact Or.inl hm

theorem rightValue_marker (valuation : ℕ → WinnerSet Role) (formula : CNF)
    (hz : (valuation 0).Ambiguous) (marker : Role) (hmarker : marker ∉ (baselineValue valuation formula).val) :
    marker ∈ (rightValue valuation formula).val ↔ marker ∈ (valuation 1).val ∧
      ∃ i ∈ ResetUnion.support formula, (valuation (ResetUnion.literalName (i, true))).Ambiguous ∧
        (valuation (ResetUnion.literalName (i, false))).Ambiguous := by
  rw [rightValue_eq, WinnerSetFold.mem_right _ _ ((baselineValue_ambiguous valuation formula).mpr hz)]
  simp only [hmarker, false_or, List.mem_map]
  have hbranch (i : ℕ) (hi : i ∈ ResetUnion.support formula) :=
    WinnerSetFold.mem_branch_outside (valuation 1) (valuation (ResetUnion.literalName (i, true)))
      (valuation (ResetUnion.literalName (i, false))) marker
      (fun hm => hmarker (literal_subset_baselineValue valuation formula hz i hi true hm))
      (fun hm => hmarker (literal_subset_baselineValue valuation formula hz i hi false hm))
  constructor
  · rintro ⟨_, ⟨i, hi, rfl⟩, hm⟩
    obtain ⟨hc, hp, hn⟩ := (hbranch i hi).mp hm
    exact ⟨hc, i, hi, hp, hn⟩
  · rintro ⟨hc, i, hi, hp, hn⟩
    exact ⟨_, ⟨i, hi, rfl⟩, (hbranch i hi).mpr ⟨hc, hp, hn⟩⟩

theorem leftValue_marker (valuation : ℕ → WinnerSet Role) (formula : CNF)
    (hz : (valuation 0).Ambiguous) (marker : Role) (hmarker : marker ∉ (baselineValue valuation formula).val) :
    marker ∈ (leftValue valuation formula).val ↔ marker ∈ (valuation 1).val ∧
      ∀ clause ∈ formula, ∃ literal ∈ clause, (valuation (ResetUnion.literalName literal)).Ambiguous := by
  rw [leftValue_eq, cnfValue_marker _ _ _ hz marker]
  · constructor
    · rintro ⟨hc, hall⟩
      refine ⟨hc, fun C hC => ?_⟩
      obtain ⟨value, hv, ha⟩ := hall (C.map (fun l => valuation (ResetUnion.literalName l)))
        (List.mem_map.mpr ⟨C, hC, rfl⟩)
      obtain ⟨literal, hl, rfl⟩ := List.mem_map.mp hv
      exact ⟨literal, hl, ha⟩
    · rintro ⟨hc, hall⟩
      refine ⟨hc, fun clause hclause => ?_⟩
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hclause
      obtain ⟨literal, hl, ha⟩ := hall C hC
      exact ⟨_, List.mem_map.mpr ⟨literal, hl, rfl⟩, ha⟩
  · exact fun hm => hmarker ((mem_baselineValue valuation formula hz marker).mpr (Or.inl hm))
  · intro clause hc literal hl hm
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hc
    obtain ⟨l, hlin, rfl⟩ := List.mem_map.mp hl
    exact hmarker (literal_subset_baselineValue valuation formula hz l.1
      (ResetUnion.literal_mem_support formula C hC l hlin) l.2 hm)

/- The shared reset DAG equation is valid for every actual winner valuation
when its original source CNF is unsatisfiable. -/
theorem equation_holds_of_unsatisfiable (formula : CNF) (hu : ¬Satisfiable formula) :
    (equation formula).Holds (WinnerSet Role) := by
  classical
  refine ⟨equation_wellFormed formula, fun valuation => ⟨rightValue valuation formula, ?_⟩⟩
  rw [eval_equation]
  congr 2
  by_cases hz : (valuation 0).Ambiguous
  · have hr : (rightValue valuation formula).Ambiguous := (rightValue_ambiguous valuation formula).mpr hz
    change (leftValue valuation formula).reset (rightValue valuation formula) = rightValue valuation formula
    rw [WinnerSet.reset_of_ambiguous _ _ hr]
    apply Subtype.ext
    exact Set.union_eq_right.mpr (by
      intro marker hm
      by_cases hw : marker ∈ (baselineValue valuation formula).val
      · exact baseline_subset_rightValue valuation formula hz hw
      · obtain ⟨hc, hclauses⟩ := (leftValue_marker valuation formula hz marker hw).mp hm
        obtain ⟨i, hi, hp, hn⟩ := RawPair.conflicting_predicates_of_unsatisfiable formula
          (fun i => (valuation (ResetUnion.literalName (i, true))).Ambiguous)
          (fun i => (valuation (ResetUnion.literalName (i, false))).Ambiguous) hu (by
            intro C hC
            obtain ⟨literal, hl, ha⟩ := hclauses C hC
            refine ⟨literal, hl, ?_⟩
            rcases literal with ⟨i, sign⟩
            cases sign <;> simpa only [Bool.false_eq_true, ite_false, ite_true] using ha)
        exact (rightValue_marker valuation formula hz marker hw).mpr ⟨hc, i, hi, hp, hn⟩)
  · obtain ⟨r, hr⟩ : ∃ r, valuation 0 = WinnerSet.singleton r := by
      unfold WinnerSet.Ambiguous at hz
      push Not at hz
      exact hz
    have hright : rightValue valuation formula = WinnerSet.singleton r := by
      rw [rightValue_eq, baselineValue_eq, hr, WinnerSetFold.right_singleton, WinnerSetFold.right_singleton]
    change (leftValue valuation formula).reset (rightValue valuation formula) = rightValue valuation formula
    rw [hright, WinnerSet.reset_singleton]

end KFOL.Circuit.ResetCNF
