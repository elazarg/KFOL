module

public import KFOL.Reductions.RawTwoOwners
public import KFOL.Reductions.RawSizes
public import KFOL.Reductions.ResetUnionSize

/-! The native choice/reset reduction: exact binary-tree translation of the
report's reset/union construction, with each union interpreted by one owner. -/

@[expose] public section

namespace KFOL.Reductions.ResetChoice

universe u v

variable {Role : Type u}

private noncomputable abbrev realize (a : Role) (t : KFOL.ResetUnion.Term ℕ) (v : ℕ → WinnerSet Role) : WinnerSet Role :=
  (translate t).eval WinnerSet.reset (WinnerSet.choice a) v

@[simp] private theorem realize_var (a : Role) (j : ℕ) (v : ℕ → WinnerSet Role) :
    realize a (.var j) v = v j := rfl
@[simp] private theorem realize_reset (a : Role) (s t : KFOL.ResetUnion.Term ℕ) (v : ℕ → WinnerSet Role) :
    realize a (KFOL.ResetUnion.Term.reset s t) v = (realize a s v).reset (realize a t v) := rfl
@[simp] private theorem realize_union (a : Role) (s t : KFOL.ResetUnion.Term ℕ) (v : ℕ → WinnerSet Role) :
    realize a (KFOL.ResetUnion.Term.union s t) v = WinnerSet.choice a (realize a s v) (realize a t v) := rfl

private theorem realize_rightComb (a : Role) (ts : List (KFOL.ResetUnion.Term ℕ))
    (base : KFOL.ResetUnion.Term ℕ) (v : ℕ → WinnerSet Role) :
    realize a (KFOL.ResetUnion.Term.rightComb ts base) v =
      (ts.map (fun t => realize a t v)).foldr WinnerSet.reset (realize a base v) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [KFOL.ResetUnion.Term.rightComb, List.foldr_cons, realize_reset, List.map_cons] at *; rw [ih]

private theorem realize_leftComb (a : Role) (ts : List (KFOL.ResetUnion.Term ℕ))
    (base : KFOL.ResetUnion.Term ℕ) (v : ℕ → WinnerSet Role) :
    realize a (KFOL.ResetUnion.Term.leftComb base ts) v =
      (ts.map (fun t => realize a t v)).foldl WinnerSet.reset (realize a base v) := by
  induction ts generalizing base with
  | nil => rfl
  | cons t ts ih =>
    change realize a (KFOL.ResetUnion.Term.leftComb (KFOL.ResetUnion.Term.reset base t) ts) v = _
    rw [ih]
    rfl

private theorem realize_unionFold (a : Role) (ts : List (KFOL.ResetUnion.Term ℕ))
    (base : KFOL.ResetUnion.Term ℕ) (v : ℕ → WinnerSet Role) :
    realize a (KFOL.ResetUnion.Term.unionFold base ts) v =
      (ts.map (fun t => realize a t v)).foldl (WinnerSet.choice a) (realize a base v) := by
  induction ts generalizing base with
  | nil => rfl
  | cons t ts ih =>
    change realize a (KFOL.ResetUnion.Term.unionFold (KFOL.ResetUnion.Term.union base t) ts) v = _
    rw [ih]
    rfl

private theorem realize_baseline (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role) :
    realize a (ResetUnion.baseline formula) v = (ResetUnion.baseline formula).eval v := by
  simp only [ResetUnion.baseline, realize_rightComb, KFOL.ResetUnion.Term.eval_rightComb,
    List.map_append, List.map_flatMap, List.map_cons, List.map_nil, ResetUnion.literalTerm,
    realize_var, KFOL.ResetUnion.Term.eval_var]

private theorem realize_clauseGuard (a : Role) (C : Clause) (v : ℕ → WinnerSet Role) :
    realize a (ResetUnion.clauseGuard C) v =
      RawPair.choiceFold a (C.map (fun literal => v (ResetUnion.literalName literal))) (v 0) := by
  simp only [ResetUnion.clauseGuard, realize_unionFold, realize_var, List.map_map,
    ResetUnion.literalTerm, Function.comp_def]
  exact (RawPair.choiceFold_eq_foldl a _ _).symm

end KFOL.Reductions.ResetChoice

namespace KFOL.Reductions.ResetChoice

universe u

variable {Role : Type u}

private theorem guard_subset_baseline (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (hz : (v 1).Ambiguous) (i : ℕ) (hi : i ∈ ResetUnion.support formula) (sign : Bool) :
    (WinnerSet.choice a (v (ResetUnion.literalName (i, sign))) (v 0)).val ⊆
      ((ResetUnion.baseline formula).eval v).val :=
  (WinnerSet.choice_subset_union a _ _).trans (ResetUnion.literal_guard_subset_baseline v formula hz i hi sign)

private theorem clauseGuard_subset_baseline (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (hz : (v 1).Ambiguous) (C : Clause) (hC : C ∈ formula) :
    (realize a (ResetUnion.clauseGuard C) v).val ⊆ ((ResetUnion.baseline formula).eval v).val := by
  rw [realize_clauseGuard]
  apply RawPair.choiceFold_subset
  · exact fun w hw => (ResetUnion.mem_baseline v formula hz w).mpr (Or.inr (Or.inl hw))
  · intro X hX
    obtain ⟨literal, hl, rfl⟩ := List.mem_map.mp hX
    intro w hw
    apply ResetUnion.literal_guard_subset_baseline v formula hz literal.1
      (ResetUnion.literal_mem_support formula C hC literal hl) literal.2
    exact Or.inl hw

private theorem right_ambiguous (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role) :
    (realize a (ResetUnion.right formula) v).Ambiguous ↔ (v 1).Ambiguous := by
  rw [ResetUnion.right, realize_rightComb, WinnerSetFold.ambiguous_right, realize_baseline,
    ResetUnion.baseline_ambiguous]

private theorem baseline_subset_right (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (hz : (v 1).Ambiguous) :
    ((ResetUnion.baseline formula).eval v).val ⊆ (realize a (ResetUnion.right formula) v).val := by
  intro w hw
  rw [ResetUnion.right, realize_rightComb, realize_baseline,
    WinnerSetFold.mem_right _ _ ((ResetUnion.baseline_ambiguous v formula).mpr hz)]
  exact Or.inl hw

private theorem right_marker (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (hz : (v 1).Ambiguous) (w : Role) (hw : w ∉ ((ResetUnion.baseline formula).eval v).val) :
    w ∈ (realize a (ResetUnion.right formula) v).val ↔ w ∈ (v 2).val ∧
      ∃ i ∈ ResetUnion.support formula,
        (WinnerSet.choice a (v (ResetUnion.literalName (i, true))) (v 0)).Ambiguous ∧
          (WinnerSet.choice a (v (ResetUnion.literalName (i, false))) (v 0)).Ambiguous := by
  have hbranch (i : ℕ) (hi : i ∈ ResetUnion.support formula) :
      w ∈ (realize a (ResetUnion.branch i) v).val ↔ w ∈ (v 2).val ∧
        (WinnerSet.choice a (v (ResetUnion.literalName (i, true))) (v 0)).Ambiguous ∧
          (WinnerSet.choice a (v (ResetUnion.literalName (i, false))) (v 0)).Ambiguous := by
    rw [ResetUnion.branch, realize_reset, realize_reset, realize_union, realize_union]
    simp only [ResetUnion.literalTerm, realize_var]
    exact WinnerSetFold.mem_branch_outside _ _ _ w
      (fun h => hw (guard_subset_baseline a formula v hz i hi true h))
      (fun h => hw (guard_subset_baseline a formula v hz i hi false h))
  rw [ResetUnion.right, realize_rightComb, realize_baseline,
    WinnerSetFold.mem_right _ _ ((ResetUnion.baseline_ambiguous v formula).mpr hz)]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, h⟩)
    · exact False.elim (hw h)
    · obtain ⟨hc, hp, hn⟩ := (hbranch i hi).mp h
      exact ⟨hc, i, hi, hp, hn⟩
  · rintro ⟨hc, i, hi, hp, hn⟩
    exact Or.inr ⟨_, ⟨_, ⟨i, hi, rfl⟩, rfl⟩, (hbranch i hi).mpr ⟨hc, hp, hn⟩⟩

private theorem left_marker (a : Role) (formula : CNF) (v : ℕ → WinnerSet Role)
    (hz : (v 1).Ambiguous) (w : Role) (hw : w ∉ ((ResetUnion.baseline formula).eval v).val) :
    w ∈ (realize a (ResetUnion.left formula) v).val ↔ w ∈ (v 2).val ∧
      ∀ C ∈ formula, (realize a (ResetUnion.clauseGuard C) v).Ambiguous := by
  rw [ResetUnion.left, realize_leftComb]
  have hsubset : ∀ X ∈ ((formula.map ResetUnion.clauseGuard).map (fun t => realize a t v)),
      X.val ⊆ ((ResetUnion.baseline formula).eval v).val := by
    intro X hX
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hX
    obtain ⟨C, hc, rfl⟩ := List.mem_map.mp ht
    exact clauseGuard_subset_baseline a formula v hz C hc
  simpa only [realize_var, List.forall_mem_map] using
    WinnerSetFold.mem_left_outside _ _ ((ResetUnion.baseline formula).eval v).val w hw hsubset

/-- The UNSAT direction on every winner-set valuation; no atomicity of the
calibration value is presumed or inferred. -/
theorem core_valid_of_unsatisfiable (a : Role) (formula : CNF)
    (hnonempty : ∀ C ∈ formula, C ≠ []) (hu : ¬Satisfiable formula) (v : ℕ → WinnerSet Role) :
    (translate (ResetUnion.equation formula).1).eval WinnerSet.reset (WinnerSet.choice a) v =
      (translate (ResetUnion.equation formula).2).eval WinnerSet.reset (WinnerSet.choice a) v := by
  classical
  change (realize a (ResetUnion.left formula) v).reset (realize a (ResetUnion.right formula) v) =
    realize a (ResetUnion.right formula) v
  by_cases hz : (v 1).Ambiguous
  · apply Subtype.ext
    ext w
    rw [WinnerSet.mem_reset]
    simp only [(right_ambiguous a formula v).mpr hz, true_and]
    constructor
    · rintro (h | hA)
      · exact h
      · by_cases hw : w ∈ ((ResetUnion.baseline formula).eval v).val
        · exact baseline_subset_right a formula v hz hw
        · obtain ⟨hC, hguards⟩ := (left_marker a formula v hz w hw).mp hA
          have hpred : ∀ C ∈ formula, ∃ literal ∈ C,
              if literal.2 then (WinnerSet.choice a (v (ResetUnion.literalName (literal.1, true))) (v 0)).Ambiguous
              else (WinnerSet.choice a (v (ResetUnion.literalName (literal.1, false))) (v 0)).Ambiguous := by
            intro C hc
            have hguard := hguards C hc
            rw [realize_clauseGuard] at hguard
            obtain ⟨X, hX, hm⟩ := RawPair.choiceFold_ambiguous_witness a _ _
              (by
                intro hnil
                apply hnonempty C hc
                have hlen := congrArg List.length hnil
                simp only [List.length_map, List.length_nil] at hlen
                exact List.length_eq_zero_iff.mp hlen) hguard
            obtain ⟨literal, hl, rfl⟩ := List.mem_map.mp hX
            refine ⟨literal, hl, ?_⟩
            obtain ⟨i, sign⟩ := literal
            cases sign <;> simpa only [Bool.false_eq_true, ite_false, ite_true] using hm
          obtain ⟨i, hi, hp, hn⟩ := RawPair.conflicting_predicates_of_unsatisfiable formula
            (fun i => (WinnerSet.choice a (v (ResetUnion.literalName (i, true))) (v 0)).Ambiguous)
            (fun i => (WinnerSet.choice a (v (ResetUnion.literalName (i, false))) (v 0)).Ambiguous) hu hpred
          exact (right_marker a formula v hz w hw).mpr ⟨hC, i, hi, hp, hn⟩
    · exact Or.inl
  · unfold WinnerSet.Ambiguous at hz
    push Not at hz
    obtain ⟨r, hr⟩ := hz
    have hbase : realize a (ResetUnion.baseline formula) v = WinnerSet.singleton r := by
      rw [realize_baseline, ResetUnion.baseline, KFOL.ResetUnion.Term.eval_rightComb,
        KFOL.ResetUnion.Term.eval_var, hr]
      exact WinnerSetFold.right_singleton _ r
    have hR : realize a (ResetUnion.right formula) v = WinnerSet.singleton r := by
      rw [ResetUnion.right, realize_rightComb, hbase]
      exact WinnerSetFold.right_singleton _ r
    rw [hR, WinnerSet.reset_singleton]

end KFOL.Reductions.ResetChoice

namespace KFOL.Reductions.ResetChoice

universe u

variable {Role : Type u}

private theorem sat_literal_ne_owner (a b d : Role) (hab : a ≠ b) (had : a ≠ d)
    (assignment : ℕ → Bool) (literal : Literal) :
    ResetUnion.satisfyingValuation b d a assignment (ResetUnion.literalName literal) ≠ WinnerSet.singleton a := by
  rw [ResetUnion.satisfyingValuation_literal]
  split_ifs with h
  · simpa only [ne_eq, WinnerSet.singleton_inj] using had.symm
  · simpa only [ne_eq, WinnerSet.singleton_inj] using hab.symm

private theorem sat_T_ne_owner (a b d : Role) (hab : a ≠ b) (assignment : ℕ → Bool) :
    ResetUnion.satisfyingValuation b d a assignment 0 ≠ WinnerSet.singleton a := by
  rw [ResetUnion.satisfyingValuation_zero]
  simpa only [ne_eq, WinnerSet.singleton_inj] using hab.symm

private theorem realize_clauseGuard_sat (a b d : Role) (hab : a ≠ b) (had : a ≠ d)
    (assignment : ℕ → Bool) (C : Clause) :
    let v := ResetUnion.satisfyingValuation b d a assignment
    realize a (ResetUnion.clauseGuard C) v = (ResetUnion.clauseGuard C).eval v := by
  dsimp only
  rw [realize_clauseGuard, RawPair.choiceFold_union a _ _ (sat_T_ne_owner a b d hab assignment)
    (by intro X hX; obtain ⟨literal, _, rfl⟩ := List.mem_map.mp hX
        exact sat_literal_ne_owner a b d hab had assignment literal)]
  apply Subtype.ext
  ext w
  rw [RawPair.mem_unions, ResetUnion.eval_clauseGuard_mem]
  simp only [List.mem_map]
  constructor
  · rintro (h | ⟨X, ⟨literal, hl, rfl⟩, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨literal, hl, h⟩
  · rintro (h | ⟨literal, hl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨literal, hl, rfl⟩, h⟩

private theorem realize_branch_sat (a b d : Role) (hab : a ≠ b) (had : a ≠ d)
    (assignment : ℕ → Bool) (i : ℕ) :
    let v := ResetUnion.satisfyingValuation b d a assignment
    realize a (ResetUnion.branch i) v = (ResetUnion.branch i).eval v := by
  dsimp only
  have hguard (literal : Literal) :
      WinnerSet.choice a (ResetUnion.satisfyingValuation b d a assignment (ResetUnion.literalName literal))
        (ResetUnion.satisfyingValuation b d a assignment 0) =
      (ResetUnion.satisfyingValuation b d a assignment (ResetUnion.literalName literal)).union
        (ResetUnion.satisfyingValuation b d a assignment 0) := by
    simp only [WinnerSet.choice, sat_literal_ne_owner a b d hab had assignment literal,
      sat_T_ne_owner a b d hab assignment, or_self, ite_false]
  simp only [ResetUnion.branch, realize_reset, realize_union, ResetUnion.literalTerm,
    realize_var, KFOL.ResetUnion.Term.eval_reset, KFOL.ResetUnion.Term.eval_union,
    KFOL.ResetUnion.Term.eval_var, hguard]

private theorem realize_right_sat (a b d : Role) (hab : a ≠ b) (had : a ≠ d)
    (assignment : ℕ → Bool) (formula : CNF) :
    let v := ResetUnion.satisfyingValuation b d a assignment
    realize a (ResetUnion.right formula) v = (ResetUnion.right formula).eval v := by
  dsimp only
  rw [ResetUnion.right, realize_rightComb, KFOL.ResetUnion.Term.eval_rightComb, realize_baseline]
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  exact realize_branch_sat a b d hab had assignment i

private theorem realize_left_sat (a b d : Role) (hab : a ≠ b) (had : a ≠ d)
    (assignment : ℕ → Bool) (formula : CNF) :
    let v := ResetUnion.satisfyingValuation b d a assignment
    realize a (ResetUnion.left formula) v = (ResetUnion.left formula).eval v := by
  dsimp only
  rw [ResetUnion.left, realize_leftComb, KFOL.ResetUnion.Term.eval_leftComb]
  congr 1
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro C _
  exact realize_clauseGuard_sat a b d hab had assignment C

/-- Actual SAT countervaluation of the translated native trees. Every
replaced union is proved equal to its owned guard at this valuation. -/
theorem core_failure_of_satisfying_assignment (a b d : Role)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (formula : CNF) (assignment : ℕ → Bool)
    (hsat : ∀ C ∈ formula, ∃ literal ∈ C, assignment literal.1 = literal.2) :
    let v := ResetUnion.satisfyingValuation b d a assignment
    (translate (ResetUnion.equation formula).1).eval WinnerSet.reset (WinnerSet.choice a) v ≠
      (translate (ResetUnion.equation formula).2).eval WinnerSet.reset (WinnerSet.choice a) v := by
  dsimp only
  intro he
  change (realize a (ResetUnion.left formula) _).reset (realize a (ResetUnion.right formula) _) =
    realize a (ResetUnion.right formula) _ at he
  rw [realize_left_sat a b d hab had assignment formula, realize_right_sat a b d hab had assignment formula] at he
  apply ResetUnion.failure_of_satisfying_assignment b d a hbd hab.symm had.symm formula assignment hsat
  exact he

/-- Complete native reset/choice reduction, including empty source clauses,
with the intended two operations and all valuation quantifiers expanded. -/
theorem equation_valid_iff_unsatisfiable (a b d : Role)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (formula : CNF) :
    (∀ v : ℕ → WinnerSet Role,
      (equation formula).1.eval WinnerSet.reset (WinnerSet.choice a) v =
        (equation formula).2.eval WinnerSet.reset (WinnerSet.choice a) v) ↔ ¬Satisfiable formula := by
  classical
  by_cases he : formula.any List.isEmpty = true
  · have hu := RawPair.unsatisfiable_of_empty_clause formula he
    simp only [equation, he, ite_true]
    exact ⟨fun _ => hu, fun _ _ => trivial⟩
  · have hnonempty := RawPair.clauses_nonempty_of_no_empty formula he
    simp only [equation, he]
    constructor
    · intro hv ⟨assignment, hs⟩
      exact core_failure_of_satisfying_assignment a b d hab had hbd formula assignment hs (hv _)
    · intro hu
      exact core_valid_of_unsatisfiable a formula hnonempty hu

end KFOL.Reductions.ResetChoice

namespace KFOL.Reductions.ResetChoice

universe v

/-- The replacement changes only operation labels: every original tree node
and every copied input occurrence is counted exactly once. -/
theorem size_translate {Var : Type v} (t : KFOL.ResetUnion.Term Var) :
    (translate t).size = t.size := by
  induction t with
  | var => rfl
  | @func n symbol args ih =>
    cases symbol <;>
      change 1 + (translate (args 0)).size + (translate (args 1)).size =
        1 + KFOL.ResetUnion.Term.size (args 0) + KFOL.ResetUnion.Term.size (args 1) <;>
      rw [ih 0, ih 1]

/-- Exact source-tree accounting gives an unconditional linear native output
bound, including the fixed valid output on source empty clauses. -/
theorem equation_size_le (formula : CNF) :
    (equation formula).1.size + (equation formula).2.size ≤
      28 * (ResetUnion.support formula).length + 2 * formula.length + 2 * formula.flatten.length + 8 := by
  classical
  by_cases he : formula.any List.isEmpty = true
  · simp only [equation, he, ite_true, KFOL.RawPair.Term.size_var]
    omega
  · rw [equation, ite_eq_right he]
    simp only [size_translate]
    rw [ResetUnion.size_equation]

end KFOL.Reductions.ResetChoice
