module

public import KFOL.Policies.HardPatterns
public import KFOL.Definitions.Reductions
public import KFOL.Reductions.ValueFolds

/-! Native policy reduction marker and calibration arguments. -/

@[expose] public section

namespace KFOL.Policies

universe u v

variable {Role : Type u} {Label : Type v}

/-- Positive preliminary tests rule out every shared blocker other than the
observer. This is the exact Boolean consistency condition needed by CNF. -/
theorem policyPasses_disjunction (U B₀ B₁ : Set Role) (w : Role) (Y : WinnerSet Role)
    (hU : WinnerSet.PolicyPasses U w Y)
    (hcover : ∀ r, r ∈ B₀ → r ∈ B₁ → r ∉ U → r = w) :
    WinnerSet.PolicyPasses B₀ w Y ∨ WinnerSet.PolicyPasses B₁ w Y := by
  apply (WinnerSet.policyPasses_inter B₀ B₁ w Y).mp
  intro r hr hrw hYr
  by_cases hrU : r ∈ U
  · exact hU r hrU hrw hYr
  · exact hrw (hcover r hr.1 hr.2 hrU)

/-- Calibration identifies the actual singleton, rather than merely supplying
an externally assumed marker restriction. -/
theorem calibration_eq_singleton (D : Label → Set Role)
    (hinj : Function.Injective (passingPattern D)) (r w : Role) (Y : WinnerSet Role)
    (hw : w ∉ Y.val) (hm : ¬Y.Ambiguous)
    (hpass : ∀ d, WinnerSet.PolicyPasses (D d) w Y ↔ r ∉ D d) :
    Y = WinnerSet.singleton r := by
  classical
  unfold WinnerSet.Ambiguous at hm
  push Not at hm
  obtain ⟨t, rfl⟩ := hm
  have htw : t ≠ w := by
    intro ht
    apply hw
    simp [ht]
  have htr : t = r := by
    apply hinj
    ext d
    have h := hpass d
    simp only [WinnerSet.policyPasses_singleton] at h
    simpa only [passingPattern, Set.mem_ofPred_eq, htw, or_false] using h
  rw [htr]

namespace Hardness

open KFOL.Reductions

/- Value of a literal-gate clause; the native tree compiler below follows this
recursion exactly, preserving separate continuation copies. -/

/-- Every gate in a branch contributes only its passing test outside the
baseline. Root and tested input contributions are absorbed by that baseline. -/
theorem mem_clauseValue_outside (B₀ B₁ : Set Role) (Z W C : WinnerSet Role)
    (Y : ℕ → WinnerSet Role) (clause : Clause) (w : Role)
    (hz : Z.Ambiguous) (hZW : Z.val ⊆ W.val)
    (hY : ∀ literal ∈ clause, (Y literal.1).val ⊆ W.val) (hw : w ∉ W.val) :
    w ∈ (clauseValue B₀ B₁ Z Y C clause).val ↔ w ∈ C.val ∧
      ∀ literal ∈ clause, WinnerSet.PolicyPasses (if literal.2 then B₀ else B₁) w (Y literal.1) := by
  induction clause with
  | nil => simp [clauseValue]
  | cons literal rest ih =>
    rw [clauseValue, WinnerSet.policyReset_marker _ Z _ _ W w hz hZW
      (hY literal (List.mem_cons_self ..)) hw,
      ih (fun l hl => hY l (List.mem_cons_of_mem _ hl))]
    simp only [List.forall_mem_cons]
    tauto

theorem literal_mem_support (formula : CNF) (clause : Clause) (hc : clause ∈ formula)
    (literal : Literal) (hl : literal ∈ clause) :
    literal.1 ∈ KFOL.Reductions.ResetUnion.support formula := by
  simp only [KFOL.Reductions.ResetUnion.support, List.mem_dedup, List.mem_cons, List.mem_map]
  exact Or.inr ⟨literal, List.mem_flatten.mpr ⟨clause, hc, hl⟩, rfl⟩

/-- An unsatisfiable formula has a clause in which every literal gate passes,
whenever each Boolean input passes at least one of the two gates. -/
theorem exists_passing_clause (B₀ B₁ : Set Role) (formula : CNF)
    (Y : ℕ → WinnerSet Role) (w : Role)
    (hpasses : ∀ i ∈ KFOL.Reductions.ResetUnion.support formula, WinnerSet.PolicyPasses B₀ w (Y i) ∨ WinnerSet.PolicyPasses B₁ w (Y i))
    (hunsat : ¬Satisfiable formula) :
    ∃ clause ∈ formula, ∀ literal ∈ clause,
      WinnerSet.PolicyPasses (if literal.2 then B₀ else B₁) w (Y literal.1) := by
  classical
  let assignment : ℕ → Bool := fun i => decide (¬WinnerSet.PolicyPasses B₀ w (Y i))
  have hfail : ¬∀ clause ∈ formula, ∃ literal ∈ clause, assignment literal.1 = literal.2 :=
    fun h => hunsat ⟨assignment, h⟩
  push Not at hfail
  obtain ⟨clause, hc, hall⟩ := hfail
  refine ⟨clause, hc, ?_⟩
  intro literal hl
  have h := hall literal hl
  cases hb : literal.2
  · have hn : ¬WinnerSet.PolicyPasses B₀ w (Y literal.1) := by
      simpa [assignment, hb] using h
    simpa [hb] using (hpasses literal.1 (literal_mem_support formula clause hc literal hl)).resolve_left hn
  · simpa [assignment, hb] using h

end Hardness
end KFOL.Policies
