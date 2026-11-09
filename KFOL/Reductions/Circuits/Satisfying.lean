module

public import KFOL.Reductions.Circuits.Values

/-! Actual three-generator countervaluations for the native reset DAG. -/

@[expose] public section

namespace KFOL.Circuit.ResetCNF

open KFOL.Reductions

universe u

variable {Role : Type u}

noncomputable local instance : (Equational.language Reset.Symbol).Structure (WinnerSet Role) :=
  Reset.structureOf WinnerSet.reset

/- Only the three generator stages occur; all variable labels stay sparse. -/
@[simp] theorem satisfyingStage_literal (assignment : ℕ → Bool) (literal : Literal) :
    satisfyingStage assignment (ResetUnion.literalName literal) =
      if assignment literal.1 = literal.2 then 1 else 0 :=
  ResetUnion.literalName_injective.extend_apply _ _ literal

private theorem satisfyingStage_small (assignment : ℕ → Bool) (j : ℕ) (hj : j < 3) :
    satisfyingStage assignment j = if j = 0 then 1 else 2 := by
  apply Function.extend_apply'
  rintro ⟨literal, he⟩
  have h := ResetUnion.literalName_ge_three literal
  omega

@[simp] theorem satisfyingStage_zero (assignment : ℕ → Bool) : satisfyingStage assignment 0 = 1 :=
  satisfyingStage_small assignment 0 (by decide)

@[simp] theorem satisfyingStage_one (assignment : ℕ → Bool) : satisfyingStage assignment 1 = 2 :=
  satisfyingStage_small assignment 1 (by decide)

@[simp] theorem satisfyingValuation_zero (three : Fin 3 ↪ Role) (assignment : ℕ → Bool) :
    satisfyingValuation three assignment 0 = Reset.chainValue three 1 := by
  simp only [satisfyingValuation, satisfyingStage_zero]

@[simp] theorem satisfyingValuation_one (three : Fin 3 ↪ Role) (assignment : ℕ → Bool) :
    satisfyingValuation three assignment 1 = Reset.chainValue three 2 := by
  simp only [satisfyingValuation, satisfyingStage_one]

theorem satisfyingValuation_literal_ambiguous (three : Fin 3 ↪ Role) (assignment : ℕ → Bool) (literal : Literal) :
    (satisfyingValuation three assignment (ResetUnion.literalName literal)).Ambiguous ↔
      assignment literal.1 = literal.2 := by
  simp only [satisfyingValuation, satisfyingStage_literal, Reset.ambiguous_chainValue]
  split_ifs <;> simp_all

theorem satisfyingValuation_literal_no_marker (three : Fin 3 ↪ Role) (assignment : ℕ → Bool) (literal : Literal) :
    three 2 ∉ (satisfyingValuation three assignment (ResetUnion.literalName literal)).val := by
  simp only [satisfyingValuation, satisfyingStage_literal, Reset.marker_chainValue]
  split_ifs <;> decide

/- The explicit SAT witness uses only Z,U,T at EVERY input, including unused
input labels; no arbitrary finite certificate is supplied. -/
theorem satisfying_assignment_separates (three : Fin 3 ↪ Role) (formula : CNF)
    (assignment : ℕ → Bool)
    (hsat : ∀ clause ∈ formula, ∃ literal ∈ clause, assignment literal.1 = literal.2) :
    Reset.chainValue three 2 ∈ Set.range (satisfyingValuation three assignment) ∧
      (∀ j, ∃ stage : Fin 3, satisfyingValuation three assignment j = Reset.chainValue three stage) ∧
      (equation formula).eval (satisfyingValuation three assignment) ≠
        some (rightValue (satisfyingValuation three assignment) formula,
          rightValue (satisfyingValuation three assignment) formula) := by
  let valuation := satisfyingValuation three assignment
  have hz : (valuation 0).Ambiguous := by
    rw [show valuation 0 = Reset.chainValue three 1 from satisfyingValuation_zero three assignment,
      Reset.ambiguous_chainValue]
    decide
  have hW : three 2 ∉ (baselineValue valuation formula).val := by
    rw [mem_baselineValue valuation formula hz]
    rintro (hroot | ⟨i, _, hp | hn⟩)
    · rw [show valuation 0 = Reset.chainValue three 1 from satisfyingValuation_zero three assignment,
        Reset.marker_chainValue] at hroot
      exact (by decide : ¬(1 : Fin 3) = 2) hroot
    · exact satisfyingValuation_literal_no_marker three assignment (i, true) hp
    · exact satisfyingValuation_literal_no_marker three assignment (i, false) hn
  have hleft : three 2 ∈ (leftValue valuation formula).val := by
    apply (leftValue_marker valuation formula hz _ hW).mpr
    refine ⟨?_, fun clause hc => ?_⟩
    · rw [show valuation 1 = Reset.chainValue three 2 from satisfyingValuation_one three assignment,
        Reset.marker_chainValue]
    · obtain ⟨literal, hl, hs⟩ := hsat clause hc
      exact ⟨literal, hl, (satisfyingValuation_literal_ambiguous three assignment literal).mpr hs⟩
  have hright : three 2 ∉ (rightValue valuation formula).val := by
    intro hm
    obtain ⟨_, i, _, hp, hn⟩ := (rightValue_marker valuation formula hz _ hW).mp hm
    have ht := (satisfyingValuation_literal_ambiguous three assignment (i, true)).mp hp
    have hf := (satisfyingValuation_literal_ambiguous three assignment (i, false)).mp hn
    exact Bool.false_ne_true (hf.symm.trans ht)
  refine ⟨⟨1, satisfyingValuation_one three assignment⟩, fun j => ⟨satisfyingStage assignment j, rfl⟩, ?_⟩
  rw [eval_equation]
  intro he
  have hpair := congrArg Prod.fst (Option.some.inj he)
  change (leftValue valuation formula).reset (rightValue valuation formula) = rightValue valuation formula at hpair
  have hmarker : three 2 ∈ ((leftValue valuation formula).reset (rightValue valuation formula)).val :=
    (WinnerSet.mem_reset _ _ _).mpr (Or.inr ⟨(rightValue_ambiguous valuation formula).mpr hz, hleft⟩)
  exact hright (hpair ▸ hmarker)

theorem equation_holds_iff_unsatisfiable (three : Fin 3 ↪ Role) (formula : CNF) :
    (equation formula).Holds (WinnerSet Role) ↔ ¬Satisfiable formula := by
  constructor
  · intro hh ⟨assignment, hsat⟩
    obtain ⟨_, _, hne⟩ := satisfying_assignment_separates three formula assignment hsat
    obtain ⟨value, he⟩ := hh.2 (satisfyingValuation three assignment)
    have heval := eval_equation (satisfyingValuation three assignment) formula
    have hright := congrArg Prod.snd (Option.some.inj (heval.symm.trans he))
    change rightValue (satisfyingValuation three assignment) formula = value at hright
    apply hne
    simpa only [← hright] using he
  · exact equation_holds_of_unsatisfiable formula

/- Validity restricted to the displayed complete three-value generator,
without unfolding the graph or introducing constants in its syntax. -/
theorem equation_chain_valid_iff_unsatisfiable (three : Fin 3 ↪ Role) (formula : CNF) :
    ((equation formula).WellFormed ∧
      ∀ valuation : ℕ → WinnerSet Role,
        (∀ j, ∃ stage : Fin 3, valuation j = Reset.chainValue three stage) →
        ∃ value, (equation formula).eval valuation = some (value, value)) ↔ ¬Satisfiable formula := by
  constructor
  · rintro ⟨_, hv⟩ ⟨assignment, hsat⟩
    obtain ⟨_, hchain, hne⟩ := satisfying_assignment_separates three formula assignment hsat
    obtain ⟨value, he⟩ := hv (satisfyingValuation three assignment) hchain
    have hright := congrArg Prod.snd (Option.some.inj ((eval_equation _ formula).symm.trans he))
    change rightValue (satisfyingValuation three assignment) formula = value at hright
    apply hne
    simpa only [← hright] using he
  · intro hu
    have hh := equation_holds_of_unsatisfiable (Role := Role) formula hu
    exact ⟨hh.1, fun valuation _ => hh.2 valuation⟩

end KFOL.Circuit.ResetCNF
