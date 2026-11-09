module
public import KFOL.Complexity.GuardedPairMachines
public import KFOL.Complexity.CNFHardness
@[expose] public section
namespace KFOL.Complexity.GuardedPairHardness
universe u
open Turing.MultiTapeTM
open KFOL.Complexity.GuardedPairMachines

theorem coNPHard {Role : Type u} (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard equationEncoding
      {equation : Tree × Tree | ∀ valuation : ℕ → WinnerSet Role,
        equation.1.eval a b valuation = equation.2.eval a b valuation} := by
  apply CNFHardness.coNPHard_of_CNF
    (fun equation : Tree × Tree => ∀ valuation : ℕ → WinnerSet Role,
      equation.1.eval a b valuation = equation.2.eval a b valuation)
    KFOL.Reductions.GuardedPair.equation ?_
    (fun formula => KFOL.Reductions.GuardedPair.equation_valid_iff_unsatisfiable a b d hab had hbd formula)
    ((.var 0, .var 0) : Tree × Tree) (fun _ => rfl)
  rw [show Cslib.Complexity.encCNF = cnfEncoding from rfl]
  exact reduction_polyTime

theorem observation_coNPHard {Role : Type u} (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard equationEncoding
      {equation : Tree × Tree | ∀ valuation : ℕ → WinnerSet Role,
        d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} := by
  apply CNFHardness.coNPHard_of_CNF
    (fun equation : Tree × Tree => ∀ valuation : ℕ → WinnerSet Role,
      d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val)
    KFOL.Reductions.GuardedPair.equation ?_
    (fun formula => KFOL.Reductions.GuardedPair.third_role_observation_valid_iff_unsatisfiable a b d hab had hbd formula)
    ((.var 0, .var 0) : Tree × Tree) (fun _ => Iff.rfl)
  rw [show Cslib.Complexity.encCNF = cnfEncoding from rfl]
  exact reduction_polyTime

theorem language_coNPHard {Role : Type u} (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard encBits
      {word | ∃ equation : Tree × Tree,
        KFOL.FiniteTermCode.encodeEquation KFOL.GuardedPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role, equation.1.eval a b valuation = equation.2.eval a b valuation} := by
  apply Cslib.Complexity.coNPHard.trans (coNPHard a b d hab had hbd)
  refine ⟨KFOL.FiniteTermCode.encodeEquation KFOL.GuardedPair.Symbol,
    ComputableInPolyTime.of_eq (fun _ => rfl), ?_⟩
  intro equation
  constructor
  · intro h
    exact ⟨equation, rfl, h⟩
  · rintro ⟨other, he, ho⟩
    have heq := KFOL.FiniteTermCode.encodeEquation_injective he
    exact heq ▸ ho
theorem observation_language_coNPHard {Role : Type u}
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard encBits
      {word | ∃ equation : Tree × Tree,
        KFOL.FiniteTermCode.encodeEquation KFOL.GuardedPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} :=
  CNFHardness.coNPHard_encode equationEncoding _ (observation_coNPHard a b d hab had hbd)
end KFOL.Complexity.GuardedPairHardness
