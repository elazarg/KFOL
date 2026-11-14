module

public import KFOL.Complexity.AtomicWinMachines
public import Complexity.Computability.Complexity.CookLevin.Completeness
public import Complexity.Computability.Complexity.Reduction

/-! # Machine-level SAT hardness of atomic possible-win existence -/

@[expose] public section

namespace KFOL.Complexity.AtomicWinHardness

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Reductions

theorem npHard {K : ℕ} (a b : Fin K) (different : a ≠ b) :
    Cslib.Complexity.NPHard (AtomicWinMachines.termEncoding K)
      {term | term.AtomicPossibleWin a} := by
  obtain ⟨test, correct⟩ := AtomicWin.exists_test a b
  apply Cslib.Complexity.NPHard.trans Cslib.Complexity.CookLevin.SAT_npComplete.2
  refine ⟨AtomicWin.formula a b test, AtomicWinMachines.formula_polyTime a b test, ?_⟩
  intro input
  change input ∈ Cslib.Complexity.SAT ↔
    (AtomicWin.formula a b test input).AtomicPossibleWin a
  rw [AtomicWin.formula_possible_iff a b different test correct]
  simp only [Cslib.Complexity.SAT, Set.mem_ofPred_eq,
    Cslib.Logic.PL.CNF.Satisfiable, Satisfiable,
    Cslib.Logic.PL.CNF.eval_eq_true_iff, Cslib.Logic.PL.Clause.eval_eq_true_iff]

theorem encoded_npHard {K : ℕ} (a b : Fin K) (different : a ≠ b) :
    Cslib.Complexity.NPHard encBits
      {word | ∃ term : Term (Fin K) ℕ,
        AtomicWinMachines.termEncoding K term = word ∧ term.AtomicPossibleWin a} := by
  apply Cslib.Complexity.NPHard.trans (npHard a b different)
  refine ⟨AtomicWinMachines.termEncoding K, ComputableInPolyTime.of_eq (fun _ => rfl), ?_⟩
  intro term
  constructor
  · exact fun wins => ⟨term, rfl, wins⟩
  · rintro ⟨other, equal, wins⟩
    exact (AtomicWinMachines.termEncoding K).injective equal ▸ wins

end KFOL.Complexity.AtomicWinHardness
