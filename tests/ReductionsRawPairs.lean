module

public import KFOL.Reductions.RawPairs

@[expose] public section

namespace KFOLTest.ReductionsRawPairs

open KFOL
open KFOL.Reductions

example : (RawPair.equation []).1.size + (RawPair.equation []).2.size = 24 := by decide
example : (RawPair.twoOwnerEquation []).1.size + (RawPair.twoOwnerEquation []).2.size = 2 := by decide
example : (RawPair.equation [[]]).1.size + (RawPair.equation [[]]).2.size = 2 := by decide
example : (RawPair.equation [[(1000000000, true)]]).1.size +
    (RawPair.equation [[(1000000000, true)]]).2.size = 46 := by decide

example : (ResetChoice.equation []).1.size + (ResetChoice.equation []).2.size = 36 := by decide
example : (ResetChoice.equation [[]]).1.size + (ResetChoice.equation [[]]).2.size = 2 := by decide
example : (ResetChoice.equation [[(1000000000, true)]]).1.size +
    (ResetChoice.equation [[(1000000000, true)]]).2.size = 68 := by decide

private theorem no_empty_clause_sat : ¬Satisfiable [[]] := by
  rintro ⟨assignment, hall⟩
  obtain ⟨literal, hl, _⟩ := hall [] (by simp)
  exact List.not_mem_nil hl

example (v : ℕ → WinnerSet (Fin 3)) :
    (RawPair.equation [[]]).1.eval (WinnerSet.choice 0) WinnerSet.union v =
      (RawPair.equation [[]]).2.eval (WinnerSet.choice 0) WinnerSet.union v :=
  (RawPair.union_equation_valid_iff_unsatisfiable 0 1 2 (by decide) (by decide) (by decide) _).mpr no_empty_clause_sat v

example (v : ℕ → WinnerSet (Fin 3)) :
    (RawPair.twoOwnerEquation [[]]).1.eval (WinnerSet.choice 0) (WinnerSet.choice 1) v =
      (RawPair.twoOwnerEquation [[]]).2.eval (WinnerSet.choice 0) (WinnerSet.choice 1) v :=
  (RawPair.twoOwners_equation_valid_iff_unsatisfiable 0 1 2 (by decide) (by decide) (by decide) _).mpr no_empty_clause_sat v

example (v : ℕ → WinnerSet (Fin 3)) :
    (ResetChoice.equation [[]]).1.eval WinnerSet.reset (WinnerSet.choice 0) v =
      (ResetChoice.equation [[]]).2.eval WinnerSet.reset (WinnerSet.choice 0) v :=
  (ResetChoice.equation_valid_iff_unsatisfiable 0 1 2 (by decide) (by decide) (by decide) _).mpr no_empty_clause_sat v

/-- info: 'KFOL.Reductions.RawPair.union_equation_valid_iff_unsatisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.RawPair.union_equation_valid_iff_unsatisfiable

/-- info: 'KFOL.Reductions.RawPair.twoOwners_equation_valid_iff_unsatisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.RawPair.twoOwners_equation_valid_iff_unsatisfiable

/-- info: 'KFOL.Reductions.ResetChoice.equation_valid_iff_unsatisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.ResetChoice.equation_valid_iff_unsatisfiable

/-- info: 'KFOL.Reductions.RawPair.equation_size_le' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.RawPair.equation_size_le
/-- info: 'KFOL.Reductions.RawPair.twoOwnerEquation_size_le' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.RawPair.twoOwnerEquation_size_le
/-- info: 'KFOL.Reductions.ResetChoice.equation_size_le' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.ResetChoice.equation_size_le

end KFOLTest.ReductionsRawPairs
