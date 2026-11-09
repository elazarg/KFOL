module

public import KFOL.Reductions.GuardedPair

@[expose] public section

namespace KFOLTest.ReductionsGuardedPair

open KFOL
open KFOL.Reductions.GuardedPair

example : (equation []).1.size + (equation []).2.size = 11 := by decide
example : (equation [[]]).1.size + (equation [[]]).2.size = 17 := by decide
example : (equation [[(1000000000, true)]]).1.size +
    (equation [[(1000000000, true)]]).2.size = 35 := by decide

example (v : ℕ → WinnerSet (Fin 3)) :
    (equation [[]]).1.eval 0 1 v = (equation [[]]).2.eval 0 1 v := by
  apply valid_of_unsatisfiable 0 1 (by decide)
  rintro ⟨assignment, hall⟩
  obtain ⟨literal, hl, _⟩ := hall [] (by simp)
  simp at hl

example : let v := satisfyingValuation (0 : Fin 3) 1 2 (fun _ => true)
    2 ∈ ((equation [[(1000000000, true)]]).1.eval 0 1 v).val ∧
      2 ∉ ((equation [[(1000000000, true)]]).2.eval 0 1 v).val := by
  apply satisfying_assignment_separates 0 1 2 (by decide) (by decide) (by decide)
  intro C hc
  have hC : C = [(1000000000, true)] := List.mem_singleton.mp hc
  subst C
  exact ⟨(1000000000, true), by simp, rfl⟩

/-- info: 'KFOL.Reductions.GuardedPair.equation_valid_iff_unsatisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.GuardedPair.equation_valid_iff_unsatisfiable

/-- info: 'KFOL.Reductions.GuardedPair.third_role_observation_valid_iff_unsatisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.GuardedPair.third_role_observation_valid_iff_unsatisfiable

/-- info: 'KFOL.Reductions.GuardedPair.equation_size' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.GuardedPair.equation_size

end KFOLTest.ReductionsGuardedPair

/-- info: 'KFOL.Reductions.GuardedPair.third_role_observation_implication_valid_iff_unsatisfiable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reductions.GuardedPair.third_role_observation_implication_valid_iff_unsatisfiable
