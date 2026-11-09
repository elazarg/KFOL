module

public import KFOL.Policies.Reductions
public import Mathlib.Tactic.Linarith

/-! Affine native-tree output size for the fixed width-three policy reduction.
Policy macro continuations are counted with their actual multiplicities. -/

@[expose] public section

namespace KFOL.Policies.Hardness.Plan

universe u v w x

open KFOL.Reductions

variable {Role : Type u} {Label : Type v}

private theorem clauseBound_le_succ (plan : Plan Role Label) (n : ℕ) :
    plan.clauseBound n ≤ plan.clauseBound (n + 1) := by
  induction n with
  | zero =>
    have hp := plan.zero.continuationCopies_pos
    simp only [clauseBound, Nat.mul_one]
    omega
  | succ n ih =>
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ ih) _

theorem clauseBound_monotone (plan : Plan Role Label) : Monotone plan.clauseBound :=
  monotone_nat_of_le_succ (clauseBound_le_succ plan)

theorem clause_size_le (plan : Plan Role Label) (clause : Clause) :
    (plan.clause clause).size ≤ plan.clauseBound clause.length := by
  induction clause with
  | nil => exact Nat.le_refl 1
  | cons literal rest ih =>
    rw [clause, PolicyExpr.size_gate]
    simp only [List.length_cons, clauseBound]
    cases literal.2 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact Nat.add_le_add
        (Nat.mul_le_mul (Nat.le_max_right _ _) ih) (Nat.le_max_right _ _)
    · exact Nat.add_le_add
        (Nat.mul_le_mul (Nat.le_max_left _ _) ih) (Nat.le_max_left _ _)

theorem clause_size_le_of_width_three (plan : Plan Role Label) (clause : Clause) (hc : clause.length ≤ 3) :
    (plan.clause clause).size ≤ plan.clauseBound 3 :=
  (plan.clause_size_le clause).trans (plan.clauseBound_monotone hc)

theorem gates_size (tests : List (Label × Variable Role)) :
    (gates tests).size = 1 + 3 * tests.length := by
  induction tests with
  | nil => rfl
  | cons test tests ih =>
    change 1 + 1 + 1 + (gates tests).size = 1 + 3 * (tests.length + 1)
    rw [ih]
    omega

theorem rightComb_size_le (trees : List (Tree (Role := Role) (Label := Label)))
    (base : Tree (Role := Role) (Label := Label)) (bound : ℕ)
    (ht : ∀ tree ∈ trees, tree.size ≤ bound) :
    (rightComb trees base).size ≤ base.size + (bound + 1) * trees.length := by
  induction trees with
  | nil => exact Nat.le_refl _
  | cons tree trees ih =>
    have hs := ht tree (List.mem_cons_self ..)
    have hr := ih (fun t h => ht t (List.mem_cons_of_mem _ h))
    change 1 + tree.size + (rightComb trees base).size ≤ base.size + (bound + 1) * (trees.length + 1)
    nlinarith

private theorem size_variable_comb (inputs : List (Variable Role)) :
    (rightComb (inputs.map (fun i => (.var i : Tree (Role := Role) (Label := Label)))) (.var .root)).size =
      1 + 2 * inputs.length := by
  induction inputs with
  | nil => rfl
  | cons input inputs ih =>
    change 1 + 1 + (rightComb (inputs.map (fun i => .var i)) (.var .root)).size =
      1 + 2 * (inputs.length + 1)
    rw [ih]
    omega

theorem baseline_size (plan : Plan Role Label) (formula : CNF) :
    (plan.baseline formula).size = 1 + 2 *
      ((KFOL.Reductions.ResetUnion.support formula).length + plan.calibration.length) := by
  rw [baseline, size_variable_comb]
  simp only [inputs, List.length_append, List.length_map]

theorem calibrationBranch_size_le (plan : Plan Role Label) (branch : Tree (Role := Role) (Label := Label))
    (hb : branch ∈ plan.calibrationBranches) : branch.size ≤ 4 := by
  obtain ⟨item, _, hb⟩ := List.mem_flatMap.mp hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Nat.le_of_lt (by decide : 3 < 4)
  · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hb
    exact Nat.le_refl 4

private theorem length_flatMap_constant {α β : Type*} (xs : List α) (f : α → List β) (n : ℕ)
    (hf : ∀ x ∈ xs, (f x).length = n) : (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, hf x (List.mem_cons_self ..),
      ih (fun y h => hf y (List.mem_cons_of_mem _ h))]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem positiveTests_length (plan : Plan Role Label) (formula : CNF) :
    (plan.positiveTests formula).length =
      (KFOL.Reductions.ResetUnion.support formula).length * plan.preliminary.length +
        (plan.calibration.flatMap (fun item => item.2.1)).length := by
  rw [positiveTests, List.length_append,
    length_flatMap_constant _ _ plan.preliminary.length (fun _ _ => List.length_map ..)]
  congr 1
  induction plan.calibration with
  | nil => rfl
  | cons item items ih => simpa only [List.flatMap_cons, List.length_append, List.length_map] using congrArg (item.2.1.length + ·) ih

/-- The target size is affine in the number of listed Boolean names and
clauses, for each fixed policy family. The constant counts every expanded
macro copy and every fixed calibration branch. -/
theorem equation_size_le (plan : Plan Role Label) (formula : CNF)
    (hwidth : ∀ clause ∈ formula, clause.length ≤ 3) :
    (plan.equation formula).1.size + (plan.equation formula).2.size ≤
      4 + (4 + 3 * plan.preliminary.length) * (KFOL.Reductions.ResetUnion.support formula).length +
        2 * (max (plan.clauseBound 3) 4 + 1) * formula.length +
        4 * plan.calibration.length +
        3 * (plan.calibration.flatMap (fun item => item.2.1)).length +
        2 * (max (plan.clauseBound 3) 4 + 1) * plan.calibrationBranches.length := by
  have hR := rightComb_size_le (formula.map plan.clause ++ plan.calibrationBranches)
    (plan.baseline formula) (max (plan.clauseBound 3) 4) (by
      intro tree ht
      rcases List.mem_append.mp ht with ht | ht
      · obtain ⟨clause, hc, rfl⟩ := List.mem_map.mp ht
        exact (plan.clause_size_le_of_width_three clause (hwidth clause hc)).trans (Nat.le_max_left _ _)
      · exact (plan.calibrationBranch_size_le tree ht).trans (Nat.le_max_right _ _))
  rw [List.length_append, List.length_map, baseline_size] at hR
  change 1 + (gates (plan.positiveTests formula)).size +
    (rightComb (formula.map plan.clause ++ plan.calibrationBranches) (plan.baseline formula)).size +
    (rightComb (formula.map plan.clause ++ plan.calibrationBranches) (plan.baseline formula)).size ≤ _
  rw [gates_size, positiveTests_length]
  nlinarith

end KFOL.Policies.Hardness.Plan
