module

public import KFOL.Algorithms.ResetUnionCode

/-! # Exact native tree size of the CNF reduction -/

@[expose] public section

namespace KFOL.ResetUnion.Term

universe v

variable {Var : Type v}

theorem size_rightComb (xs : List (Term Var)) (base : Term Var) :
    (rightComb xs base).size = base.size + (xs.map (fun t => 1 + t.size)).sum := by
  induction xs with
  | nil => simp [rightComb]
  | cons t xs ih =>
    change (reset t (rightComb xs base)).size = _
    rw [size_reset, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem size_leftComb (xs : List (Term Var)) (base : Term Var) :
    (leftComb base xs).size = base.size + (xs.map (fun t => 1 + t.size)).sum := by
  induction xs generalizing base with
  | nil => simp [leftComb]
  | cons t xs ih =>
    change (leftComb (reset base t) xs).size = _
    rw [ih, size_reset]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem size_unionFold (xs : List (Term Var)) (base : Term Var) :
    (unionFold base xs).size = base.size + (xs.map (fun t => 1 + t.size)).sum := by
  induction xs generalizing base with
  | nil => simp [unionFold]
  | cons t xs ih =>
    change (unionFold (union base t) xs).size = _
    rw [ih, size_union]
    simp only [List.map_cons, List.sum_cons]
    omega

end KFOL.ResetUnion.Term

namespace KFOL.Reductions.ResetUnion

open KFOL.ResetUnion

@[simp] theorem size_literalTerm (literal : Literal) : (literalTerm literal).size = 1 := rfl
@[simp] theorem size_branch (j : ℕ) : (branch j).size = 9 := rfl

theorem size_baseline (formula : CNF) : (baseline formula).size = 4 * (support formula).length + 3 := by
  have hsum (xs : List ℕ) :
      ((xs.flatMap (fun j => [literalTerm (j, true), literalTerm (j, false)])).map
        (fun t => 1 + t.size)).sum = 4 * xs.length := by
    induction xs with
    | nil => rfl
    | cons j xs ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil, size_literalTerm, List.length_cons, ih]
      omega
  rw [baseline, Term.size_rightComb]
  simp only [List.map_append, List.sum_append, hsum, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Term.size_var]
  omega

theorem size_right (formula : CNF) : (right formula).size = 14 * (support formula).length + 3 := by
  have hsum (xs : List ℕ) : ((xs.map branch).map (fun t => 1 + t.size)).sum = 10 * xs.length := by
    induction xs with
    | nil => rfl
    | cons j xs ih => simp only [List.map_cons, List.sum_cons, size_branch, List.length_cons, ih]; omega
  rw [right, Term.size_rightComb, size_baseline, hsum]
  omega

theorem size_clauseGuard (C : Clause) : (clauseGuard C).size = 1 + 2 * C.length := by
  have hsum : ((C.map literalTerm).map (fun t => 1 + t.size)).sum = 2 * C.length := by
    induction C with
    | nil => rfl
    | cons literal C ih => simp only [List.map_cons, List.sum_cons, size_literalTerm, List.length_cons, ih]; omega
  rw [clauseGuard, Term.size_unionFold, Term.size_var, hsum]

theorem size_left (formula : CNF) :
    (left formula).size = 1 + 2 * formula.length + 2 * formula.flatten.length := by
  have hsum : ((formula.map clauseGuard).map (fun t => 1 + t.size)).sum =
      2 * formula.length + 2 * formula.flatten.length := by
    induction formula with
    | nil => rfl
    | cons C formula ih =>
      simp only [List.map_cons, List.sum_cons, size_clauseGuard, List.length_cons,
        List.flatten_cons, List.length_append, ih]
      omega
  rw [left, Term.size_leftComb, Term.size_var, hsum]
  omega

/-- Count every node and copied continuation in both actual output trees. -/
theorem size_equation (formula : CNF) :
    (equation formula).1.size + (equation formula).2.size =
      28 * (support formula).length + 2 * formula.length + 2 * formula.flatten.length + 8 := by
  change (Term.reset (left formula) (right formula)).size + (right formula).size = _
  rw [Term.size_reset, size_left, size_right]
  omega

/-- Sparse support extraction bounds syntax by input occurrences, without
iterating up to any numeric variable name. -/
theorem support_length_le (formula : CNF) : (support formula).length ≤ 1 + formula.flatten.length := by
  simpa only [support, List.length_cons, List.length_map, Nat.add_comm] using
    (0 :: formula.flatten.map Prod.fst).dedup_sublist.length_le

theorem size_equation_linear (formula : CNF) :
    (equation formula).1.size + (equation formula).2.size ≤
      30 * (formula.length + formula.flatten.length) + 36 := by
  rw [size_equation]
  have h := support_length_le formula
  omega

end KFOL.Reductions.ResetUnion
