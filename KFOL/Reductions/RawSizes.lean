module

public import KFOL.Reductions.RawPair

/-! Exact original native tree sizes for the hard raw binary pairs. -/

@[expose] public section

namespace KFOL.RawPair.Term

universe v

variable {Var : Type v}

@[simp] theorem size_var (j : Var) : size (.var j) = 1 := rfl
@[simp] theorem size_node (sign : Bool) (s t : Term Var) :
    (node sign s t).size = 1 + s.size + t.size := rfl

theorem size_fold (sign : Bool) (terms : List (Term Var)) (base : Term Var) :
    (fold sign terms base).size = base.size + terms.length + (terms.map size).sum := by
  induction terms with
  | nil => simp [fold]
  | cons t terms ih =>
    change 1 + t.size + (fold sign terms base).size = _
    rw [ih]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem size_variable_fold (sign : Bool) (inputs : List Var) (root : Var) :
    (fold sign (inputs.map (fun i => .var i)) (.var root)).size = 1 + 2 * inputs.length := by
  induction inputs with
  | nil => rfl
  | cons i inputs ih =>
    change 1 + 1 + (fold sign (inputs.map (fun i => .var i)) (.var root)).size = _
    rw [ih]
    simp only [List.length_cons]
    omega

end KFOL.RawPair.Term

namespace KFOL.Reductions.RawPair

@[simp] theorem size_literalTerm (literal : Literal) : (literalTerm literal).size = 1 := rfl
@[simp] theorem length_rails (formula : CNF) : (rails formula).length = 2 * (ResetUnion.support formula).length := by
  unfold rails
  induction ResetUnion.support formula with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
    omega

private theorem sum_rails_size (formula : CNF) :
    ((rails formula).map KFOL.RawPair.Term.size).sum = (rails formula).length := by
  unfold rails
  induction ResetUnion.support formula with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, size_literalTerm, List.length_append, List.length_cons, List.length_nil, ih]
    omega

@[simp] theorem size_baseline (formula : CNF) : (baseline formula).size = 1 + 4 * (ResetUnion.support formula).length := by
  rw [baseline, KFOL.RawPair.Term.size_fold, size_literalTerm, sum_rails_size, length_rails]
  omega

@[simp] theorem size_branch (i : ℕ) : (branch i).size = 5 := rfl

theorem size_right (formula : CNF) : (right formula).size = 1 + 10 * (ResetUnion.support formula).length := by
  rw [right, KFOL.RawPair.Term.size_fold, size_baseline, List.length_map]
  have hs : (((ResetUnion.support formula).map branch).map KFOL.RawPair.Term.size).sum =
      5 * (ResetUnion.support formula).length := by
    induction ResetUnion.support formula with
    | nil => rfl
    | cons i rest ih =>
      simp only [List.map_cons, List.sum_cons, size_branch, List.length_cons, ih]
      omega
  rw [hs]
  omega

theorem size_clause_add_one (C : Clause) (hne : C ≠ []) : (clause C).size + 1 = 2 * C.length := by
  cases C with
  | nil => exact False.elim (hne rfl)
  | cons literal rest =>
    rw [clause, KFOL.RawPair.Term.size_fold, size_literalTerm, List.length_map, List.length_cons]
    have hs : ((rest.map literalTerm).map KFOL.RawPair.Term.size).sum = rest.length := by
      clear hne
      induction rest with
      | nil => rfl
      | cons l rest ih =>
        simp only [List.map_cons, List.sum_cons, size_literalTerm, List.length_cons, ih]
        omega
    rw [hs]
    omega

theorem size_left (formula : CNF) (hnonempty : ∀ C ∈ formula, C ≠ []) :
    (left formula).size = 1 + 2 * (formula.map List.length).sum := by
  rw [left, KFOL.RawPair.Term.size_fold, KFOL.RawPair.Term.size_var, List.length_map]
  have hs : ((formula.map clause).map KFOL.RawPair.Term.size).sum + formula.length =
      2 * (formula.map List.length).sum := by
    induction formula with
    | nil => rfl
    | cons C formula ih =>
      have hC := size_clause_add_one C (hnonempty C (List.mem_cons_self ..))
      have ht := ih (fun C hc => hnonempty C (List.mem_cons_of_mem _ hc))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  omega

theorem coreEquation_size (formula : CNF) (hnonempty : ∀ C ∈ formula, C ≠ []) :
    (coreEquation formula).1.size + (coreEquation formula).2.size =
      4 + 20 * (ResetUnion.support formula).length + 2 * (formula.map List.length).sum := by
  change 1 + (left formula).size + (right formula).size + (right formula).size = _
  rw [size_left formula hnonempty, size_right]
  omega

/-- The entire native reduction, including its empty-clause gate, has a
linear original-tree bound even for clauses of unbounded width. -/
theorem equation_size_le (formula : CNF) :
    (equation formula).1.size + (equation formula).2.size ≤
      4 + 20 * (ResetUnion.support formula).length + 2 * (formula.map List.length).sum := by
  classical
  by_cases he : formula.any List.isEmpty = true
  · simp only [equation, he, ite_true, KFOL.RawPair.Term.size_var]
    omega
  · have hnonempty : ∀ C ∈ formula, C ≠ [] := by
      intro C hc hnil
      exact he (List.any_eq_true.mpr ⟨C, hc, by simp [hnil]⟩)
    rw [equation, ite_eq_right he, coreEquation_size formula hnonempty]

end KFOL.Reductions.RawPair

namespace KFOL.Reductions.RawPair

/-- The two-owner empty-conjunction branch also retains the same native
linear bound; both reductions use the identical binary signature. -/
theorem twoOwnerEquation_size_le (formula : CNF) :
    (twoOwnerEquation formula).1.size + (twoOwnerEquation formula).2.size ≤
      4 + 20 * (ResetUnion.support formula).length + 2 * (formula.map List.length).sum := by
  cases formula with
  | nil =>
    simp only [twoOwnerEquation, List.isEmpty_nil, ite_true, KFOL.RawPair.Term.size_var,
      List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
    omega
  | cons C formula =>
    simp only [twoOwnerEquation, List.isEmpty_cons, Bool.false_eq_true, ite_false]
    exact equation_size_le _

end KFOL.Reductions.RawPair
