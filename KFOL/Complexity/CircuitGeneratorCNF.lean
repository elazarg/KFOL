module
public import KFOL.Complexity.CircuitGeneratorBuilders
/-! Original CNF builders as independent clause chunks indexed by physical prefixes. Empty clauses retain their exact reset-to-root behavior. -/

@[expose] public section
namespace KFOL.Complexity.CircuitGenerator
open CircuitMachine

/-- The last clause is read from the physical list, never from its labels. -/
def lastClause (clauses : List (List ℕ)) : List ℕ := clauses.reverse.headD []

private theorem lastClause_cons (head : List ℕ) (tail : List (List ℕ)) (ht : tail ≠ []) :
    lastClause (head :: tail) = lastClause tail := by
  cases hr : tail.reverse with
  | nil => simp only [List.reverse_eq_nil_iff] at hr; exact (ht hr).elim
  | cons C Cs => simp only [lastClause, List.reverse_cons, hr, List.cons_append, List.headD_cons]

/-- Actual output after a prefix, including the empty-clause reset to root. -/
def prefixOutput (clauses : List (List ℕ)) (previous root offset : ℕ) : ℕ :=
  if clauses.isEmpty then previous else
    if (lastClause clauses).isEmpty then root else offset + 2 * clauses.flatten.length - 1

@[simp] theorem prefixOutput_nil (previous root offset : ℕ) :
    prefixOutput [] previous root offset = previous := rfl

theorem prefixOutput_cons (head : List ℕ) (tail : List (List ℕ)) (previous root offset : ℕ) :
    prefixOutput (head :: tail) previous root offset =
      prefixOutput tail (lastRef root offset (2 * head.length)) root (offset + 2 * head.length) := by
  cases tail with
  | nil =>
    simp only [prefixOutput, List.isEmpty_cons, Bool.false_eq_true, ite_false,
      lastClause, List.reverse_cons, List.reverse_nil, List.nil_append, List.headD_cons,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.isEmpty_nil, ite_true, lastRef]
    cases head with
    | nil => simp
    | cons x xs => simp only [List.isEmpty_cons, List.length_cons, Bool.false_eq_true, ite_false]
                   rw [ite_eq_right (by omega)]
  | cons C Cs =>
    rw [prefixOutput, prefixOutput, lastClause_cons head (C :: Cs) (by simp)]
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false, List.flatten_cons, List.length_append]
    split <;> omega

/-- Independent chunks indexed by original clause positions. Taking a prefix
reads its bytes; it does not copy any already generated graph into a gate. -/
def cnfNodes (clauses : List (List ℕ)) (previous root offset : ℕ) : Gates :=
  clauses.zipIdx.flatMap fun item =>
    let consumed := clauses.take item.2
    clauseNodes item.1 (prefixOutput consumed previous root offset) root
      (offset + 2 * consumed.flatten.length)

@[simp] theorem cnfNodes_nil (previous root offset : ℕ) : cnfNodes [] previous root offset = [] := rfl

theorem cnfNodes_cons (head : List ℕ) (tail : List (List ℕ)) (previous root offset : ℕ) :
    cnfNodes (head :: tail) previous root offset =
      clauseNodes head previous root offset ++
        cnfNodes tail (lastRef root offset (2 * head.length)) root (offset + 2 * head.length) := by
  simp only [cnfNodes, List.zipIdx_cons', List.flatMap_cons, List.take_zero,
    prefixOutput_nil, List.flatten_nil, List.length_nil, Nat.mul_zero, Nat.add_zero,
    List.flatMap_map]
  congr 1
  congr 1
  funext item
  dsimp only [Function.comp_def, Prod.map, id_eq]
  rw [List.take_succ_cons, prefixOutput_cons]
  simp only [List.flatten_cons, List.length_append]
  congr 1
  omega

theorem view_buildCNF (clauses : List (List ℕ)) (previous root : ℕ)
    (gates : List (Circuit.Gate Reset.Symbol ℕ)) :
    (Circuit.buildCNF clauses previous root gates).gates.map viewGate =
      gates.map viewGate ++ cnfNodes clauses previous root gates.length ∧
    (Circuit.buildCNF clauses previous root gates).output =
      prefixOutput clauses previous root gates.length := by
  induction clauses generalizing previous gates with
  | nil => simp [Circuit.buildCNF]
  | cons head tail ih =>
    have hh := view_buildClause head previous root gates
    have ht := ih (Circuit.buildClause head previous root gates).output
      (Circuit.buildClause head previous root gates).gates
    constructor
    · simpa only [Circuit.buildCNF, ht.1, hh.1, hh.2, Circuit.length_buildClause,
        cnfNodes_cons, List.append_assoc] using ht.1
    · simpa only [Circuit.buildCNF, hh.2, Circuit.length_buildClause,
        prefixOutput_cons] using ht.2
end KFOL.Complexity.CircuitGenerator
