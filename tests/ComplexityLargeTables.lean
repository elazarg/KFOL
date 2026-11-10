module
import KFOL.Reductions.Circuits.LargeTables.Succinctness
namespace KFOL.Tests.LargeCircuitTables
open KFOL.Circuit.LargeTables

example (n : ℕ) :
    (graph n).WellFormed ∧ (graph n).gates.length = 6*n+3 ∧
      KFOL.Circuit.operationCount (graph n).gates = 4*n+1 ∧
      (graph n).unfold = some (tree n,tree n) ∧
      2^n ≤ ((tree n).table markerName).card := linear_graph_exponential_table n
example (n : ℕ) :
    ((graph n).gates.map (fun gate => gate.references.length)).sum = 8*n+2 := graph_edge_count n
example (n : ℕ) (first second : Fin n → Bool) :
    guard n first ⊆ guard n second ↔ first = second := guard_subset_iff n first second
example : ((tree 0).table markerName).card = 1 := by decide
example : ((tree 1).table markerName).card = 2 := by decide
example : ((tree 2).table markerName).card = 4 := by decide
example (B : Set Variable) : (tree 2).Selected B markerName ↔
    rootName ∈ B ∧ ∀ i < 2, rail i true ∈ B ∨ rail i false ∈ B := selected_marker 2 B

example (n : ℕ) : (tree n).table markerName = Finset.univ.image (guard n) := table_marker_eq n
example (n : ℕ) : ((tree n).table markerName).card = 2^n := card_table_marker n
example (n : ℕ) {A : Finset Variable} (hA : A ∈ (tree n).table markerName) :
    A.card = n+1 := card_mem_table_marker n hA
example (n : ℕ) : ∑ A ∈ (tree n).table markerName, A.card = (n+1)*2^n := sum_guard_card_marker n
example (n : ℕ) : (tree n).occurrences markerName = 2^n := occurrences_marker_tree n
example {Role : Type} (three : Fin 3 ↪ Role) (n : ℕ) (t : KFOL.Reset.Term Variable)
    (equal : ∀ v : Variable → KFOL.WinnerSet Role, t.eval v = (tree n).eval v) :
    2^n ≤ t.occurrences markerName ∧ 2^n+1 ≤ t.leafCount ∧ 2^(n+1)+1 ≤ t.size :=
  ⟨marker_occurrences_le_of_eval_eq three n t equal,
   leafCount_lower_of_eval_eq three n t equal,size_lower_of_eval_eq three n t equal⟩
example (n : ℕ) : IsLeast {count : ℕ | ∃ t : KFOL.Reset.Term Variable,
    (∀ v : Variable → KFOL.WinnerSet (Fin 3), t.eval v = (tree n).eval v) ∧
      t.occurrences markerName = count} (2^n) := minimum_marker_occurrences (Function.Embedding.refl _) n

#print axioms table_marker_eq
#print axioms card_table_marker
#print axioms minimum_marker_occurrences
#print axioms graph_tree_lower_bounds

#print axioms linear_graph_exponential_table
#print axioms graph_input_gate_count
#print axioms graph_edge_count
#print axioms guard_subset_iff
end KFOL.Tests.LargeCircuitTables
