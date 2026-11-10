module
import KFOL.Reductions.Circuits.LargeTables.Graph
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

#print axioms linear_graph_exponential_table
#print axioms graph_input_gate_count
#print axioms graph_edge_count
#print axioms guard_subset_iff
end KFOL.Tests.LargeCircuitTables
