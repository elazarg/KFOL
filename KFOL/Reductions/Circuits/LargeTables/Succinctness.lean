module

public import KFOL.Reductions.Circuits.LargeTables.Graph
public import KFOL.Reset.SemanticBounds

/-! Semantic tree lower bounds for an explicit linear shared reset circuit.
The marker budget is exact, not an artifact of a particular unfolding. -/

@[expose] public section
namespace KFOL.Circuit.LargeTables

universe u
variable {Role : Type u}

/-- Every reset tree representing this operation needs 2^n occurrences of
its marker input, even when arbitrary additional variable names are allowed. -/
theorem marker_occurrences_le_of_eval_eq (three : Fin 3 ↪ Role) (n : ℕ)
    (t : Reset.Term Variable)
    (equal : ∀ valuation : Variable → WinnerSet Role, t.eval valuation = (tree n).eval valuation) :
    2^n ≤ t.occurrences markerName := by
  have h := Reset.Term.card_table_le_occurrences_of_eval_eq three (tree n) t
    (fun valuation => (equal valuation).symm) markerName
  rwa [card_table_marker] at h

/-- A nonmarker root leaf is needed in addition to the marker budget. -/
theorem leafCount_lower_of_eval_eq (three : Fin 3 ↪ Role) (n : ℕ)
    (t : Reset.Term Variable)
    (equal : ∀ valuation : Variable → WinnerSet Role, t.eval valuation = (tree n).eval valuation) :
    2^n+1 ≤ t.leafCount := by
  have h := Reset.Term.card_table_add_one_le_leafCount_of_eval_eq three (tree n) t
    (fun valuation => (equal valuation).symm) markerName
    (by simp only [root_tree]; decide)
  rwa [card_table_marker] at h

/-- Primitive constructor size is exponentially large for every equivalent
reset tree, independent of how it is obtained from the graph. -/
theorem size_lower_of_eval_eq (three : Fin 3 ↪ Role) (n : ℕ)
    (t : Reset.Term Variable)
    (equal : ∀ valuation : Variable → WinnerSet Role, t.eval valuation = (tree n).eval valuation) :
    2^(n+1)+1 ≤ t.size := by
  have hlower := leafCount_lower_of_eval_eq three n t equal
  have hsize := t.size_add_one
  rw [pow_succ]
  omega

/-- The exact minimum number of marker occurrences for this term function.
The lower bound is attained by the displayed unfolding. -/
theorem minimum_marker_occurrences (three : Fin 3 ↪ Role) (n : ℕ) :
    IsLeast {count : ℕ | ∃ t : Reset.Term Variable,
      (∀ valuation : Variable → WinnerSet Role, t.eval valuation = (tree n).eval valuation) ∧
      t.occurrences markerName = count} (2^n) := by
  constructor
  · exact ⟨tree n,fun _ => rfl,occurrences_marker_tree n⟩
  · rintro count ⟨t,equal,hcount⟩
    rw [← hcount]
    exact marker_occurrences_le_of_eval_eq three n t equal

/-- A direct circuit-to-tree separation. Any original tree whose actual
WinnerSet semantics realizes this original shared graph has exponential
marker, leaf and constructor cost; proof-only unfolding is not required of it. -/
theorem graph_tree_lower_bounds (three : Fin 3 ↪ Role) (n : ℕ) (t : Reset.Term Variable)
    (equal : let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
      ∀ valuation : Variable → WinnerSet Role,
        (graph n).eval valuation = some (t.eval valuation,t.eval valuation)) :
    2^n ≤ t.occurrences markerName ∧ 2^n+1 ≤ t.leafCount ∧ 2^(n+1)+1 ≤ t.size := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  have hterm : ∀ valuation : Variable → WinnerSet Role,
      t.eval valuation = (tree n).eval valuation := by
    intro valuation
    have hgraph := (graph n).eval_of_unfold (tree n) (tree n) (graph_unfold n) valuation
    have heq := Option.some.inj ((equal valuation).symm.trans hgraph)
    exact congrArg Prod.fst heq
  exact ⟨marker_occurrences_le_of_eval_eq three n t hterm,
    leafCount_lower_of_eval_eq three n t hterm,size_lower_of_eval_eq three n t hterm⟩

end KFOL.Circuit.LargeTables
