module

public import KFOL.Reset.Extraction
public import KFOL.Reset.Chain

/-! Canonical guard counts give semantic lower bounds on all equivalent trees.
The occurrence and leaf counts are the existing independent syntax measures. -/

@[expose] public section
namespace KFOL.Reset.Term

universe u v
variable {Role : Type u} {Var : Type v} [DecidableEq Var]

theorem occurrences_le_leafCount (t : Term Var) (j : Var) : t.occurrences j ≤ t.leafCount := by
  calc
    _ = t.guardEntries.countP (fun entry => decide (entry.1 = j)) := (t.countP_guardEntries j).symm
    _ ≤ t.guardEntries.length := List.countP_le_length
    _ = t.leafCount := t.length_guardEntries

/-- The rightmost root contributes at least one leaf distinct from j. -/
theorem occurrences_lt_leafCount_of_ne_root (t : Term Var) (j : Var) (hne : j ≠ t.root) :
    t.occurrences j < t.leafCount := by
  induction t using induction_reset with
  | var i =>
    change j ≠ i at hne
    simp [occurrences_var,leafCount_var,hne]
  | step s t _ ht =>
    have hright := ht hne
    have hleft := s.occurrences_le_leafCount j
    rw [occurrences_step,leafCount_step]
    omega

/-- Semantic equivalence preserves the independently defined rightmost root. -/
theorem root_eq_of_eval_eq (three : Fin 3 ↪ Role) (s t : Term Var)
    (equal : ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) :
    s.root = t.root := by
  have tables := (eval_eq_iff_table s t three).mp equal
  have h : ∅ ∈ t.table s.root := by
    rw [← tables]
    exact (s.empty_mem_table s.root).mpr rfl
  exact (t.empty_mem_table s.root).mp h

/-- Any tree for a given term function needs one syntactic occurrence of j
for each distinct canonical minimal guard enabling j. -/
theorem card_table_le_occurrences_of_eval_eq (three : Fin 3 ↪ Role) (s t : Term Var)
    (equal : ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) (j : Var) :
    (s.table j).card ≤ t.occurrences j := by
  rw [(eval_eq_iff_table s t three).mp equal]
  exact t.card_table_le_occurrences j

theorem card_table_le_leafCount_of_eval_eq (three : Fin 3 ↪ Role) (s t : Term Var)
    (equal : ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) (j : Var) :
    (s.table j).card ≤ t.leafCount :=
  (card_table_le_occurrences_of_eval_eq three s t equal j).trans (t.occurrences_le_leafCount j)

/-- At a nonroot input, at least one additional leaf is needed for the root. -/
theorem card_table_add_one_le_leafCount_of_eval_eq (three : Fin 3 ↪ Role) (s t : Term Var)
    (equal : ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation)
    (j : Var) (hne : j ≠ s.root) : (s.table j).card+1 ≤ t.leafCount := by
  have hroot := root_eq_of_eval_eq three s t equal
  have hocc := card_table_le_occurrences_of_eval_eq three s t equal j
  have hne' : j ≠ t.root := by simpa only [hroot] using hne
  have hlt := t.occurrences_lt_leafCount_of_ne_root j hne'
  omega

end KFOL.Reset.Term
