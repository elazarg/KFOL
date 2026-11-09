module

public import KFOL.Reset.Extraction

/-! Actual traversal lists, repeated leaves, normalization and infinite ambients. -/

@[expose] public section

namespace KFOLTest.ResetExtraction

open KFOL KFOL.Reset KFOL.Reset.Term

private def x (i : Fin 4) : Reset.Term (Fin 4) := .var i
private def alternatives : Reset.Term (Fin 4) :=
  step (step (step (x 3) (x 1)) (x 0)) (step (step (x 3) (x 2)) (x 0))

-- The two copies of variable 3 contribute independent prerequisite paths.
example : alternatives.guardEntries =
    [(0, ∅), (2, {0}), (3, {0, 2}), (0, {0}), (1, {0}), (3, {0, 1})] := by decide

example : alternatives.leafCount = 6 ∧ alternatives.occurrences 3 = 2 ∧
    alternatives.guardTable.entryCount = 5 := by decide

-- The actual normalized collector recovers both alternatives for output 3.
example : minimize
    (((alternatives.guardEntries.filter (fun p => p.1 = 3)).map Prod.snd).toFinset) =
      {{0, 1}, {0, 2}} := by decide

-- Before normalization the output label may occur in its own raw guard.
-- Duplicate deletion and antichain minimization are different operations.
private def repeated : Reset.Term (Fin 1) := step (step (.var 0) (.var 0)) (.var 0)

example : repeated.guardEntries = [(0, ∅), (0, {0}), (0, {0})] ∧
    repeated.occurrences 0 = 3 ∧ (repeated.guards 0).card = 2 ∧
    (repeated.table 0).card = 1 := by decide

-- Label counts refer to the actual syntax and support. An arbitrarily large
-- variable name does not introduce intervening unused declarations.
private def padded : Reset.Term ℕ := step (.var 100000) (.var 7)

example : padded.guardEntries = [(7, ∅), (100000, {7})] ∧
    padded.leafCount = 2 ∧ padded.varFinset.card = 2 ∧ padded.table 42 = ∅ := by decide

example : (1 + ∑ j ∈ padded.varFinset, ∑ A ∈ padded.table j, (A.card + 1)) = 4 := by decide

-- The general bound applies directly to this infinite ambient type.
example : 1 + ∑ j ∈ padded.varFinset, ∑ A ∈ padded.table j, (A.card + 1) ≤ 5 := by
  simpa only [show padded.varFinset.card = 2 from by decide,
    show padded.leafCount = 2 from by decide] using padded.table_description_le

end KFOLTest.ResetExtraction
