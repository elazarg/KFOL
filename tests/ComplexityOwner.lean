module

public import KFOL.Complexity.OwnerSynthesisBridge

/-! Whole owner-table machine checks, including rejected noncanonical input. -/

@[expose] public section

namespace KFOLTest.ComplexityOwner

open KFOL KFOL.Complexity

def singletonTable : Owner.GuardTable (Fin 1) :=
  ⟨0, [(0, ⟨∅, ∅⟩)]⟩

def duplicateTable : Owner.GuardTable (Fin 1) :=
  ⟨0, [(0, ⟨∅, ∅⟩), (0, ⟨∅, ∅⟩)]⟩

example : singletonTable.check (List.finRange 1) = true := by decide
example : duplicateTable.check (List.finRange 1) = false := by decide

example : OwnerRuntime.check (1, OwnerRuntime.tableView singletonTable) = true := by
  rw [OwnerRuntime.check_view]
  decide

example : OwnerRuntime.check (1, OwnerRuntime.tableView duplicateTable) = false := by
  rw [OwnerRuntime.check_view]
  decide

example : OwnerRuntime.canonical (0, []) = false := by decide

example {n : ℕ} (T : Owner.GuardTable (Fin n)) :
    OwnerRuntime.check (n, OwnerRuntime.tableView T) = T.check (List.finRange n) :=
  OwnerRuntime.check_view T

open Turing.MultiTapeTM

example : ComputableInPolyTime
    (fun input : OwnerRuntime.Input => input.2.check (List.finRange input.1))
    OwnerRuntime.inputEncoding encBool := OwnerRuntime.source_check_polyTime

example : singletonTable.synthesize () (List.finRange 1) =
    some (Owner.Term.step (.var 0) (.var 0)) := by
  unfold Owner.GuardTable.synthesize
  rw [show singletonTable.check (List.finRange 1) = true by decide]
  rfl

example : duplicateTable.synthesize () (List.finRange 1) = none := by
  unfold Owner.GuardTable.synthesize
  rw [show duplicateTable.check (List.finRange 1) = false by decide]
  rfl

example : OwnerRuntime.synthesize () (1, OwnerRuntime.tableView singletonTable) =
    (singletonTable.synthesize () (List.finRange 1)).map
      (FirstOrder.Language.Term.relabel Fin.val) := OwnerRuntime.synthesize_view () singletonTable

example : ComputableInPolyTime
    (fun input : OwnerRuntime.Input =>
      (input.2.synthesize () (List.finRange input.1)).map
        (fun term => (⟨input.1, term⟩ : OwnerRuntime.Output Unit)))
    OwnerRuntime.inputEncoding (encOption OwnerRuntime.outputEncoding) :=
  OwnerRuntime.source_synthesize_polyTime ()

end KFOLTest.ComplexityOwner
