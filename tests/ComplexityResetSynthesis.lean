module

public import KFOL.Complexity.ResetSynthesisMachine

@[expose] public section

namespace KFOLTest.ComplexityResetSynthesis

open KFOL KFOL.Algorithms KFOL.Complexity
open Turing.MultiTapeTM

/-- Root is position one, the dictionary has an unused position, the first
record is not the root, and the root record occurs twice. -/
private def sparse : GuardDescriptor :=
  ⟨[1000000000, 7, 9], by decide,
    [(⟨0, by decide⟩, {⟨1, by decide⟩}), (⟨1, by decide⟩, ∅), (⟨1, by decide⟩, ∅)]⟩

private def expected : Reset.Term ℕ :=
  Reset.Term.step (Reset.Term.step (.var 1000000000) (.var 7))
    (Reset.Term.step (.var 7) (Reset.Term.step (.var 7) (.var 7)))

example : sparse.check = true := by decide
example : ResetSynthesis.synthesize sparse = some expected := by rfl
example : expected.size = 9 := by decide
example : ResetSynthesis.synthesizeCode sparse.encode = some (TermCode.encode expected) := by
  rw [ResetSynthesis.synthesizeCode_encode]
  have h : ResetSynthesis.synthesize sparse = some expected := by rfl
  rw [h]
  rfl

private def empty : GuardDescriptor := ⟨[], by decide, []⟩
example : ResetSynthesis.synthesize empty = none := by decide
example : ResetSynthesis.synthesizeCode [] = none := by decide

example (word : List Bool) :
    (ResetSynthesis.synthesizeCode word).isSome = GuardDescriptor.recognize word :=
  ResetSynthesis.synthesizeCode_isSome word

example : ComputableInPolyTime ResetSynthesis.synthesizeCode encBits (encOption encBits) :=
  ResetSynthesis.synthesizeCode_polyTime

example (d : GuardDescriptor) (h : d.check = true) :
    ∃ (root : Fin d.labels.length) (t : Reset.Term (Fin d.labels.length)),
      ResetSynthesis.synthesize d = some (t.relabel d.labels.get) ∧ t.root = root ∧
      t.table = d.guards ∧ t.size ≤ 1 + 2 * d.labels.length * d.records.length :=
  ResetSynthesis.synthesize_spec d h

/-- info: 'KFOL.Reset.GuardTable.greedyOrder_eq_of_card_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Reset.GuardTable.greedyOrder_eq_of_card_le

/-- info: 'KFOL.Algorithms.GuardDescriptor.recordTerm_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Algorithms.GuardDescriptor.recordTerm_spec

/-- info: 'KFOL.Complexity.ResetSynthesis.run_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.run_view

/-- info: 'KFOL.Complexity.ResetSynthesis.run_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.run_polyTime

/-- info: 'KFOL.Complexity.ResetSynthesis.pathTerm_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.pathTerm_polyTime

/-- info: 'KFOL.Complexity.ResetSynthesis.joinPaths_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.joinPaths_polyTime

/-- info: 'KFOL.Complexity.ResetSynthesis.path_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.path_view

/-- info: 'KFOL.Complexity.ResetSynthesis.rawSynthesize_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.rawSynthesize_polyTime

/-- info: 'KFOL.Complexity.ResetSynthesis.rawSynthesize_view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.rawSynthesize_view

/-- info: 'KFOL.Complexity.ResetSynthesis.synthesizeWord_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.synthesizeWord_polyTime

/-- info: 'KFOL.Complexity.ResetSynthesis.synthesize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.synthesize_spec

/-- info: 'KFOL.Complexity.ResetSynthesis.synthesize_semantics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.synthesize_semantics

/-- info: 'KFOL.Complexity.ResetSynthesis.synthesizeCode_polyTime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.synthesizeCode_polyTime

/-- info: 'KFOL.Complexity.ResetSynthesis.synthesizeCode_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.synthesizeCode_isSome

/-- info: 'KFOL.Complexity.ResetSynthesis.synthesizeCode_encode_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Complexity.ResetSynthesis.synthesizeCode_encode_spec

end KFOLTest.ComplexityResetSynthesis
