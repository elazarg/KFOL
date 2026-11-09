module

public import KFOL.Algorithms.GuardDescriptor

/-! Whole-word validation, unused positions and exact canonical recognition. -/

@[expose] public section

namespace KFOLTest.GuardDescriptor

open KFOL KFOL.Algorithms

set_option maxRecDepth 4096

private def good : GuardDescriptor :=
  ⟨[100000, 7, 42], by decide, [(1, ∅), (0, {1})]⟩

-- Root selection uses the guards, not dictionary order; position 2 is unused.
example : good.root?.map Fin.val = some 1 := by decide
example : good.check = true := by decide
example : GuardDescriptor.recognize (GuardDescriptor.encode good) = true := by decide
example : (GuardDescriptor.encode good).length = 146 := by decide
example : (GuardDescriptor.decode (GuardDescriptor.encode good)).map (fun d =>
    (d.labels, d.records.map (fun r => (r.1.val, Bitset.encode r.2)))) =
      some ([100000, 7, 42], [(1, [false, false, false]), (0, [false, true, false])]) := by decide

private def duplicateRecords : GuardDescriptor :=
  ⟨[100000, 7, 42], by decide, [(1, ∅), (0, {1}), (0, {1})]⟩

example : duplicateRecords.check = true := by decide
example : (duplicateRecords.table ⟨1, by decide⟩).entryCount = 2 := by decide
example : duplicateRecords.records.length = 3 := by decide

private def empty : GuardDescriptor := ⟨[], by decide, []⟩
example : (GuardDescriptor.decode (GuardDescriptor.encode empty)).isSome = true := by decide
example : GuardDescriptor.recognize (GuardDescriptor.encode empty) = false := by decide

private def multipleRoots : GuardDescriptor := ⟨[7, 42], by decide, [(0, ∅), (1, ∅)]⟩
private def noRoot : GuardDescriptor := ⟨[7, 42], by decide, [(0, {1}), (1, {0})]⟩
private def cycle : GuardDescriptor :=
  ⟨[7, 42, 100000], by decide, [(0, ∅), (1, {2}), (2, {1})]⟩
private def dominated : GuardDescriptor :=
  ⟨[7, 42, 100000], by decide, [(1, ∅), (0, {1}), (0, {1, 2})]⟩
private def selfDependent : GuardDescriptor :=
  ⟨[7, 42], by decide, [(1, ∅), (0, {0, 1})]⟩

example : multipleRoots.check = false := by decide
example : noRoot.check = false := by decide
example : cycle.check = false := by decide
example : dominated.check = false := by decide
example : selfDependent.check = false := by decide

-- Dictionary validation is stricter than the binary list codec.
example : GuardDescriptor.decode (_root_.Complexity.pair (LabelDictionary.encode [7, 7])
    (GuardRecord.encodeList ([(0, ∅)] : List (GuardRecord.Record 2)))) = none := by decide
example : GuardDescriptor.decode (_root_.Complexity.pair (LabelDictionary.encode [7])
    (GuardRecord.encodeList ([(1, ∅)] : List (GuardRecord.Record 2)))) = none := by decide
-- A valid index but the wrong prerequisite width is also rejected.
example : GuardDescriptor.decode (_root_.Complexity.pair (LabelDictionary.encode [7])
    (_root_.Complexity.delimit (_root_.Complexity.pair [] [false, false]))) = none := by decide
example : GuardDescriptor.decode (GuardDescriptor.encode good ++ [true]) = none := by decide
example : GuardDescriptor.recognize [true] = false := by decide

private def repeated : Reset.Term ℕ := Reset.Term.step
  (Reset.Term.step (.var 7) (.var 7)) (.var 7)

-- Raw extraction is a valid descriptor. Its nonminimal guards still need
-- normalization before the canonical-table recognizer can accept them.
example : ((TermCode.extract (TermCode.encode repeated)).bind GuardDescriptor.decode).isSome =
    true := by decide
example : (TermCode.extract (TermCode.encode repeated)).map GuardDescriptor.recognize =
    some false := by decide

end KFOLTest.GuardDescriptor
