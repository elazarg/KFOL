module

public import KFOL.Algorithms.TermCode

/-! Exact prefix syntax, arbitrary suffixes, malformed trees and real extraction. -/

@[expose] public section

namespace KFOLTest.TermCode

open KFOL KFOL.Algorithms

private def zero : Reset.Term ℕ := .var 0
private def binary : Reset.Term ℕ := Reset.Term.step (.var 0) (.var 1)
private def sparse : Reset.Term ℕ := Reset.Term.step (.var 100000) (.var 7)
private def repeated : Reset.Term ℕ := Reset.Term.step
  (Reset.Term.step (.var 7) (.var 7)) (.var 7)

example : TermCode.encode zero = [false, false, true] := by decide
example : TermCode.encode binary = [true, false, false, true, false, true, true, false, true] :=
  by decide
example : TermCode.decode (TermCode.encode binary) = some binary := by rfl
example : TermCode.parse 2 (TermCode.encode binary) = some (binary, []) := by rfl
example : TermCode.parse 1 (TermCode.encode binary) = none := by decide
example : TermCode.parse 0 (TermCode.encode zero) = none := by decide
example : TermCode.parse 1 (TermCode.encode zero ++ [true, false]) =
    some (zero, [true, false]) := by rfl

-- Complete decoding refuses suffixes even if the first tree is valid.
example : TermCode.decode (TermCode.encode zero ++ [true]) = none := by decide
example : TermCode.decode (TermCode.encode zero ++ TermCode.encode zero) = none := by decide
example : TermCode.decode [] = none := by decide
example : TermCode.decode [true] = none := by decide
example : TermCode.decode (true :: TermCode.encode zero) = none := by decide
-- Missing label delimiter, invalid doubled bit, and noncanonical binary zero.
example : TermCode.decode [false] = none := by decide
example : TermCode.decode [false, true, false] = none := by decide
example : TermCode.decode [false, false, false, false, true] = none := by decide

-- Large numeric values contribute binary label bits, without a value-based clock.
example : (TermCode.encode sparse).length = 47 := by decide
example : TermCode.decode (TermCode.encode sparse) = some sparse := by rfl
example : TermCode.decode (TermCode.encode repeated) = some repeated := by rfl
example : (TermCode.encode repeated).length = 29 := by decide

-- The frontend runs from the original bits and returns a single framed output word.
example : (TermCode.extract (TermCode.encode sparse)).map List.length = some 114 := by decide
example : (TermCode.extract (TermCode.encode sparse)).bind (fun word => do
    let (dict, stream) ← _root_.Complexity.unpair? word
    let labels ← LabelDictionary.decode dict
    let records ← GuardRecord.decodeList labels.length stream
    return (labels, records.map (fun r => (r.1.val, Bitset.encode r.2)))) =
      some ([7, 100000], [(0, [false, false]), (1, [true, false])]) := by decide
example : TermCode.extract [true] = none := by decide

end KFOLTest.TermCode
