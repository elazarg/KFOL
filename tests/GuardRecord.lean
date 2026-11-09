module

public import KFOL.Algorithms.GuardRecord

/-! Sparse names, occurrence recovery, exact framing and malformed fields. -/

@[expose] public section

namespace KFOLTest.GuardRecord

open KFOL KFOL.Algorithms

private def sparse : Reset.Term ℕ := Reset.Term.step (.var 100000) (.var 7)

example : SupportIndex.labels sparse = [7, 100000] := by decide
example : (SupportIndex.labels sparse).length = 2 := by decide
example : (SupportIndex.locate (SupportIndex.labels sparse) 100000).map Fin.val = some 1 := by decide
example : SupportIndex.locate (SupportIndex.labels sparse) 42 = none := by decide

-- Extra unused status labels do not affect compression or the subset test.
example : Bitset.encode (SupportIndex.compress (SupportIndex.labels sparse) {100000}) =
    [false, true] := by decide
example : GuardWords.subsetWord
    (Bitset.encode (SupportIndex.compress (SupportIndex.labels sparse) {7}))
    (Bitset.encode (SupportIndex.compress (SupportIndex.labels sparse) {7, 42})) = [true] :=
  by decide

private def records : List (GuardRecord.Record 2) := [(0, ∅), (1, {0})]

-- Compression preserves the raw collector's order and repeated occurrences.
example : (sparse.guardEntries.mapM (SupportIndex.compressEntry (SupportIndex.labels sparse))).map
    (fun rs => rs.map (fun r => (r.1.val, Bitset.encode r.2))) =
      some [(0, [false, false]), (1, [true, false])] := by decide

example : (GuardRecord.encodeList records).length = 24 := by decide
example : GuardRecord.decodeList 2 (GuardRecord.encodeList records) = some records := by decide
example : (LabelDictionary.encode (SupportIndex.labels sparse)).length = 44 := by decide
example : LabelDictionary.decode (LabelDictionary.encode (SupportIndex.labels sparse)) =
    some [7, 100000] := by decide

-- Binary zero has the canonical empty code. A redundant high zero is rejected.
example : GuardRecord.decode 2 (_root_.Complexity.pair [false] [false, false]) = none := by decide
-- An output index outside the declared dictionary is invalid.
example : GuardRecord.decode 2 (_root_.Complexity.pair [true, true] [false, false]) = none := by decide
-- The entire payload must have exactly the dictionary width.
example : GuardRecord.decode 2 (_root_.Complexity.pair [] [false]) = none := by decide
example : GuardRecord.decodeList 2 (GuardRecord.encodeList records ++ [true]) = none := by decide
example : GuardRecord.decodeList 0 [] = some [] := by decide

-- Duplicate labels get one index; duplicate occurrences still have records.
private def repeated : Reset.Term ℕ := Reset.Term.step (Reset.Term.step (.var 7) (.var 7)) (.var 7)

example : SupportIndex.labels repeated = [7] ∧ repeated.guardEntries.length = 3 := by decide

private def alternatives : Reset.Term ℕ := Reset.Term.step
  (Reset.Term.step (Reset.Term.step (.var 3) (.var 1)) (.var 0))
  (Reset.Term.step (Reset.Term.step (.var 3) (.var 2)) (.var 0))

-- Dictionary order comes from deduplication; the root is not necessarily index zero.
example : SupportIndex.labels alternatives = [2, 0, 1, 3] ∧
    (SupportIndex.locate (SupportIndex.labels alternatives) alternatives.root).map Fin.val =
      some 1 := by decide

end KFOLTest.GuardRecord
