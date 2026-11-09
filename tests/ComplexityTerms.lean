import KFOL.Complexity.ResetEquality

/-! Prefix-tree boundary regressions. Repeated variables remain separate
syntax occurrences, and sparse names keep their canonical binary spelling. -/

set_option maxRecDepth 4096

open KFOL KFOL.Algorithms

private def repeated : Reset.Term ℕ :=
  Reset.Term.step (.var 100000) (Reset.Term.step (.var 7) (.var 100000))

example : (TermCode.decode (TermCode.encode repeated)).map Reset.Term.leafCount = some 3 := by decide

example : TermCode.decode (TermCode.encode repeated ++ [false]) = none := by decide

example : TermCode.decode [] = none := by decide

example : TermCode.decode [true, false, false, true] = none := by decide

example : TermCode.decode [false, false, false, false, true] = none := by decide

example : (TermCode.decode [false, false, true]).map Reset.Term.root = some 0 := by decide

example : (TermCode.decode [true, false, false, true, false, false, true]).map Reset.Term.size = some 3 := by decide


private def repeatedDescriptor : GuardDescriptor :=
  ⟨[7, 100000], by decide, [(1, ∅), (0, {1}), (1, {1})]⟩

example : TermCode.extract (TermCode.encode repeated) = some repeatedDescriptor.encode := by decide

example : TermCode.extract [false, false, false, false, true] = none := by decide

private def x : Reset.Term ℕ := .var 100000
private def y : Reset.Term ℕ := .var 7
private def z : Reset.Term ℕ := .var 42

private def equation (s t : Reset.Term ℕ) : List Bool :=
  Words.pair (TermCode.encode s) (TermCode.encode t)

-- Duplicate minimal records and syntax order do not affect canonical tables.
example : ResetEquation.checkWord (equation (Reset.Term.step (Reset.Term.step x y) y)
    (Reset.Term.step x y)) = true := by decide

example : ResetEquation.checkWord (equation (Reset.Term.step (Reset.Term.step x y) x)
    (Reset.Term.step y x)) = true := by decide

example : ResetEquation.checkWord (equation (Reset.Term.step (Reset.Term.step x y) z)
    (Reset.Term.step x (Reset.Term.step y z))) = false := by decide

example : ResetEquation.checkWord (Words.pair (TermCode.encode x ++ [false]) (TermCode.encode x)) = false := by decide

example : ResetEquation.checkWord (Words.pair [] []) = false := by decide
