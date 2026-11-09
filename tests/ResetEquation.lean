module

public import KFOL.Algorithms.ResetEquation

/-! Normalized raw extraction, dictionary alignment and the complete equation input. -/

@[expose] public section

namespace KFOLTest.ResetEquation

open KFOL KFOL.Algorithms

set_option maxRecDepth 4096

private def raw : GuardDescriptor := ⟨[7, 42, 100000], by decide,
  [(0, {1, 2}), (1, ∅), (0, {1}), (0, {1}), (1, {2})]⟩

-- Minimal duplicates retain order, while both kinds of dominated guards disappear.
example : raw.normalize.records.map (fun r => (r.1.val, Bitset.encode r.2)) =
    [(1, [false, false, false]), (0, [false, true, false]), (0, [false, true, false])] := by decide
example : raw.check = false ∧ raw.normalize.check = true := by decide
example : (GuardDescriptor.encode raw).length = 186 ∧
    (GuardDescriptor.encode raw.normalize).length = 158 := by decide
example : GuardDescriptor.encode raw.normalize.normalize = GuardDescriptor.encode raw.normalize := by decide
example : GuardDescriptor.normalizeWord (GuardDescriptor.encode raw) =
    some (GuardDescriptor.encode raw.normalize) := by decide
example : GuardDescriptor.normalizeWord [true] = none := by decide

private def repeated : Reset.Term ℕ := Reset.Term.step
  (Reset.Term.step (.var 7) (.var 7)) (.var 7)

-- The previously rejected raw extraction now becomes a recognized canonical table.
example : ((TermCode.extract (TermCode.encode repeated)).bind GuardDescriptor.normalizeWord).map
    List.length = some 26 := by decide
example : ((TermCode.extract (TermCode.encode repeated)).bind GuardDescriptor.normalizeWord).map
    GuardDescriptor.recognize = some true := by decide

private def x : Reset.Term ℕ := .var 100000
private def y : Reset.Term ℕ := .var 7
private def z : Reset.Term ℕ := .var 42
private def leftComm : Reset.Term ℕ := Reset.Term.step x (Reset.Term.step y z)
private def rightComm : Reset.Term ℕ := Reset.Term.step y (Reset.Term.step x z)

-- Independent dictionaries can order the same labels differently.
example : SupportIndex.labels leftComm ≠ SupportIndex.labels rightComm := by decide
example : (ResetEquation.labels leftComm rightComm).length = 3 := by decide
example : ResetEquation.check leftComm rightComm = true := by decide
example : ResetEquation.check repeated (.var 7) = true := by decide
example : ResetEquation.check x y = false := by decide
example : ResetEquation.check (Reset.Term.step (Reset.Term.step x y) z) leftComm = false := by decide

-- A one-variable raw record stream alone cannot identify the original variable.
example : ((TermCode.extract (TermCode.encode x)).bind _root_.KFOL.Words.unpair?).map Prod.snd =
    ((TermCode.extract (TermCode.encode y)).bind _root_.KFOL.Words.unpair?).map Prod.snd := by decide

example : ResetEquation.checkWord (_root_.KFOL.Words.pair
    (TermCode.encode leftComm) (TermCode.encode rightComm)) = true := by decide
example : ResetEquation.checkWord (_root_.KFOL.Words.pair
    (TermCode.encode x) (TermCode.encode y)) = false := by decide
example : ResetEquation.checkWord [] = false := by decide
example : ResetEquation.checkWord [true, false] = false := by decide
example : ResetEquation.checkWord (_root_.KFOL.Words.pair [] (TermCode.encode x)) = false := by decide
example : ResetEquation.checkWord (_root_.KFOL.Words.pair (TermCode.encode x) []) = false := by decide
example : ResetEquation.checkWord (_root_.KFOL.Words.pair
    (TermCode.encode x) (TermCode.encode x) ++ [true]) = false := by decide

end KFOLTest.ResetEquation
