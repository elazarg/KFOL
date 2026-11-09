import KFOL.Complexity.NormalizeMachine
import KFOL.Complexity.RecognitionMachine

/-! Regression cases for the complete binary descriptor machines. These
exercise sparse binary names, duplicates, domination and failed construction. -/

set_option maxRecDepth 4096

open KFOL.Algorithms

private def path : GuardDescriptor :=
  ⟨[100000, 7], by decide, [(1, ∅), (0, {1})]⟩

example : GuardDescriptor.recognize path.encode = true := by decide

example : GuardDescriptor.normalizeWord path.encode = some path.encode := by decide

private def repeated : GuardDescriptor :=
  ⟨[100000, 7], by decide, [(1, ∅), (0, {1}), (0, {1})]⟩

example : GuardDescriptor.recognize repeated.encode = true := by decide

example : GuardDescriptor.normalizeWord repeated.encode = some repeated.encode := by decide

private def empty : GuardDescriptor := ⟨[], by decide, []⟩

example : (GuardDescriptor.decode empty.encode).isSome = true := by decide

example : GuardDescriptor.recognize empty.encode = false := by decide

private def dominated : GuardDescriptor :=
  ⟨[2, 5, 11], by decide, [(0, ∅), (1, {0}), (1, {0, 2}), (2, {0})]⟩

example : GuardDescriptor.recognize dominated.encode = false := by decide

example : GuardDescriptor.recognize dominated.normalize.encode = true := by decide

example : GuardDescriptor.normalizeWord dominated.encode = some dominated.normalize.encode := by decide

private def cyclic : GuardDescriptor :=
  ⟨[2, 5, 11], by decide, [(0, ∅), (1, {2}), (2, {1})]⟩

example : GuardDescriptor.recognize cyclic.encode = false := by decide

private def selfDependent : GuardDescriptor :=
  ⟨[2, 5], by decide, [(0, ∅), (1, {1})]⟩

example : GuardDescriptor.recognize selfDependent.encode = false := by decide

private def twoRoots : GuardDescriptor :=
  ⟨[2, 5], by decide, [(0, ∅), (1, ∅)]⟩

example : GuardDescriptor.recognize twoRoots.encode = false := by decide

example : GuardDescriptor.recognize [true] = false := by decide

example : GuardDescriptor.normalizeWord [true] = none := by decide
