module

public import KFOL.Owner.SynthesisNecessity

/-! Kernel regressions for genuine whole-table acceptance and rejection. -/

@[expose] public section

namespace KFOLTest.OwnerSynthesis

open KFOL.Owner

private def projection : GuardTable (Fin 1) := ⟨0, [(0, ⟨∅, ∅⟩)]⟩
private def guarded : GuardTable (Fin 3) :=
  ⟨0, [(0, ⟨∅, ∅⟩), (1, ⟨{0}, {2}⟩), (2, ⟨{0}, {1}⟩)]⟩
private def unsupported : GuardTable (Fin 3) :=
  ⟨0, [(0, ⟨∅, ∅⟩), (1, ⟨{0, 2}, ∅⟩)]⟩

example : projection.check [0] = true := by decide
example : (projection.synthesize () [0]).isSome = true := by decide
example : guarded.canonicalB = true := by decide
example : guarded.check [0, 1, 2] = true := by decide
example : guarded.check [2, 0, 1] = true := by decide
example : (guarded.synthesize () [0, 1, 2]).isSome = true := by decide
example : unsupported.canonicalB = true := by decide
example : unsupported.check [0, 1, 2] = false := by decide
example : (unsupported.synthesize () [0, 1, 2]).isSome = false := by decide
example : guarded.check [0, 1] = false := by decide

/-- info: 'KFOL.Owner.GuardTable.synthesis_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.GuardTable.synthesis_iff

/-- info: 'KFOL.Owner.GuardTable.run_order_independent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.GuardTable.run_order_independent

end KFOLTest.OwnerSynthesis
