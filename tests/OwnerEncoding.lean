module

public import KFOL.Owner.GuardEncoding

@[expose] public section

namespace KFOLTest.OwnerEncoding

open KFOL.Owner

private def sparseTree : Term Unit ℕ := Term.guarded () (.var 7) (.var 1000000000) (.var 1000000000)

example : (sparseTree.withOwner false).guards true =
    [⟨7, [], []⟩, ⟨1000000000, [7], [1000000000, 1000000000]⟩,
      ⟨1000000000, [7], [1000000000, 1000000000]⟩] := by decide

example {Role : Type} [DecidableEq Role] (a k : Role) (hne : k ≠ a) :
    (sparseTree.withOwner a).guards k = (sparseTree.withOwner false).guards true :=
  Term.guards_withOwner_outsider sparseTree a k hne

example (weight : ℕ → ℕ) (g : Guard ℕ) :
    ((g.addOutside 1000000000).addOutside 1000000000).payloadWeight weight =
      g.payloadWeight weight + 2 * weight 1000000000 := by
  simp only [Guard.payloadWeight_addOutside]
  omega

/-- info: 'KFOL.Owner.Term.guardAnnotationWeight_le_encode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.Term.guardAnnotationWeight_le_encode

/-- info: 'KFOL.Owner.Term.guards_withOwner_outsider' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.Term.guards_withOwner_outsider

end KFOLTest.OwnerEncoding
