module

public import KFOL.Owner.Basis.TwoSource

@[expose] public section

namespace KFOLTest.OwnerTwoSource

open KFOL.Owner

example : Term.twoSourceGuards (0 : ℕ) 1 2 [] =
    [⟨1, [0], [2, 1]⟩, ⟨2, [0], [2, 1]⟩] := rfl

example : Term.twoSourceGuards (0 : ℕ) 1 1 [(3, 4)] =
    [⟨1, [0, 3, 0], [4, 3, 1, 1]⟩, ⟨1, [0, 3, 0], [4, 3, 1, 1]⟩] := rfl

example {Var : Type} (r a b : Var) (P : List (Var × Var)) (W : Term Unit Var)
    (hzero : KFOL.Equational.Derives FiniteBasis.theory
      (Term.step (Term.pathBody () r P (.var r)) W) W)
    (hcover : Covers (Term.twoSourceGuards r a b P) ((W.withOwner false).guards true)) :
    KFOL.Equational.Derives FiniteBasis.theory
      (Term.step (Term.pathBody () r P (Term.guarded () (.var r) (.var a) (.var b))) W) W :=
  FiniteBasis.two_source_guard_absorption r a b P W hzero hcover

/-- info: 'KFOL.Owner.FiniteBasis.two_source_guard_absorption' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.FiniteBasis.two_source_guard_absorption

/-- info: 'KFOL.Owner.Term.eval_guards_two_sources' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Owner.Term.eval_guards_two_sources

end KFOLTest.OwnerTwoSource
