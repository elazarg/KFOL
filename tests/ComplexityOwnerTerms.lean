module

public import KFOL.Complexity.OwnerWordFrontend

/-! Original one-owner trees, sparse names, ternary guards and strict word rejection. -/

@[expose] public section

namespace KFOLTest.ComplexityOwnerTerms

open KFOL KFOL.Complexity
open Turing.MultiTapeTM

private def sparse : OwnerTermFrontend.Tree :=
  Owner.Term.guarded () (.var 0) (.var (2^30)) (.var 2)

example : OwnerTermFrontend.checkWord [] = false := rfl
example : OwnerTermFrontend.checkWord [true, false] = false := rfl

example : OwnerTermFrontend.checkWord
    (FiniteTermCode.encodeEquation (Owner.Symbol Unit) (sparse, sparse)) = true := by
  rw [OwnerTermFrontend.checkWord_encode]
  decide

example : OwnerTermFrontend.checkWord
    (FiniteTermCode.encodeEquation (Owner.Symbol Unit)
      (Owner.Term.guarded () (.var 0) (.var 1) (.var 2), .var 0)) = false := by
  rw [OwnerTermFrontend.checkWord_encode]
  decide

example : (Owner.Term.withOwner false sparse).guards true =
    [⟨0, [], []⟩, ⟨2^30, [0], [2, 2^30]⟩, ⟨2, [0], [2, 2^30]⟩] := rfl

example : ComputableInPolyTime OwnerTermFrontend.checkWord encBits encBool :=
  OwnerTermFrontend.checkWord_polyTime

example {Role : Type} [DecidableEq Role] (three : Fin 3 ↪ Role)
    (owner observer : Role) (hne : observer ≠ owner) (word : List Bool) :
    OwnerTermFrontend.checkWord word = true ↔ ∃ left right : OwnerTermFrontend.Tree,
      FiniteTermCode.encodeEquation (Owner.Symbol Unit) (left, right) = word ∧
        ∀ valuation : ℕ → WinnerSet Role,
          (left.withOwner owner).eval valuation = (right.withOwner owner).eval valuation :=
  OwnerTermFrontend.checkWord_iff three owner observer hne word

end KFOLTest.ComplexityOwnerTerms
