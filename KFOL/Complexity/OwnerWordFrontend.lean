module

public import KFOL.Complexity.OwnerTermFrontend
public import KFOL.Complexity.FiniteTermDecoding

/-! # Complete original-word equality for the one-owner reset/H signature -/

@[expose] public section

namespace KFOL.Complexity.OwnerTermFrontend

universe u
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

/-- Decode both original complete trees, run the independently defined raw
guard checker, and reject every malformed outer or inner word. -/
noncomputable def checkWord (word : List Bool) : Bool :=
  ((decodeEquation (Owner.Symbol Unit) word).map (fun equation =>
    Owner.Term.equationB true (Owner.Term.withOwner false equation.1) (Owner.Term.withOwner false equation.2))).getD false

/-- Complete native running time for the actual original binary input format. -/
theorem checkWord_polyTime : ComputableInPolyTime checkWord encBits encBool := by
  have hd := FiniteTermMachines.decodeEquation_polyTime (σ := Owner.Symbol Unit)
  have he : ComputableInPolyTime
      (fun p : List Bool × (Tree × Tree) =>
        Owner.Term.equationB true (p.2.1.withOwner false) (p.2.2.withOwner false))
      (encPair encBits (encPair termEncoding termEncoding)) encBool := equation_polyTime.comp (snd _ _)
  exact (hd.optionMapWithInput (f := fun (_ : List Bool) equation =>
    Owner.Term.equationB true (Owner.Term.withOwner false equation.1) (Owner.Term.withOwner false equation.2)) he).optionGetDWithInput (const false)

@[simp] theorem checkWord_encode (left right : Tree) :
    checkWord (encodeEquation (Owner.Symbol Unit) (left, right)) =
      Owner.Term.equationB true (left.withOwner false) (right.withOwner false) := by
  simp only [checkWord, decodeEquation_encodeEquation, Option.map_some, Option.getD_some]

/-- Full word-language correctness, uniformly in the ambient role type. The
existential encoding clause explicitly excludes every malformed word. -/
theorem checkWord_iff {Role : Type u} [DecidableEq Role] (three : Fin 3 ↪ Role)
    (owner observer : Role) (hne : observer ≠ owner) (word : List Bool) :
    checkWord word = true ↔ ∃ left right : Tree,
      encodeEquation (Owner.Symbol Unit) (left, right) = word ∧
        ∀ valuation : ℕ → WinnerSet Role,
          (left.withOwner owner).eval valuation = (right.withOwner owner).eval valuation := by
  cases hd : decodeEquation (Owner.Symbol Unit) word with
  | none =>
    simp only [checkWord, hd, Option.map_none, Option.getD_none, Bool.false_eq_true, false_iff]
    rintro ⟨left, right, hw, _⟩
    have hp := decodeEquation_encodeEquation (σ := Owner.Symbol Unit) (left, right)
    rw [hw, hd] at hp
    contradiction
  | some equation =>
    simp only [checkWord, hd, Option.map_some, Option.getD_some]
    constructor
    · intro he
      exact ⟨equation.1, equation.2, encodeEquation_of_decodeEquation hd,
        (equation_iff three owner observer hne equation.1 equation.2).mp he⟩
    · rintro ⟨left, right, hw, he⟩
      have hp := decodeEquation_encodeEquation (σ := Owner.Symbol Unit) (left, right)
      rw [hw, hd] at hp
      cases Option.some.inj hp
      exact (equation_iff three owner observer hne left right).mpr he

end KFOL.Complexity.OwnerTermFrontend
