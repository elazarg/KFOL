module

public import KFOL.Core.BichainReadOnce
public import KFOL.Definitions.BichainSwitch
import Mathlib.Tactic.FinCases

/-! # A minimal Boolean-cofactor obstruction beyond the four-variable path -/

@[expose] public section
namespace KFOL.Bichain

private def switchPositive : Fin 5 → Bool := fun j => decide (j = 0 ∨ j = 3 ∨ j = 4)
private def switchNegative : Fin 5 → Bool := fun j => decide (j = 1 ∨ j = 2)
private def switchLower₁ : Fin 5 → Bool := fun j => decide (j = 2)
private def switchUpper₁ : Fin 5 → Bool := fun j => decide (j ≠ 1)
private def switchLower₂ : Fin 5 → Bool := fun j => decide (j = 1)
private def switchUpper₂ : Fin 5 → Bool := fun j => decide (j ≠ 2)

/-- The switch is monotone as a Boolean function. -/
theorem squareSwitch_monotone : Monotone squareSwitch := by decide +kernel

private theorem switch_essential₁ : ∀ j,
    Essential squareSwitch switchLower₁ switchUpper₁ j ↔ j = 3 := by decide +kernel

private theorem switch_essential₂ : ∀ j,
    Essential squareSwitch switchLower₂ switchUpper₂ j ↔ j = 0 := by decide +kernel

/-- The two compatible cubes reduce to different projections; there is no
source that remains essential in both of them. -/
theorem squareSwitch_not_stableSeparatingSource : ¬ StableSeparatingSource squareSwitch := by
  intro h
  obtain ⟨j, _, _, hj⟩ := h switchPositive switchNegative (by decide +kernel) (by decide +kernel)
  have h₁ := hj switchLower₁ switchUpper₁ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have h₂ := hj switchLower₂ switchUpper₂ (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  have hj₁ : j = 3 := (switch_essential₁ j).mp h₁
  have hj₂ : j = 0 := (switch_essential₂ j).mp h₂
  subst j
  contradiction

/-- Canonical essential-source information cannot be represented by a bichain
term, even with observer union. -/
theorem squareSwitch_not_hasCanonicalRealizer : ¬ HasCanonicalRealizer squareSwitch :=
  fun h => squareSwitch_not_stableSeparatingSource h.stableSeparatingSource

/-- All ten displayed cofactor words use only the two original operations. -/
theorem squareSwitchCofactorTerm_isPure : ∀ j bit,
    (squareSwitchCofactorTerm j bit).IsPure := by
  intro j bit
  fin_cases j <;> cases bit <;> trivial

/-- Every one-variable cofactor has a read-once realizer. -/
theorem squareSwitchCofactorTerm_isReadOnce : ∀ j bit,
    (squareSwitchCofactorTerm j bit).IsReadOnce := by
  intro j bit
  fin_cases j <;> cases bit <;>
    simp [squareSwitchCofactorTerm, Term.IsReadOnce, Term.vars]

private theorem squareSwitchCofactorTerm_bool : ∀ j bit (v : Fin 5 → Bool),
    (squareSwitchCofactorTerm j bit).eval (fun i => Value.ofBool (v i)) =
      Value.ofBool (booleanCofactor squareSwitch j bit v) := by decide +kernel

/-- Exact canonical semantics, rather than merely the Boolean truth table,
for all ten one-variable cofactors. -/
theorem squareSwitchCofactorTerm_canonical (j : Fin 5) (bit : Bool) (v : Fin 5 → Value) :
    (squareSwitchCofactorTerm j bit).eval v =
      canonicalExtension (booleanCofactor squareSwitch j bit) v :=
  (squareSwitchCofactorTerm_isReadOnce j bit).canonical _ (squareSwitchCofactorTerm_bool j bit) v

/-- The five-variable switch is nonrealizable although fixing any single
Boolean input yields a pure read-once canonical realizer. -/
theorem squareSwitch_cofactor_obstruction :
    Monotone squareSwitch ∧ ¬ HasCanonicalRealizer squareSwitch ∧
      ∀ j bit, ∃ t : Term (Fin 5), t.IsReadOnce ∧
        ∀ v, t.eval v = canonicalExtension (booleanCofactor squareSwitch j bit) v :=
  ⟨squareSwitch_monotone, squareSwitch_not_hasCanonicalRealizer,
    fun j bit => ⟨squareSwitchCofactorTerm j bit,
      squareSwitchCofactorTerm_isReadOnce j bit, squareSwitchCofactorTerm_canonical j bit⟩⟩

end KFOL.Bichain
