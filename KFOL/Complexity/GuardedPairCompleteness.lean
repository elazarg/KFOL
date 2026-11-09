module
public import KFOL.Complexity.GuardedPairHardness
public import KFOL.Complexity.FiniteSignatureVerifier
@[expose] public section
namespace KFOL.Complexity.GuardedPairCompleteness
open Turing.MultiTapeTM
open KFOL.Complexity.GuardedPairMachines

theorem validity_mem_coNP {Role : Type} [Fintype Role] (a b : Role) :
    {equation : Tree × Tree | ∀ valuation : ℕ → WinnerSet Role,
      equation.1.eval a b valuation = equation.2.eval a b valuation} ∈
      Cslib.Complexity.coNP equationEncoding := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton a⟩
  let : (Equational.language KFOL.GuardedPair.Symbol).Structure (WinnerSet Role) := KFOL.GuardedPair.structureOf a b
  exact FiniteSignatureVerifier.holds_mem_coNP (σ := KFOL.GuardedPair.Symbol) (Value := WinnerSet Role) Eq

theorem observation_mem_coNP {Role : Type} [Fintype Role] (a b d : Role) :
    {equation : Tree × Tree | ∀ valuation : ℕ → WinnerSet Role,
      d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} ∈
      Cslib.Complexity.coNP equationEncoding := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton a⟩
  let : (Equational.language KFOL.GuardedPair.Symbol).Structure (WinnerSet Role) := KFOL.GuardedPair.structureOf a b
  exact FiniteSignatureVerifier.holds_mem_coNP (σ := KFOL.GuardedPair.Symbol) (Value := WinnerSet Role)
    (fun x y => d ∈ x.val ↔ d ∈ y.val)

theorem language_mem_coNP {Role : Type} [Fintype Role] (a b : Role) :
    {word | ∃ equation : Tree × Tree,
      KFOL.FiniteTermCode.encodeEquation KFOL.GuardedPair.Symbol equation = word ∧
        ∀ valuation : ℕ → WinnerSet Role, equation.1.eval a b valuation = equation.2.eval a b valuation} ∈
      Cslib.Complexity.coNP encBits := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton a⟩
  let : (Equational.language KFOL.GuardedPair.Symbol).Structure (WinnerSet Role) := KFOL.GuardedPair.structureOf a b
  exact FiniteSignatureVerifier.language_mem_coNP (σ := KFOL.GuardedPair.Symbol) (Value := WinnerSet Role) Eq

theorem observation_language_mem_coNP {Role : Type} [Fintype Role] (a b d : Role) :
    {word | ∃ equation : Tree × Tree,
      KFOL.FiniteTermCode.encodeEquation KFOL.GuardedPair.Symbol equation = word ∧
        ∀ valuation : ℕ → WinnerSet Role,
          d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} ∈
      Cslib.Complexity.coNP encBits := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton a⟩
  let : (Equational.language KFOL.GuardedPair.Symbol).Structure (WinnerSet Role) := KFOL.GuardedPair.structureOf a b
  exact FiniteSignatureVerifier.language_mem_coNP (σ := KFOL.GuardedPair.Symbol) (Value := WinnerSet Role)
    (fun x y => d ∈ x.val ↔ d ∈ y.val)

theorem coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete equationEncoding
      {equation : Tree × Tree | ∀ valuation : ℕ → WinnerSet Role,
        equation.1.eval a b valuation = equation.2.eval a b valuation} :=
  ⟨validity_mem_coNP a b, GuardedPairHardness.coNPHard a b d hab had hbd⟩

theorem language_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete encBits
      {word | ∃ equation : Tree × Tree,
        KFOL.FiniteTermCode.encodeEquation KFOL.GuardedPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role, equation.1.eval a b valuation = equation.2.eval a b valuation} :=
  ⟨language_mem_coNP a b, GuardedPairHardness.language_coNPHard a b d hab had hbd⟩

theorem observation_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete equationEncoding
      {equation : Tree × Tree | ∀ valuation : ℕ → WinnerSet Role,
        d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} :=
  ⟨observation_mem_coNP a b d, GuardedPairHardness.observation_coNPHard a b d hab had hbd⟩

theorem observation_language_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete encBits
      {word | ∃ equation : Tree × Tree,
        KFOL.FiniteTermCode.encodeEquation KFOL.GuardedPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} :=
  ⟨observation_language_mem_coNP a b d, GuardedPairHardness.observation_language_coNPHard a b d hab had hbd⟩
end KFOL.Complexity.GuardedPairCompleteness
