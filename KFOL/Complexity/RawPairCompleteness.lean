module
public import KFOL.Complexity.ResetChoiceMachines
public import KFOL.Complexity.CNFHardness
public import KFOL.Complexity.FiniteSignatureVerifier
@[expose] public section
namespace KFOL.Complexity.RawPairCompleteness
open Turing.MultiTapeTM
open KFOL.Complexity.RawPairMachines

/-- The independent identity theory of a native two-binary-operation signature. -/
def Theory {Role : Type} (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role) : Set (Tree × Tree) :=
  {equation | ∀ valuation : ℕ → WinnerSet Role,
    equation.1.eval first second valuation = equation.2.eval first second valuation}

noncomputable def Language {Role : Type} (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role) : Set (List Bool) :=
  {word | ∃ equation : Tree × Tree, KFOL.FiniteTermCode.encodeEquation KFOL.RawPair.Symbol equation = word ∧
    equation ∈ Theory first second}

theorem mem_coNP {Role : Type} [Fintype Role] (inhabitant : Role)
    (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role) :
    Theory first second ∈ Cslib.Complexity.coNP equationEncoding := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton inhabitant⟩
  let : (Equational.language KFOL.RawPair.Symbol).Structure (WinnerSet Role) := KFOL.RawPair.structureOf first second
  exact FiniteSignatureVerifier.holds_mem_coNP (σ := KFOL.RawPair.Symbol) (Value := WinnerSet Role) Eq

theorem language_mem_coNP {Role : Type} [Fintype Role] (inhabitant : Role)
    (first second : WinnerSet Role → WinnerSet Role → WinnerSet Role) :
    Language first second ∈ Cslib.Complexity.coNP encBits := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton inhabitant⟩
  let : (Equational.language KFOL.RawPair.Symbol).Structure (WinnerSet Role) := KFOL.RawPair.structureOf first second
  exact FiniteSignatureVerifier.language_mem_coNP (σ := KFOL.RawPair.Symbol) (Value := WinnerSet Role) Eq

theorem union_coNPHard {Role : Type} (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard equationEncoding (Theory (WinnerSet.choice a) WinnerSet.union) := by
  apply CNFHardness.coNPHard_of_CNF
    (fun equation : Tree × Tree => equation ∈ Theory (WinnerSet.choice a) WinnerSet.union)
    KFOL.Reductions.RawPair.equation ?_
    (fun formula => KFOL.Reductions.RawPair.union_equation_valid_iff_unsatisfiable a b d hab had hbd.symm formula)
    ((.var 0, .var 0) : Tree × Tree) (fun _ => rfl)
  exact reduction_polyTime

theorem twoOwners_coNPHard {Role : Type} (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard equationEncoding (Theory (WinnerSet.choice a) (WinnerSet.choice b)) := by
  apply CNFHardness.coNPHard_of_CNF
    (fun equation : Tree × Tree => equation ∈ Theory (WinnerSet.choice a) (WinnerSet.choice b))
    KFOL.Reductions.RawPair.twoOwnerEquation ?_
    (fun formula => KFOL.Reductions.RawPair.twoOwners_equation_valid_iff_unsatisfiable a b d hab had hbd.symm formula)
    ((.var 0, .var 0) : Tree × Tree) (fun _ => rfl)
  exact twoOwnerReduction_polyTime

theorem union_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete equationEncoding (Theory (WinnerSet.choice a) WinnerSet.union) :=
  ⟨mem_coNP a _ _, union_coNPHard a b d hab had hbd⟩

theorem twoOwners_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete equationEncoding (Theory (WinnerSet.choice a) (WinnerSet.choice b)) :=
  ⟨mem_coNP a _ _, twoOwners_coNPHard a b d hab had hbd⟩

theorem union_language_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete encBits (Language (WinnerSet.choice a) WinnerSet.union) :=
  ⟨language_mem_coNP a _ _, CNFHardness.coNPHard_encode equationEncoding _ (union_coNPHard a b d hab had hbd)⟩

theorem twoOwners_language_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete encBits (Language (WinnerSet.choice a) (WinnerSet.choice b)) :=
  ⟨language_mem_coNP a _ _, CNFHardness.coNPHard_encode equationEncoding _ (twoOwners_coNPHard a b d hab had hbd)⟩
theorem resetChoice_coNPHard {Role : Type} (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard equationEncoding (Theory WinnerSet.reset (WinnerSet.choice a)) := by
  apply CNFHardness.coNPHard_of_CNF
    (fun equation : Tree × Tree => equation ∈ Theory WinnerSet.reset (WinnerSet.choice a))
    KFOL.Reductions.ResetChoice.equation ?_
    (fun formula => KFOL.Reductions.ResetChoice.equation_valid_iff_unsatisfiable a b d hab had hbd formula)
    ((.var 0, .var 0) : Tree × Tree) (fun _ => rfl)
  exact ResetChoiceMachines.reduction_polyTime

theorem resetChoice_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete equationEncoding (Theory WinnerSet.reset (WinnerSet.choice a)) :=
  ⟨mem_coNP a _ _, resetChoice_coNPHard a b d hab had hbd⟩

theorem resetChoice_language_coNPComplete {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete encBits (Language WinnerSet.reset (WinnerSet.choice a)) :=
  ⟨language_mem_coNP a _ _, CNFHardness.coNPHard_encode equationEncoding _ (resetChoice_coNPHard a b d hab had hbd)⟩

end KFOL.Complexity.RawPairCompleteness
