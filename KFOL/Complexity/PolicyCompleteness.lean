module
public import KFOL.Complexity.PolicyReductionMachines
public import KFOL.Complexity.CNFHardness
public import KFOL.Complexity.FiniteSignatureVerifier
@[expose] public section
namespace KFOL.Complexity.PolicyCompleteness
open Turing.MultiTapeTM
open KFOL.Policies KFOL.Complexity.PolicyTermMachines
variable {Role Label : Type} [Fintype Label]

def Theory (D : Label → Set Role) : Set (Policies.Term Label ℕ × Policies.Term Label ℕ) :=
  {equation | ∀ valuation : ℕ → WinnerSet Role, equation.1.eval D valuation = equation.2.eval D valuation}
noncomputable def Language (D : Label → Set Role) : Set (List Bool) :=
  {word | ∃ equation : Policies.Term Label ℕ × Policies.Term Label ℕ,
    FiniteTermCode.encodeEquation (Policies.Symbol Label) equation = word ∧ equation ∈ Theory D}

theorem coNPHard [Fintype Role] (D : Label → Set Role) (three : Fin 3 ↪ Role)
    (code : Role ↪ ℕ) (hne : ¬FamilyEasy D) :
    Cslib.Complexity.coNPHard PolicyReductionMachines.equationEncoding (Theory D) := by
  obtain ⟨plan, hplan⟩ := non_easy_family_nat_cnf_reduction D three code hne
  apply CNFHardness.coNPHard_of_width_three (fun equation => equation ∈ Theory D)
    (PolicyReductionMachines.equationAt code plan) (PolicyReductionMachines.reduction_polyTime code plan)
    ?_ ((.var 0, .var 0) : Policies.Term Label ℕ × Policies.Term Label ℕ) (fun _ => rfl)
  intro formula hw
  rw [PolicyReductionMachines.equationAt_eq code plan formula hw]
  exact hplan formula

theorem mem_coNP [Fintype Role] (D : Label → Set Role) (inhabitant : Role) :
    Theory D ∈ Cslib.Complexity.coNP PolicyReductionMachines.equationEncoding := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton inhabitant⟩
  let : (Equational.language (Policies.Symbol Label)).Structure (WinnerSet Role) := Policies.structureOf D
  exact FiniteSignatureVerifier.holds_mem_coNP (σ := Policies.Symbol Label) (Value := WinnerSet Role) Eq

theorem language_mem_coNP [Fintype Role] (D : Label → Set Role) (inhabitant : Role) :
    Language D ∈ Cslib.Complexity.coNP encBits := by
  classical
  let : Fintype (WinnerSet Role) := Fintype.ofFinite _
  let : Nonempty (WinnerSet Role) := ⟨WinnerSet.singleton inhabitant⟩
  let : (Equational.language (Policies.Symbol Label)).Structure (WinnerSet Role) := Policies.structureOf D
  exact FiniteSignatureVerifier.language_mem_coNP (σ := Policies.Symbol Label) (Value := WinnerSet Role) Eq

theorem coNPComplete [Fintype Role] (D : Label → Set Role) (three : Fin 3 ↪ Role)
    (code : Role ↪ ℕ) (hne : ¬FamilyEasy D) :
    Cslib.Complexity.coNPComplete PolicyReductionMachines.equationEncoding (Theory D) :=
  ⟨mem_coNP D (three 0), coNPHard D three code hne⟩

theorem language_coNPComplete [Fintype Role] (D : Label → Set Role) (three : Fin 3 ↪ Role)
    (code : Role ↪ ℕ) (hne : ¬FamilyEasy D) :
    Cslib.Complexity.coNPComplete encBits (Language D) :=
  ⟨language_mem_coNP D (three 0), CNFHardness.coNPHard_encode _ _ (coNPHard D three code hne)⟩
end KFOL.Complexity.PolicyCompleteness
