module

public import KFOL.Complexity.ResetUnionVariables
public import KFOL.Complexity.FiniteValueWitness
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Native short countervaluation certificates for finite reset/union algebras -/

@[expose] public section

namespace KFOL.Complexity.FiniteAlgebraVerifier

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.ResetUnion

section Finite

variable {Value : Type} [Fintype Value] [Nonempty Value]

/-- Independent algebraic validity for the two supplied binary operations. -/
def Holds (reset union : Value → Value → Value) (equation : Equation) : Prop :=
  ∀ valuation : ℕ → Value,
    ResetUnionEvaluation.fold (fun (v : ℕ → Value) j => v j) reset union valuation equation.1 =
      ResetUnionEvaluation.fold (fun (v : ℕ → Value) j => v j) reset union valuation equation.2

noncomputable def verifier (reset union : Value → Value → Value) (input : Equation × List Bool) : Bool := by
  classical
  let context := (ResetUnionVariables.equationNames input.1, input.2)
  exact decide (ResetUnionEvaluation.fold lookup reset union context input.1.1 ≠
    ResetUnionEvaluation.fold lookup reset union context input.1.2)

@[fun_prop] theorem verifier_polyTime (reset union : Value → Value → Value) :
    ComputableInPolyTime (verifier reset union) (encPair ResetUnionMachines.equationEncoding encBits) encBool := by
  classical
  have hreset : ComputableInPolyTime (fun p : Value × Value => reset p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding := .of_finite _
  have hunion : ComputableInPolyTime (fun p : Value × Value => union p.1 p.2)
      (encPair valueEncoding valueEncoding) valueEncoding := .of_finite _
  have heval := ResetUnionEvaluation.fold_polyTime contextEncoding valueEncoding lookup reset union fallback
    lookup_polyTime hreset hunion (Fintype.card Value) value_length_le
  have hnames := ResetUnionVariables.equationNames_polyTime.comp
    (fst ResetUnionMachines.equationEncoding encBits)
  have hword := snd ResetUnionMachines.equationEncoding encBits
  have hcontext := hnames.prod hword
  have hpair := ResetUnionMachines.arguments_polyTime.comp (fst ResetUnionMachines.equationEncoding encBits)
  have hleft := heval.comp (hcontext.prod ((fst ResetUnionMachines.termEncoding ResetUnionMachines.termEncoding).comp hpair))
  have hright := heval.comp (hcontext.prod ((snd ResetUnionMachines.termEncoding ResetUnionMachines.termEncoding).comp hpair))
  have h := bool_not.comp (decide_eq' hleft hright)
  convert h using 1
  funext input
  by_cases he : ResetUnionEvaluation.fold lookup reset union
      (ResetUnionVariables.equationNames input.1, input.2) input.1.1 =
    ResetUnionEvaluation.fold lookup reset union
      (ResetUnionVariables.equationNames input.1, input.2) input.1.2 <;> simp [verifier, Function.comp_def, he]

private theorem verifier_sound (reset union : Value → Value → Value) (equation : Equation)
    (word : List Bool) (h : verifier reset union (equation, word) = true) : ¬Holds reset union equation := by
  classical
  have hne := of_decide_eq_true h
  intro hv
  apply hne
  change ResetUnionEvaluation.fold lookup reset union (ResetUnionVariables.equationNames equation, word) equation.1 =
    ResetUnionEvaluation.fold lookup reset union (ResetUnionVariables.equationNames equation, word) equation.2
  rw [ResetUnionEvaluation.fold_function lookup reset union _ equation.1,
    ResetUnionEvaluation.fold_function lookup reset union _ equation.2]
  exact hv _

private theorem verifier_complete (reset union : Value → Value → Value) (equation : Equation)
    (valuation : ℕ → Value)
    (hne : ResetUnionEvaluation.fold (fun (v : ℕ → Value) j => v j) reset union valuation equation.1 ≠
      ResetUnionEvaluation.fold (fun (v : ℕ → Value) j => v j) reset union valuation equation.2)
    (padding : List Bool) :
    verifier reset union (equation, witness (ResetUnionVariables.equationNames equation) valuation ++ padding) = true := by
  classical
  let labels := ResetUnionVariables.equationNames equation
  let context : Context := (labels, witness labels valuation ++ padding)
  have hleft := ResetUnionVariables.fold_congr lookup (fun (_ : Context) j => valuation j)
    reset union context equation.1 (fun j hj => lookup_witness labels valuation j
      (List.mem_append_left _ hj) padding)
  have hright := ResetUnionVariables.fold_congr lookup (fun (_ : Context) j => valuation j)
    reset union context equation.2 (fun j hj => lookup_witness labels valuation j
      (List.mem_append_right _ hj) padding)
  unfold verifier
  apply decide_eq_true
  change ResetUnionEvaluation.fold lookup reset union context equation.1 ≠
    ResetUnionEvaluation.fold lookup reset union context equation.2
  rw [hleft, hright]
  rw [ResetUnionEvaluation.fold_function (fun (_ : Context) j => valuation j) reset union context equation.1,
    ResetUnionEvaluation.fold_function (fun (_ : Context) j => valuation j) reset union context equation.2]
  exact hne

/-- Equational validity in any fixed finite nonempty algebra with two binary
operations belongs to the imported machine-level coNP class. The verifier is
uniform in original tree size and uses only linearly many finite-value blocks. -/
theorem holds_mem_coNP (reset union : Value → Value → Value) :
    {equation | Holds reset union equation} ∈ Cslib.Complexity.coNP ResetUnionMachines.equationEncoding := by
  classical
  change {equation | Holds reset union equation}ᶜ ∈ Cslib.Complexity.NP ResetUnionMachines.equationEncoding
  refine ⟨Polynomial.C (Fintype.card Value) * Polynomial.X, verifier reset union, verifier_polyTime reset union, ?_⟩
  apply Cslib.Complexity.IsVerifier.of_padding
  · intro equation word _ h
    exact verifier_sound reset union equation word h
  · intro equation h
    obtain ⟨valuation, hne⟩ := not_forall.mp h
    refine ⟨witness (ResetUnionVariables.equationNames equation) valuation, ?_, fun k =>
      verifier_complete reset union equation valuation hne _⟩
    simp only [length_witness, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact Nat.mul_le_mul_left _ (ResetUnionVariables.length_equationNames_le equation)

end Finite
end KFOL.Complexity.FiniteAlgebraVerifier
