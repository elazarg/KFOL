module
public import KFOL.Complexity.FiniteValueWitness
public import KFOL.Complexity.FiniteTermVariables
public import Complexity.Computability.Complexity.Classes.NP
@[expose] public section
namespace KFOL.Complexity.FiniteSignatureVerifier
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
open KFOL.Complexity.FiniteAlgebraVerifier
variable {σ : ℕ → Type} [Fintype (Operation σ)]
variable {Value : Type} [Fintype Value] [Nonempty Value]
variable [(Equational.language σ).Structure Value]
abbrev Tree (σ : ℕ → Type) := Equational.Term σ ℕ
abbrev Equation (σ : ℕ → Type) := Tree σ × Tree σ

noncomputable def node (_ : Context) (operation : Operation σ) (children : List Value) : Value :=
  FirstOrder.Language.Structure.funMap (L := Equational.language σ) operation.2 (fun i => children.getD i.val fallback)

private theorem node_polyTime : ComputableInPolyTime
    (fun p : Context × (Operation σ × List Value) => node p.1 p.2.1 p.2.2)
    (encPair contextEncoding (encPair FiniteTermMachines.operationEncoding (encList valueEncoding))) valueEncoding := by
  let input := encPair contextEncoding
    (encPair (FiniteTermMachines.operationEncoding (σ := σ)) (encList (valueEncoding (Value := Value))))
  have hop : ComputableInPolyTime (fun p : Context × (Operation σ × List Value) => p.2.1)
      input FiniteTermMachines.operationEncoding := by fun_prop
  have hchildren : ComputableInPolyTime (fun p : Context × (Operation σ × List Value) => p.2.2)
      input (encList valueEncoding) := by fun_prop
  apply hop.finite_cases (branch := fun operation p => node p.1 operation p.2.2)
  rintro ⟨n, function⟩
  have hargs : ComputableInPolyTime
      (fun p : Context × (Operation σ × List Value) => fun i : Fin n => p.2.2.getD i.val fallback)
      input (encPi valueEncoding) := by
    apply ComputableInPolyTime.pi
    intro i
    exact (listGetD (encA := valueEncoding) (encL := encList valueEncoding) fallback).comp
      (hchildren.prod (const i.val))
  have hf : ComputableInPolyTime
      (fun args : Fin n → Value => FirstOrder.Language.Structure.funMap (L := Equational.language σ) function args)
      (encPi valueEncoding) valueEncoding := .of_finite _
  exact hf.comp hargs

omit [Fintype (Operation σ)] in
private theorem fold_realize (context : Context) (term : Tree σ) :
    FiniteFoldMachine.fold (lookup (Value := Value)) node context term = term.realize (lookup context) := by
  induction term with
  | var j => rfl
  | @func n function children ih =>
    simp only [FiniteFoldMachine.fold, node, FirstOrder.Language.Term.realize_func]
    congr 1
    funext i
    simp [ih]

private theorem eval_polyTime : ComputableInPolyTime
    (fun p : Context × Tree σ => p.2.realize (lookup p.1 : ℕ → Value))
    (encPair contextEncoding FiniteTermMachines.termEncoding) valueEncoding := by
  have h := FiniteFoldMachine.fold_polyTime (σ := σ) lookup node lookup_polyTime node_polyTime
    (Fintype.card Value) 0 (by
      intro context term
      simpa only [Nat.pow_zero, Nat.mul_one] using value_length_le
        (FiniteFoldMachine.fold lookup node context term)) fallback
  convert h using 1
  funext p
  exact (fold_realize p.1 p.2).symm

noncomputable def verifier (relation : Value → Value → Prop) (input : Equation σ × List Bool) : Bool := by
  classical
  let context : Context := (FiniteTermVariables.equationNames input.1, input.2)
  exact decide (¬relation (input.1.1.realize (lookup context)) (input.1.2.realize (lookup context)))

theorem verifier_polyTime (relation : Value → Value → Prop) : ComputableInPolyTime (verifier (σ := σ) relation)
    (encPair FiniteTermMachines.equationEncoding encBits) encBool := by
  classical
  have he := eval_polyTime (σ := σ) (Value := Value)
  have hnames := (FiniteTermVariables.equationNames_polyTime (σ := σ)).comp
    (fst (FiniteTermMachines.equationEncoding (σ := σ)) encBits)
  have hword := snd (FiniteTermMachines.equationEncoding (σ := σ)) encBits
  have hc := hnames.prod hword
  have hpair := (FiniteTermMachines.arguments_polyTime (σ := σ)).comp
    (fst (FiniteTermMachines.equationEncoding (σ := σ)) encBits)
  have hl := he.comp (hc.prod ((fst _ _).comp hpair))
  have hr := he.comp (hc.prod ((snd _ _).comp hpair))
  have ht : ComputableInPolyTime (fun p : Value × Value => decide (¬relation p.1 p.2))
      (encPair valueEncoding valueEncoding) encBool := .of_finite _
  exact ht.comp (hl.prod hr)

omit [Fintype (Operation σ)] in
private theorem verifier_sound (relation : Value → Value → Prop) (equation : Equation σ)
    (word : List Bool) (h : verifier relation (equation, word) = true) :
    ¬∀ valuation : ℕ → Value, relation (equation.1.realize valuation) (equation.2.realize valuation) := by
  classical
  exact fun hv => (of_decide_eq_true h) (hv _)

omit [Fintype (Operation σ)] in
private theorem verifier_complete (relation : Value → Value → Prop) (equation : Equation σ)
    (valuation : ℕ → Value) (h : ¬relation (equation.1.realize valuation) (equation.2.realize valuation))
    (padding : List Bool) : verifier relation
      (equation, witness (FiniteTermVariables.equationNames equation) valuation ++ padding) = true := by
  classical
  let labels := FiniteTermVariables.equationNames equation
  let context : Context := (labels, witness labels valuation ++ padding)
  have hl := FiniteTermVariables.realize_congr equation.1 (lookup context) valuation
    (fun j hj => lookup_witness labels valuation j (List.mem_append_left _ hj) padding)
  have hr := FiniteTermVariables.realize_congr equation.2 (lookup context) valuation
    (fun j hj => lookup_witness labels valuation j (List.mem_append_right _ hj) padding)
  unfold verifier
  apply decide_eq_true
  change ¬relation (equation.1.realize (lookup context)) (equation.2.realize (lookup context))
  rw [hl, hr]
  exact h

/-- For any fixed finite nonempty algebra and finite signature, the universal
relation theory of actual original tree terms has a machine-level coNP bound.
The relation may be equality or one chosen winner-membership observation. -/
theorem holds_mem_coNP (relation : Value → Value → Prop) :
    {equation : Equation σ | ∀ valuation : ℕ → Value,
      relation (equation.1.realize valuation) (equation.2.realize valuation)} ∈
      Cslib.Complexity.coNP FiniteTermMachines.equationEncoding := by
  classical
  change {equation : Equation σ | ∀ valuation : ℕ → Value,
      relation (equation.1.realize valuation) (equation.2.realize valuation)}ᶜ ∈
    Cslib.Complexity.NP FiniteTermMachines.equationEncoding
  refine ⟨Polynomial.C (Fintype.card Value) * Polynomial.X, verifier relation, verifier_polyTime relation, ?_⟩
  apply Cslib.Complexity.IsVerifier.of_padding
  · intro equation word _ h
    exact verifier_sound relation equation word h
  · intro equation h
    obtain ⟨valuation, hrelation⟩ := not_forall.mp h
    refine ⟨witness (FiniteTermVariables.equationNames equation) valuation, ?_, fun _ =>
      verifier_complete relation equation valuation hrelation _⟩
    simp only [length_witness, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact Nat.mul_le_mul_left _ (FiniteTermVariables.length_equationNames_le equation)
noncomputable def wordVerifier (relation : Value → Value → Prop) (input : List Bool × List Bool) : Bool :=
  (decodeEquation σ input.1).elim true (fun equation => verifier relation (equation, input.2))

theorem wordVerifier_polyTime (relation : Value → Value → Prop) : ComputableInPolyTime
    (wordVerifier (σ := σ) relation) (encPair encBits encBits) encBool := by
  have hd := (FiniteTermMachines.decodeEquation_polyTime (σ := σ)).comp (fst encBits encBits)
  have he := (FiniteTermMachines.equationRecode_polyTime (σ := σ)).comp
    (snd (encPair encBits encBits) (encPair FiniteTermMachines.termEncoding FiniteTermMachines.termEncoding))
  have hw : ComputableInPolyTime (fun p : (List Bool × List Bool) × Equation σ => p.1.2)
      (encPair (encPair encBits encBits) (encPair FiniteTermMachines.termEncoding FiniteTermMachines.termEncoding)) encBits := by fun_prop
  have hb := (verifier_polyTime (σ := σ) relation).comp (he.prod hw)
  exact hd.optionElimWithInput (body := fun (p : List Bool × List Bool) (equation : Equation σ) =>
    verifier relation (equation, p.2)) (const true) hb

/-- The complete original binary language, with malformed outer and inner
words excluded by its independent existential encoding clause, is in coNP. -/
theorem language_mem_coNP (relation : Value → Value → Prop) :
    {word | ∃ equation : Equation σ, encodeEquation σ equation = word ∧
      ∀ valuation : ℕ → Value, relation (equation.1.realize valuation) (equation.2.realize valuation)} ∈
      Cslib.Complexity.coNP encBits := by
  classical
  change {word | ∃ equation : Equation σ, encodeEquation σ equation = word ∧
      ∀ valuation : ℕ → Value, relation (equation.1.realize valuation) (equation.2.realize valuation)}ᶜ ∈
    Cslib.Complexity.NP encBits
  refine ⟨Polynomial.C (Fintype.card Value) * Polynomial.X, wordVerifier (σ := σ) relation, wordVerifier_polyTime (σ := σ) relation, ?_⟩
  apply Cslib.Complexity.IsVerifier.of_padding
  · intro word certificate _ hv
    rintro ⟨equation, hw, he⟩
    have hd : decodeEquation σ word = some equation := by
      rw [← hw]
      exact decodeEquation_encodeEquation equation
    have hc : verifier relation (equation, certificate) = true := by
      simpa only [wordVerifier, hd, Option.elim_some] using hv
    exact verifier_sound relation equation certificate hc he
  · intro word hn
    cases hd : decodeEquation σ word with
    | none =>
      refine ⟨[], ?_, ?_⟩
      · simp
      · intro padding
        simp only [wordVerifier, hd, Option.elim_none]
    | some equation =>
      have hnot : ¬∀ valuation : ℕ → Value,
          relation (equation.1.realize valuation) (equation.2.realize valuation) :=
        fun he => hn ⟨equation, encodeEquation_of_decodeEquation hd, he⟩
      obtain ⟨valuation, hrelation⟩ := not_forall.mp hnot
      refine ⟨witness (FiniteTermVariables.equationNames equation) valuation, ?_, ?_⟩
      · simp only [length_witness, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, encBits_apply]
        have hl := FiniteTermVariables.length_equationNames_le equation
        rw [encodeEquation_of_decodeEquation hd] at hl
        exact Nat.mul_le_mul_left _ hl
      · intro padding
        simp only [wordVerifier, hd, Option.elim_some]
        exact verifier_complete relation equation valuation hrelation (List.replicate padding false)

end KFOL.Complexity.FiniteSignatureVerifier
