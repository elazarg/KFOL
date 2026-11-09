module

public import KFOL.Complexity.ResetUnionVariables
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Native short countervaluation certificates for finite reset/union algebras -/

@[expose] public section

namespace KFOL.Complexity.FiniteAlgebraVerifier

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.ResetUnion

section Finite

variable {Value : Type} [Fintype Value] [Nonempty Value]

noncomputable def numbering : Value ≃ Fin (Fintype.card Value) := Fintype.equivFin Value

noncomputable def index (value : Value) : ℕ := (numbering value).val

noncomputable def valueEncoding : Value ↪ List Bool :=
  ⟨fun value => encUnary (index value), fun _a _b he =>
    numbering.injective (Fin.ext (encUnary.injective he))⟩

noncomputable def values : List Value := (List.finRange (Fintype.card Value)).map numbering.symm

noncomputable def fallback : Value := Classical.choice inferInstance

omit [Nonempty Value] in
private theorem index_lt (value : Value) : index value < Fintype.card Value := (numbering value).isLt

omit [Nonempty Value] in
private theorem index_injective : Function.Injective (index (Value := Value)) := by
  intro a b he
  exact numbering.injective (Fin.ext he)

omit [Nonempty Value] in
private theorem mem_values (value : Value) : value ∈ values := by
  exact List.mem_map.mpr ⟨numbering value, by simp, (numbering.symm_apply_apply value)⟩

/-- A finite-value block is decoded by its first indicated value. Every bit
word supplies a genuine algebra value, including malformed/short blocks. -/
noncomputable def decodeValue (word : List Bool) : Value :=
  (values.find? (fun value => word.getD (index value) false)).getD fallback

private theorem decodeValue_polyTime : ComputableInPolyTime (decodeValue (Value := Value)) encBits valueEncoding := by
  classical
  have hi : ComputableInPolyTime (index (Value := Value)) valueEncoding encUnary := .of_finite _
  have hread := bitsGetDWithInput (fst encBits valueEncoding) (hi.comp (snd encBits valueEncoding)) false
  have hfind := findWithInput (test := fun (word : List Bool) value => word.getD (index value) false)
    (const values) hread
  exact hfind.optionGetDWithInput (const fallback)

abbrev Context := List ℕ × List Bool
abbrev contextEncoding := encPair (encList encNat) encBits

/-- Lookup uses the first occurrence position, scaled by a fixed finite-value
block width. The numeric variable name is compared as binary input data. -/
noncomputable def lookup (context : Context) (j : ℕ) : Value :=
  decodeValue (context.2.drop (Fintype.card Value * context.1.idxOf j))

private theorem lookup_polyTime : ComputableInPolyTime
    (fun p : Context × ℕ => (lookup p.1 p.2 : Value)) (encPair contextEncoding encNat) valueEncoding := by
  have hlabels : ComputableInPolyTime (fun p : Context × ℕ => p.1.1)
      (encPair contextEncoding encNat) (encList encNat) := by fun_prop
  have hword : ComputableInPolyTime (fun p : Context × ℕ => p.1.2)
      (encPair contextEncoding encNat) encBits := by fun_prop
  have hj := snd contextEncoding encNat
  have hindex := idxOfWithInput hlabels hj
  have hoffset := unary_mul' (const (Fintype.card Value)) hindex
  exact decodeValue_polyTime.comp (bitsDropWithInput hword hoffset)

/-- A fixed-width one-hot block for every listed occurrence. This is only a
mathematical existence witness; the verifier decodes arbitrary supplied bits. -/
noncomputable def witness (labels : List ℕ) (valuation : ℕ → Value) : List Bool :=
  List.ofFn (fun i : Fin (Fintype.card Value * labels.length) =>
    decide (index (valuation (labels.getD (i.val / Fintype.card Value) 0)) = i.val % Fintype.card Value))

omit [Nonempty Value] in
@[simp] theorem length_witness (labels : List ℕ) (valuation : ℕ → Value) :
    (witness labels valuation).length = Fintype.card Value * labels.length := by simp [witness]

private theorem getD_witness (labels : List ℕ) (valuation : ℕ → Value) (j : ℕ) (hj : j ∈ labels)
    (padding : List Bool) (r : Fin (Fintype.card Value)) :
    (witness labels valuation ++ padding).getD (Fintype.card Value * labels.idxOf j + r.val) false =
      decide (index (valuation j) = r.val) := by
  have hm : 0 < Fintype.card Value := Fintype.card_pos
  have hi := List.idxOf_lt_length_iff.mpr hj
  have hlt : Fintype.card Value * labels.idxOf j + r.val < (witness labels valuation).length := by
    rw [length_witness]
    nlinarith [r.isLt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
  simp only [witness, List.getElem_ofFn]
  have hd : (Fintype.card Value * labels.idxOf j + r.val) / Fintype.card Value = labels.idxOf j := by
    rw [Nat.mul_add_div hm, Nat.div_eq_of_lt r.isLt, Nat.add_zero]
  have hr : (Fintype.card Value * labels.idxOf j + r.val) % Fintype.card Value = r.val := by
    rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  rw [hd, hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem_idxOf hi]
  rfl

private theorem find_unique {A : Type} (list : List A) (predicate : A → Bool) (value : A)
    (hv : value ∈ list) (hp : predicate value = true)
    (hunique : ∀ other ∈ list, predicate other = true → other = value) :
    list.find? predicate = some value := by
  cases hfind : list.find? predicate with
  | none =>
    have hnone := List.find?_eq_none.mp hfind
    exact False.elim (hnone value hv hp)
  | some other =>
    have he := hunique other (List.mem_of_find?_eq_some hfind) (List.find?_some hfind)
    rw [he]

/-- All supplied padding is ignored at the positions needed by the instance. -/
theorem lookup_witness (labels : List ℕ) (valuation : ℕ → Value) (j : ℕ) (hj : j ∈ labels)
    (padding : List Bool) : lookup (labels, witness labels valuation ++ padding) j = valuation j := by
  classical
  unfold lookup decodeValue
  have hread (value : Value) :
      ((witness labels valuation ++ padding).drop (Fintype.card Value * labels.idxOf j)).getD (index value) false =
        decide (valuation j = value) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop]
    have h := getD_witness labels valuation j hj padding (numbering value)
    simp only [List.getD_eq_getElem?_getD] at h
    change (witness labels valuation ++ padding)[Fintype.card Value * labels.idxOf j + index value]?.getD false =
      decide (index (valuation j) = index value) at h
    rw [h]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using index_injective.eq_iff
  have hfind :
      values.find? (fun value =>
        ((witness labels valuation ++ padding).drop (Fintype.card Value * labels.idxOf j)).getD (index value) false) =
        some (valuation j) := by
    apply find_unique _ _ _ (mem_values _) (by rw [hread]; simp)
    intro other _ ho
    rw [hread, decide_eq_true_eq] at ho
    exact ho.symm
  rw [hfind]
  rfl


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

omit [Nonempty Value] in
private theorem value_length_le (value : Value) :
    (valueEncoding value).length ≤ Fintype.card Value := by
  change (encUnary (index value)).length ≤ Fintype.card Value
  simpa using (index_lt value).le

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
