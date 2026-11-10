module
public import KFOL.Complexity.FullInputMachines
public import KFOL.Complexity.FullSparseSemantics
public import KFOL.Complexity.FullTermDictionary
public import KFOL.Complexity.FullCorePredicate
public import KFOL.Complexity.CoreExtractionValidation
public import KFOL.Complexity.RawSmallSignature
@[expose] public section
namespace KFOL.Complexity.FullCounterVerifier
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
abbrev RawInput := FullInputMachines.Input
noncomputable abbrev inputEncoding := FullInputMachines.inputEncoding
abbrev valueEncoding := encList encNat

/-- Only the first complete certificate frame is read, so arbitrary trailing
padding cannot change a successfully decoded assignment. -/
def decodeWitness (word : List Bool) : Option (List ℕ) := do
  let (payload,_) ← Words.unpair? word
  Algorithms.LabelDictionary.decode payload

def witnessWord (values : List ℕ) : List Bool := Words.delimit (Algorithms.LabelDictionary.encode values)
@[simp] theorem decodeWitness_witnessWord_append (values : List ℕ) (padding : List Bool) :
    decodeWitness (witnessWord values ++ padding) = some values := by
  simp [decodeWitness,witnessWord,Words.unpair?_delimit_append]

theorem decodeWitness_polyTime : ComputableInPolyTime decodeWitness encBits (encOption valueEncoding) := by
  have hp : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => p.2.1)
      (encPair encBits (encPair encBits encBits)) encBits := by fun_prop
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) (pair : List Bool × List Bool) => Algorithms.LabelDictionary.decode pair.1)
    (const none) (Dictionary.dictionary_decode_polyTime.comp hp)
  convert h using 1
  funext word
  unfold decodeWitness
  cases Words.unpair? word <;> rfl

def setEqB (left right : List ℕ) : Bool :=
  RawSmallSignature.subsetB (left,right) && RawSmallSignature.subsetB (right,left)
theorem setEqB_iff (left right : List ℕ) : setEqB left right = true ↔
    FullSparseEvaluation.asSet left = FullSparseEvaluation.asSet right := by
  simp only [setEqB,Bool.and_eq_true,RawSmallSignature.subsetB_iff]
  constructor
  · rintro ⟨hl,hr⟩
    exact Set.ext (fun role => ⟨hl role,hr role⟩)
  · intro h
    constructor <;> intro role hm
    · change role ∈ FullSparseEvaluation.asSet right
      rw [← h]
      exact hm
    · change role ∈ FullSparseEvaluation.asSet left
      rw [h]
      exact hm

theorem setEqB_polyTime : ComputableInPolyTime (fun p : List ℕ × List ℕ => setEqB p.1 p.2)
    (encPair valueEncoding valueEncoding) encBool :=
  bool_and' RawSmallSignature.subsetB_polyTime
    (RawSmallSignature.subsetB_polyTime.comp ((snd _ _).prod (fst _ _)))

def sourceOk (coreOnly : Bool) (input : RawInput) : Bool :=
  decide (3 ≤ input.1) && valid input.1 input.2.1 && valid input.1 input.2.2 &&
    (if coreOnly then FullCorePredicate.check input.2.1 && FullCorePredicate.check input.2.2 else true)

theorem sourceOk_polyTime (coreOnly : Bool) : ComputableInPolyTime (sourceOk coreOnly) inputEncoding encBool := by
  have hK := fst encNat FullInputMachines.pairEncoding
  have hl : ComputableInPolyTime (fun p : RawInput => p.2.1) inputEncoding FullTermMachines.termEncoding := by fun_prop
  have hr : ComputableInPolyTime (fun p : RawInput => p.2.2) inputEncoding FullTermMachines.termEncoding := by fun_prop
  have hscope := binary_le.comp ((const 3).prod hK)
  have hleft := CoreExtraction.valid_polyTime.comp (hK.prod hl)
  have hright := CoreExtraction.valid_polyTime.comp (hK.prod hr)
  have hcore := bool_and' (FullCorePredicate.check_polyTime.comp hl) (FullCorePredicate.check_polyTime.comp hr)
  have ht : ComputableInPolyTime (fun p : RawInput =>
      if coreOnly then FullCorePredicate.check p.2.1 && FullCorePredicate.check p.2.2 else true) inputEncoding encBool := by
    cases coreOnly
    · exact const true
    · exact hcore
  exact bool_and' (bool_and' (bool_and' hscope hleft) hright) ht

def dictionary (input : RawInput) : List ℕ := FullTermSize.labels input.2.1 ++ FullTermSize.labels input.2.2

def failure (input : RawInput) (values : List ℕ) : Bool :=
  let context : FullSparseEvaluation.Context := (dictionary input,values)
  !setEqB (FullSparseEvaluation.evaluate context input.2.1) (FullSparseEvaluation.evaluate context input.2.2)

theorem failure_polyTime : ComputableInPolyTime (fun p : RawInput × List ℕ => failure p.1 p.2)
    (encPair inputEncoding valueEncoding) encBool := by
  let input := encPair inputEncoding valueEncoding
  have hl : ComputableInPolyTime (fun p : RawInput × List ℕ => p.1.2.1) input FullTermMachines.termEncoding := by fun_prop
  have hr : ComputableInPolyTime (fun p : RawInput × List ℕ => p.1.2.2) input FullTermMachines.termEncoding := by fun_prop
  have hd := listAppend' (FullTermSize.labels_polyTime.comp hl) (FullTermSize.labels_polyTime.comp hr)
  have hc := hd.prod (snd inputEncoding valueEncoding)
  have hleft := FullSparseEvaluation.evaluate_polyTime.comp (hc.prod hl)
  have hright := FullSparseEvaluation.evaluate_polyTime.comp (hc.prod hr)
  exact bool_not.comp (setEqB_polyTime.comp (hleft.prod hright))

def decodedVerifier (coreOnly : Bool) (input : RawInput × List Bool) : Bool :=
  if sourceOk coreOnly input.1 then
    (decodeWitness input.2).elim false (fun values =>
      if values.all (fun role => decide (role < input.1.1)) then failure input.1 values else false)
  else true

theorem decodedVerifier_polyTime (coreOnly : Bool) : ComputableInPolyTime (decodedVerifier coreOnly)
    (encPair inputEncoding encBits) encBool := by
  let input := encPair inputEncoding encBits
  let callback := encPair input valueEncoding
  have hsource := (sourceOk_polyTime coreOnly).comp (fst inputEncoding encBits)
  have hdecode := decodeWitness_polyTime.comp (snd inputEncoding encBits)
  have hvalues := snd input valueEncoding
  have hK : ComputableInPolyTime (fun p : (RawInput × List Bool) × List ℕ => p.1.1.1) callback encNat := by fun_prop
  have hK' := hK.comp (fst callback encNat)
  have hall := allWithInput (test := fun (p : (RawInput × List Bool) × List ℕ) role => decide (role < p.1.1.1)) hvalues
    (binary_lt.comp ((snd callback encNat).prod hK'))
  have hraw : ComputableInPolyTime (fun p : (RawInput × List Bool) × List ℕ => p.1.1) callback inputEncoding := by fun_prop
  have hf := failure_polyTime.comp (hraw.prod hvalues)
  have hbody := hall.ite hf (const false)
  have hcheck := hdecode.optionElimWithInput
    (body := fun (p : RawInput × List Bool) values => if values.all (fun role => decide (role < p.1.1)) then failure p.1 values else false)
    (const false) hbody
  exact hsource.ite hcheck (const true)

def verifier (coreOnly : Bool) (input : List Bool × List Bool) : Bool :=
  (FullInputMachines.decodeInput input.1).elim true (fun equation => decodedVerifier coreOnly (equation,input.2))

theorem verifier_polyTime (coreOnly : Bool) : ComputableInPolyTime (verifier coreOnly)
    (encPair encBits encBits) encBool := by
  let input := encPair encBits encBits
  have hd := FullInputMachines.decodeInput_polyTime.comp (fst encBits encBits)
  have hraw := snd input inputEncoding
  have hw : ComputableInPolyTime (fun p : (List Bool × List Bool) × RawInput => p.1.2)
      (encPair input inputEncoding) encBits := by fun_prop
  exact hd.optionElimWithInput (body := fun (p : List Bool × List Bool) equation => decodedVerifier coreOnly (equation,p.2))
    (const true) ((decodedVerifier_polyTime coreOnly).comp (hraw.prod hw))
end KFOL.Complexity.FullCounterVerifier
