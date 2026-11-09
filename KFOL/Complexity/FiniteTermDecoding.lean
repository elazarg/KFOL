module

public import KFOL.Complexity.FiniteFoldRuntime
public import KFOL.Complexity.OptionTraversal

/-! # Complete original-word decoding for a fixed finite signature

The cached-AST evaluator supplies a candidate. Re-encoding checks that candidate
against the whole input, which connects accepted output to the independent pure
prefix decoder and rejects every malformed or trailing word.
-/

@[expose] public section

namespace KFOL.Complexity.FiniteTermMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

variable {σ : ℕ → Type} [Fintype (Operation σ)]

private def leaf (_ : Unit) (_ : ℕ) : Unit := ()
private def node (_ : Unit) (_ : Operation σ) (_ : List Unit) : Unit := ()

private noncomputable def candidate (word : List Bool) : Option (Equational.Term σ ℕ) :=
  (FiniteFoldMachine.result (FiniteFoldMachine.evaluateState leaf node ((), word))).map Prod.fst

private theorem candidate_polyTime : ComputableInPolyTime (@candidate σ _) encBits (encOption termEncoding) := by
  have he := FiniteFoldMachine.evaluateState_polyTime (contextEncoding := encUnit) (valueEncoding := encUnit)
    leaf (node (σ := σ)) (const ()) (const ()) 0 0 (by intros; exact le_rfl)
  have hp : ComputableInPolyTime (fun word : List Bool => ((), word)) encBits (encPair encUnit encBits) :=
    (const ()).prod id'
  have hr := FiniteFoldMachine.result_polyTime.comp (he.comp hp)
  have hf : ComputableInPolyTime
      (fun p : List Bool × FiniteFoldMachine.Cached σ Unit => p.2.1)
      (encPair encBits (FiniteFoldMachine.cachedEncoding encUnit)) termEncoding := by fun_prop
  exact hr.optionMapWithInput (f := fun (_ : List Bool) cache => cache.1) hf

private theorem candidate_encode (term : Equational.Term σ ℕ) : candidate (encode σ term) = some term := by
  simp only [candidate, FiniteFoldMachine.evaluateState_encode, FiniteFoldMachine.result,
    Option.elim_some, List.isEmpty_nil, Bool.true_and, ite_true, Option.map_some,
    FiniteFoldMachine.sourceCache]

private noncomputable def checkedDecode (word : List Bool) : Option (Equational.Term σ ℕ) :=
  (candidate word).elim none (fun term => if encode σ term = word then some term else none)

private theorem checkedDecode_polyTime : ComputableInPolyTime (@checkedDecode σ _) encBits (encOption termEncoding) := by
  have hterm := snd encBits (termEncoding (σ := σ))
  have hword := fst encBits (termEncoding (σ := σ))
  have heq := decide_eq' (encode_polyTime.comp hterm) hword
  have hbody := heq.ite ((optionSome termEncoding).comp hterm) (const none)
  have hb : ComputableInPolyTime
      (fun p : List Bool × Equational.Term σ ℕ => if encode σ p.2 = p.1 then some p.2 else none)
      (encPair encBits termEncoding) (encOption termEncoding) := by
    convert hbody using 1
    funext p
    simp only [Function.comp_def, decide_eq_true_eq]
  exact (candidate_polyTime (σ := σ)).optionElimWithInput (body := fun word term =>
    if encode σ term = word then some term else none) (const none) hb

private theorem checkedDecode_eq (word : List Bool) : checkedDecode word = decode σ word := by
  cases hd : decode σ word with
  | none =>
    cases hc : candidate (σ := σ) word with
    | none => simp only [checkedDecode, hc, Option.elim_none]
    | some term =>
      have hn : encode σ term ≠ word := by
        intro he
        have hp := decode_encode term
        rw [he, hd] at hp
        contradiction
      simp only [checkedDecode, hc, Option.elim_some, hn, ite_false]
  | some term =>
    have he := encode_of_decode hd
    rw [← he]
    simp only [checkedDecode, candidate_encode, Option.elim_some, ite_true]

/-- The actual independent original decoder, including malformed-word rejection,
is polynomial-time for each fixed finite operation alphabet. -/
theorem decode_polyTime : ComputableInPolyTime (decode σ) encBits (encOption termEncoding) := by
  convert (checkedDecode_polyTime (σ := σ)) using 1
  funext word
  exact (checkedDecode_eq word).symm

noncomputable def equationEncoding : (Equational.Term σ ℕ × Equational.Term σ ℕ) ↪ List Bool :=
  ⟨encodeEquation σ, encodeEquation_injective⟩

/-- Complete decoding of the original outer equation framing and both child
trees, with the native tuple representation only at the typed output boundary. -/
theorem decodeEquation_polyTime : ComputableInPolyTime (decodeEquation σ) encBits
    (encOption (encPair termEncoding termEncoding)) := by
  have hl := (decode_polyTime (σ := σ)).comp (fst encBits encBits)
  have hr := (decode_polyTime (σ := σ)).comp (snd encBits encBits)
  have hboth := optionPairWithInput_polyTime hl hr
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) (pair : List Bool × List Bool) => (decode σ pair.1).bind
      (fun left => (decode σ pair.2).map (fun right => (left, right))))
    (const none) (hboth.comp (snd encBits (encPair encBits encBits)))
  convert h using 1
  funext word
  unfold decodeEquation
  cases Words.unpair? word with
  | none => rfl
  | some pair =>
    change (decode σ pair.1).bind (fun left => (decode σ pair.2).bind (fun right => some (left, right))) =
      (decode σ pair.1).bind (fun left => (decode σ pair.2).map (fun right => (left, right)))
    cases decode σ pair.1 <;> cases decode σ pair.2 <;> rfl

@[fun_prop] theorem encodeEquation_polyTime : ComputableInPolyTime (encodeEquation σ)
    (encPair termEncoding termEncoding) encBits :=
  Framing.pair_polyTime.comp ((encode_polyTime.comp (fst _ _)).prod (encode_polyTime.comp (snd _ _)))

/-- Re-encode the native typed tuple into the original paper equation format. -/
theorem equationRecode_polyTime : ComputableInPolyTime
    (id : Equational.Term σ ℕ × Equational.Term σ ℕ → _)
    (encPair termEncoding termEncoding) equationEncoding :=
  encodeEquation_polyTime.of_enc_eq (fun _ => rfl)

/-- Recover native typed arguments from the original injective equation codec. -/
theorem arguments_polyTime : ComputableInPolyTime
    (id : Equational.Term σ ℕ × Equational.Term σ ℕ → _)
    equationEncoding (encPair termEncoding termEncoding) := by
  have hw : ComputableInPolyTime (encodeEquation σ) equationEncoding encBits := .of_eq (fun _ => rfl)
  have hd := (decodeEquation_polyTime (σ := σ)).comp hw
  have h := hd.optionGetDWithInput (const ((.var 0, .var 0) : Equational.Term σ ℕ × Equational.Term σ ℕ))
  convert h using 1
  funext equation
  simp only [Function.comp_def, decodeEquation_encodeEquation, Option.getD_some, id_eq]

end KFOL.Complexity.FiniteTermMachines
