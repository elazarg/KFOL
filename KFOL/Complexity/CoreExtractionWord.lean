module

public import KFOL.Complexity.CoreExtractionAnnotate
public import KFOL.Complexity.OptionTraversal

/-! # Complete native original-word extraction, uniformly in binary role count -/

@[expose] public section

namespace KFOL.Complexity.CoreExtraction

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

/-- Parse only the physically stored binary header and complete original raw
tree. Raw role/array validation is the next separately certified stage. -/
def parseInputWord (word : List Bool) : Option (ℕ × Raw) := do
  let (countWord,treeWord) ← Words.unpair? word
  let K ← Words.BinaryNatCode.decode? countWord
  let raw ← decode treeWord
  return (K,raw)

/-- Validation precedes extraction; output uses the same canonical binary role
count and the complete extracted original-tree code. -/
def finishInputWord (input : ℕ × Raw) : Option (List Bool) :=
  if valid input.1 input.2 then
    (extractRaw input.2).map fun core =>
      Words.pair (Words.BinaryNatCode.encode input.1) (encode core)
  else none

/-- Reconstructing the canonical count header is exact on successful binary
decoding, including malformed/trailing-byte rejection on every other input. -/
theorem extractWord_eq_parse_finish (word : List Bool) :
    extractWord word = (parseInputWord word).bind finishInputWord := by
  cases ho : Words.unpair? word with
  | none => simp [extractWord,parseInputWord,ho]
  | some pair =>
    rcases pair with ⟨countWord,treeWord⟩
    cases hc : Words.BinaryNatCode.decode? countWord with
    | none => simp [extractWord,parseInputWord,ho,hc]
    | some K =>
      have hcount : countWord = Words.BinaryNatCode.encode K :=
        (Words.BinaryNatCode.decode?_eq_some_iff countWord K).mp hc
      cases ht : decode treeWord with
      | none => simp [extractWord,parseInputWord,ho,hc,ht]
      | some raw =>
        cases hv : valid K raw <;> cases hx : extractRaw raw <;>
          simp [extractWord,parseInputWord,finishInputWord,ho,ht,hcount,hv,hx]

noncomputable abbrev parsedEncoding := encPair encNat FullTermMachines.termEncoding

theorem parseInputWord_polyTime : ComputableInPolyTime parseInputWord encBits (encOption parsedEncoding) := by
  let callback := encPair encBits (encPair encBits encBits)
  have hcount : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => p.2.1)
      callback encBits := by fun_prop
  have htree : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => p.2.2)
      callback encBits := by fun_prop
  have hK := Dictionary.decode_polyTime.comp hcount
  have hraw := FullTermMachines.decode_polyTime.comp htree
  have hpair := optionPairWithInput_polyTime hK hraw
  have hbody : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => do
        let K ← Words.BinaryNatCode.decode? p.2.1
        let raw ← decode p.2.2
        pure (K,raw)) callback (encOption parsedEncoding) := by
    convert hpair using 1
    funext p
    dsimp only [Function.comp_def]
    cases Words.BinaryNatCode.decode? p.2.1 <;> cases decode p.2.2 <;> rfl
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) pair => do
      let K ← Words.BinaryNatCode.decode? pair.1
      let raw ← decode pair.2
      pure (K,raw)) (const none) hbody
  convert h using 1
  funext word
  unfold parseInputWord
  cases Words.unpair? word <;> rfl

theorem finishInputWord_polyTime : ComputableInPolyTime finishInputWord parsedEncoding (encOption encBits) := by
  have hraw := snd encNat FullTermMachines.termEncoding
  have hextract := extractRaw_polyTime.comp hraw
  have hK : ComputableInPolyTime (fun p : (ℕ × Raw) × Raw => p.1.1)
      (encPair parsedEncoding FullTermMachines.termEncoding) encNat := by fun_prop
  have hout := FullTermMachines.encode_polyTime.comp (snd parsedEncoding FullTermMachines.termEncoding)
  have hbody := Framing.pair_polyTime.comp ((Dictionary.encode_polyTime.comp hK).prod hout)
  have hmap := hextract.optionMapWithInput
    (f := fun (input : ℕ × Raw) core => Words.pair (Words.BinaryNatCode.encode input.1) (encode core)) hbody
  have h := valid_polyTime.ite hmap (const none)
  exact h

/-- The complete original binary input-to-output extraction has a native
multitape Turing machine with a polynomial clock. K and all sparse names stay
binary; only physically stored permutation arrays are traversed. This theorem
covers every malformed input word as well as every original typed source. -/
theorem extractWord_polyTime : ComputableInPolyTime extractWord encBits (encOption encBits) := by
  have hfinish := finishInputWord_polyTime.comp (snd encBits parsedEncoding)
  have h := parseInputWord_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) input => finishInputWord input) (const none) hfinish
  convert h using 1
  funext word
  rw [extractWord_eq_parse_finish]
  cases parseInputWord word <;> rfl

end KFOL.Complexity.CoreExtraction
