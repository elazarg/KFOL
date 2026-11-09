module
public import KFOL.Complexity.FullTermDecoding
public import KFOL.Algorithms.FullTermCode.Validation
@[expose] public section
namespace KFOL.Complexity.FullInputMachines
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
abbrev Input := ℕ × (Raw × Raw)
noncomputable abbrev pairEncoding := encPair FullTermMachines.termEncoding FullTermMachines.termEncoding
noncomputable abbrev inputEncoding := encPair encNat pairEncoding

def encodePair (pair : Raw × Raw) : List Bool := Words.pair (encode pair.1) (encode pair.2)
def encodeRawInput (input : Input) : List Bool := Words.pair (Words.BinaryNatCode.encode input.1) (encodePair input.2)
def decodePair (word : List Bool) : Option (Raw × Raw) := do
  let (left,right) ← Words.unpair? word
  let left ← decode left
  let right ← decode right
  return (left,right)
def decodeInput (word : List Bool) : Option Input := do
  let (count,equation) ← Words.unpair? word
  let K ← Words.BinaryNatCode.decode? count
  let equation ← decodePair equation
  return (K,equation)

@[simp] theorem decodePair_encodePair (pair : Raw × Raw) : decodePair (encodePair pair) = some pair := by
  simp [decodePair,encodePair]
@[simp] theorem decodeInput_encodeRawInput (input : Input) : decodeInput (encodeRawInput input) = some input := by
  simp [decodeInput,encodeRawInput]

theorem encodePair_of_decodePair {word : List Bool} {pair : Raw × Raw} (h : decodePair word = some pair) : encodePair pair = word := by
  unfold decodePair at h
  obtain ⟨⟨leftWord,rightWord⟩,houter,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨left,hl,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨right,hr,h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  rw [Words.eq_pair_of_unpair?_eq_some houter]
  simp only [encodePair,encode_of_decode hl,encode_of_decode hr]

theorem encodeRawInput_of_decodeInput {word : List Bool} {input : Input} (h : decodeInput word = some input) : encodeRawInput input = word := by
  unfold decodeInput at h
  obtain ⟨⟨countWord,pairWord⟩,houter,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨K,hK,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨pair,hpair,h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  have hc := (Words.BinaryNatCode.decode?_eq_some_iff countWord K).mp hK
  rw [Words.eq_pair_of_unpair?_eq_some houter]
  simp only [encodeRawInput,hc,encodePair_of_decodePair hpair]

theorem encodePair_polyTime : ComputableInPolyTime encodePair pairEncoding encBits :=
  Framing.pair_polyTime.comp ((FullTermMachines.encode_polyTime.comp (fst _ _)).prod
    (FullTermMachines.encode_polyTime.comp (snd _ _)))
theorem encodeRawInput_polyTime : ComputableInPolyTime encodeRawInput inputEncoding encBits :=
  Framing.pair_polyTime.comp ((Dictionary.encode_polyTime.comp (fst _ _)).prod
    (encodePair_polyTime.comp (snd _ _)))

theorem decodePair_polyTime : ComputableInPolyTime decodePair encBits (encOption pairEncoding) := by
  have hl := FullTermMachines.decode_polyTime.comp (fst encBits encBits)
  have hr := FullTermMachines.decode_polyTime.comp (snd encBits encBits)
  have hboth := optionPairWithInput_polyTime hl hr
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) (pair : List Bool × List Bool) => (decode pair.1).bind
      (fun left => (decode pair.2).map (fun right => (left,right))))
    (const none) (hboth.comp (snd encBits (encPair encBits encBits)))
  convert h using 1
  funext word
  unfold decodePair
  cases Words.unpair? word with
  | none => rfl
  | some pair =>
    rcases pair with ⟨left,right⟩
    change ((decode left).bind fun l => (decode right).bind fun r => some (l,r)) =
      (decode left).bind (fun l => (decode right).map (fun r => (l,r)))
    cases decode left <;> cases decode right <;> rfl

theorem decodeInput_polyTime : ComputableInPolyTime decodeInput encBits (encOption inputEncoding) := by
  let callback := encPair encBits (encPair encBits encBits)
  have hc : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => p.2.1) callback encBits := by fun_prop
  have he : ComputableInPolyTime (fun p : List Bool × (List Bool × List Bool) => p.2.2) callback encBits := by fun_prop
  have hboth := optionPairWithInput_polyTime (Dictionary.decode_polyTime.comp hc) (decodePair_polyTime.comp he)
  have hbody : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => do
        let K ← Words.BinaryNatCode.decode? p.2.1
        let equation ← decodePair p.2.2
        pure (K,equation)) callback (encOption inputEncoding) := by
    convert hboth using 1
    funext p
    dsimp only [Function.comp_def]
    cases Words.BinaryNatCode.decode? p.2.1 <;> cases decodePair p.2.2 <;> rfl
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) pair => do
      let K ← Words.BinaryNatCode.decode? pair.1
      let equation ← decodePair pair.2
      pure (K,equation)) (const none) hbody
  convert h using 1
  funext word
  unfold decodeInput
  cases Words.unpair? word <;> rfl
end KFOL.Complexity.FullInputMachines
