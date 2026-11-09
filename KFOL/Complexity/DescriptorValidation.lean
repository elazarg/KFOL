module

public import KFOL.Complexity.Dictionary
public import KFOL.Algorithms.GuardDescriptor
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Native machine certificates for complete external descriptor validation -/

@[expose] public section

namespace KFOL.Complexity.DescriptorValidation

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Words

private def recordValid (n : ℕ) (word : List Bool) : Bool :=
  (unpair? word).elim false fun p =>
    decide ((BinaryNatCode.value p.1).bits = p.1) &&
    decide (BinaryNatCode.value p.1 < n) && decide (p.2.length = n)

private theorem recordValid_eq (n : ℕ) (word : List Bool) :
    recordValid n word = (Algorithms.GuardRecord.decode n word).isSome := by
  cases hp : unpair? word with
  | none => simp [recordValid, Algorithms.GuardRecord.decode, hp]
  | some p =>
    by_cases hc : (BinaryNatCode.value p.1).bits = p.1 <;>
      by_cases hr : BinaryNatCode.value p.1 < n <;>
        by_cases hw : p.2.length = n <;>
          simp [recordValid, Algorithms.GuardRecord.decode, hp, BinaryNatCode.decode?,
            Algorithms.Bitset.decode, hc, hr, hw]

private theorem recordValid_polyTime : ComputableInPolyTime
    (fun p : ℕ × List Bool => recordValid p.1 p.2) (encPair encUnary encBits) encBool := by
  let input := encPair encUnary encBits
  let callback := encPair input (encPair encBits encBits)
  have hword : ComputableInPolyTime (fun p : ℕ × List Bool => p.2) input encBits := snd _ _
  have hp := Framing.unpair_polyTime.comp hword
  have hindex : ComputableInPolyTime (fun p : (ℕ × List Bool) × (List Bool × List Bool) => p.2.1)
      callback encBits := by fun_prop
  have hwidth : ComputableInPolyTime (fun p : (ℕ × List Bool) × (List Bool × List Bool) => p.1.1)
      callback encUnary := by fun_prop
  have hvalue := Dictionary.value_polyTime.comp hindex
  have hcanon := decide_eq' (Dictionary.encode_polyTime.comp hvalue) hindex
  have hbound := binary_lt' hvalue (unary_to_binary.comp hwidth)
  have hlength := decide_eq' (length_bits.comp
    (show ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (List Bool × List Bool) => p.2.2) callback encBits by fun_prop)) hwidth
  have hbody := bool_and' (bool_and' hcanon hbound) hlength
  have hbody' : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × (List Bool × List Bool) =>
        decide ((BinaryNatCode.value p.2.1).bits = p.2.1) &&
        decide (BinaryNatCode.value p.2.1 < p.1.1) && decide (p.2.2.length = p.1.1))
      callback encBool := by
    convert hbody using 1
    funext p
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_def, BinaryNatCode.encode, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hc : (BinaryNatCode.value p.2.1).bits = p.2.1 <;> simp [hc]
  have h := hp.optionElimWithInput
    (body := fun p q => decide ((BinaryNatCode.value q.1).bits = q.1) &&
      decide (BinaryNatCode.value q.1 < p.1) && decide (q.2.length = p.1))
    (const false) hbody'
  exact h

private theorem isSome_mapM {α β : Type*} (f : α → Option β) (xs : List α) :
    (xs.mapM f).isSome = xs.all (fun x => (f x).isSome) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, List.all_cons]
    rw [← ih]
    cases f x <;> cases xs.mapM f <;> rfl

private def streamValid (n : ℕ) (word : List Bool) : Bool :=
  (undelimitBlocks word).elim false fun blocks => blocks.all (recordValid n)

private theorem streamValid_eq (n : ℕ) (word : List Bool) :
    streamValid n word = (Algorithms.GuardRecord.decodeList n word).isSome := by
  unfold streamValid Algorithms.GuardRecord.decodeList
  cases undelimitBlocks word with
  | none => rfl
  | some blocks =>
    change blocks.all (recordValid n) = (blocks.mapM (Algorithms.GuardRecord.decode n)).isSome
    rw [isSome_mapM]
    congr 1
    funext block
    exact recordValid_eq n block

private theorem streamValid_polyTime : ComputableInPolyTime
    (fun p : ℕ × List Bool => streamValid p.1 p.2) (encPair encUnary encBits) encBool := by
  let input := encPair encUnary encBits
  let callback := encPair input (encList encBits)
  have hp := BlockScan.undelimitBlocks_polyTime.comp (snd encUnary encBits)
  have hrecords : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × List (List Bool) => p.2) callback (encList encBits) := snd _ _
  have htest : ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List (List Bool)) × List Bool => recordValid p.1.1.1 p.2)
      (encPair callback encBits) encBool := recordValid_polyTime.comp
    ((show ComputableInPolyTime
      (fun p : ((ℕ × List Bool) × List (List Bool)) × List Bool => p.1.1.1)
      (encPair callback encBits) encUnary by fun_prop).prod (snd _ _))
  have hall := allWithInput (test := fun p block => recordValid p.1.1 block) hrecords htest
  exact hp.optionElimWithInput (const false) hall

private def descriptorValid (word : List Bool) : Bool :=
  (unpair? word).elim false fun p =>
    (Algorithms.LabelDictionary.decode p.1).elim false fun labels =>
      if labels.Nodup then streamValid labels.length p.2 else false

private theorem descriptorValid_eq (word : List Bool) :
    descriptorValid word = (Algorithms.GuardDescriptor.decode word).isSome := by
  cases hp : unpair? word with
  | none => simp [descriptorValid, Algorithms.GuardDescriptor.decode, hp]
  | some p =>
    cases hd : Algorithms.LabelDictionary.decode p.1 with
    | none => simp [descriptorValid, Algorithms.GuardDescriptor.decode, hp, hd]
    | some labels =>
      by_cases hn : labels.Nodup
      · rw [show descriptorValid word = streamValid labels.length p.2 by
          simp [descriptorValid, hp, hd, hn], streamValid_eq]
        cases hr : Algorithms.GuardRecord.decodeList labels.length p.2 <;>
          simp [Algorithms.GuardDescriptor.decode, hp, hd, hn, hr]
      · simp [descriptorValid, Algorithms.GuardDescriptor.decode, hp, hd, hn]

/-- Complete binary descriptor validation is polynomial-time, uniformly in
dictionary width and binary label values. The certified Boolean result is
exactly successful decoding by the existing dependent descriptor parser. -/
@[fun_prop] theorem decode_isSome_polyTime : ComputableInPolyTime
    (fun word => (Algorithms.GuardDescriptor.decode word).isSome) encBits encBool := by
  let pairEncoding := encPair encBits encBits
  let outer := encPair encBits pairEncoding
  let inner := encPair outer (encList encNat)
  have hp := Framing.unpair_polyTime
  have hdict : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => Algorithms.LabelDictionary.decode p.2.1)
      outer (encOption (encList encNat)) := Dictionary.dictionary_decode_polyTime.comp (by fun_prop)
  have hlabels : ComputableInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × List ℕ => p.2)
      inner (encList encNat) := snd _ _
  have hnodup := Dictionary.dictionary_nodup_polyTime.comp hlabels
  have hwidth := (length_list encNat).comp hlabels
  have hstream : ComputableInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × List ℕ => p.1.2.2)
      inner encBits := by fun_prop
  have hcheck := streamValid_polyTime.comp (hwidth.prod hstream)
  have hbody := hnodup.ite hcheck (const false)
  have hinner := hdict.optionElimWithInput
    (body := fun p labels => if decide labels.Nodup then streamValid labels.length p.2.2 else false)
    (const false) (by simpa only [Function.comp_def] using hbody)
  have h := hp.optionElimWithInput
    (body := fun (_ : List Bool) p => (Algorithms.LabelDictionary.decode p.1).elim false
      (fun labels => if decide labels.Nodup then streamValid labels.length p.2 else false))
    (const false) (by simpa only [Function.comp_def] using hinner)
  convert h using 1
  funext word
  rw [← descriptorValid_eq]
  unfold descriptorValid
  cases hpair : unpair? word with
  | none => rfl
  | some p =>
    simp only [Option.elim_some]
    cases hlabels : Algorithms.LabelDictionary.decode p.1 with
    | none => rfl
    | some labels =>
      by_cases hn : labels.Nodup <;> simp [hn]

/-- The descriptor's existing exact binary serialization, bundled as the
injective output encoding required by the native machine model. -/
def descriptorEncoding : Algorithms.GuardDescriptor ↪ List Bool :=
  ⟨Algorithms.GuardDescriptor.encode, Algorithms.GuardDescriptor.encode_injective⟩

@[simp] theorem descriptorEncoding_apply (d : Algorithms.GuardDescriptor) :
    descriptorEncoding d = Algorithms.GuardDescriptor.encode d := rfl

/-- The complete dependent descriptor decoder is polynomial-time under its
existing exact serialization. Validation followed by copying the original
word writes the precise encoding of the decoded value, with no certificate
or numeric-value clock supplied by the caller. -/
@[fun_prop] theorem decode_polyTime : ComputableInPolyTime
    Algorithms.GuardDescriptor.decode encBits (encOption descriptorEncoding) := by
  have hcopy := decode_isSome_polyTime.ite
    ((optionSome encBits).comp (id' (encIn := encBits))) (const none)
  apply hcopy.of_enc_eq
  intro word
  cases hd : Algorithms.GuardDescriptor.decode word with
  | none => simp
  | some d =>
    simp only [Option.isSome_some, ite_true, encOption_some,
      descriptorEncoding_apply]
    exact congrArg (List.cons true) (Algorithms.GuardDescriptor.encode_of_decode hd)

end KFOL.Complexity.DescriptorValidation
