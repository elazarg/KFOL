module

public import KFOL.Complexity.BlockScan
public import KFOL.Algorithms.GuardRecord
public import Complexity.Foundations.Data.BitString.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy

/-! # Sparse binary-label and complete dictionary machines

Natural labels retain binary encodings throughout. Their numeric values are
never used as an iteration clock or a unary output bound.
-/

@[expose] public section

namespace KFOL.Complexity.Dictionary

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Words

private theorem value_eq_lsb (word : List Bool) :
    BinaryNatCode.value word = Cslib.BitString.lsbValue word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    cases bit <;> simp [BinaryNatCode.value, Cslib.BitString.lsbValue, ih, Nat.bit, Nat.add_comm]

/-- Arbitrary little-endian input words are interpreted in polynomial time
with a binary natural output, even for large sparse variable names. -/
@[fun_prop] theorem value_polyTime : ComputableInPolyTime BinaryNatCode.value encBits encNat := by
  have he : BinaryNatCode.value = fun word => Cslib.BitString.binaryValue word.reverse :=
    funext (fun word => (value_eq_lsb word).trans (Cslib.BitString.lsbValue_eq_binaryValue_reverse word))
  rw [he]
  exact bitsBinaryValue.comp bitsReverse

/-- Canonical binary serialization agrees with the native natural embedding. -/
@[fun_prop] theorem encode_polyTime : ComputableInPolyTime BinaryNatCode.encode encNat encBits := by
  exact .of_eq (fun _ => rfl)

/-- Reject noncanonical binary names while retaining binary output costs. -/
@[fun_prop] theorem decode_polyTime :
    ComputableInPolyTime BinaryNatCode.decode? encBits (encOption encNat) := by
  have hbits := encode_polyTime.comp value_polyTime
  have htest := decide_eq' hbits (id' (encIn := encBits))
  have hsome := (optionSome encNat).comp value_polyTime
  have h := htest.ite hsome (const none)
  convert h using 1
  funext word
  by_cases hc : (BinaryNatCode.value word).bits = word <;>
    simp [BinaryNatCode.decode?, BinaryNatCode.encode, hc]

private theorem mapM_decode_eq (blocks : List (List Bool)) :
    blocks.mapM BinaryNatCode.decode? =
      if blocks.all (fun word => decide ((BinaryNatCode.value word).bits = word)) then
        some (blocks.map BinaryNatCode.value) else none := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    rw [List.mapM_cons, ih]
    by_cases hb : (BinaryNatCode.value block).bits = block
    · simp only [BinaryNatCode.decode?, hb, ite_true, List.all_cons,
        decide_true, Bool.true_and, List.map_cons]
      cases blocks.all _ <;> rfl
    · simp [BinaryNatCode.decode?, hb]

private theorem decodeBlocks_polyTime : ComputableInPolyTime
    (fun blocks : List (List Bool) => blocks.mapM BinaryNatCode.decode?)
      (encList encBits) (encOption (encList encNat)) := by
  have hvalue : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => BinaryNatCode.value p.2)
      (encPair (encList encBits) encBits) encNat := value_polyTime.comp (snd _ _)
  have hmap : ComputableInPolyTime
      (fun blocks : List (List Bool) => blocks.map BinaryNatCode.value)
      (encList encBits) (encList encNat) := mapWithInput id' hvalue
  have hword : ComputableInPolyTime (fun p : List (List Bool) × List Bool => p.2)
      (encPair (encList encBits) encBits) encBits := snd _ _
  have hbits := encode_polyTime.comp hvalue
  have htest : ComputableInPolyTime
      (fun p : List (List Bool) × List Bool => decide ((BinaryNatCode.value p.2).bits = p.2))
      (encPair (encList encBits) encBits) encBool := decide_eq' hbits hword
  have hall := allWithInput
    (test := fun (_ : List (List Bool)) word => decide ((BinaryNatCode.value word).bits = word))
    (id' (encIn := encList encBits)) htest
  have h := hall.ite ((optionSome (encList encNat)).comp hmap) (const none)
  have he := funext mapM_decode_eq
  rw [he]
  exact h

/-- Complete sparse-name dictionaries are decoded by an actual native
polynomial-time machine, including malformed framing and noncanonical names. -/
@[fun_prop] theorem dictionary_decode_polyTime :
    ComputableInPolyTime Algorithms.LabelDictionary.decode encBits (encOption (encList encNat)) := by
  have hbody : ComputableInPolyTime
      (fun p : List Bool × List (List Bool) => p.2.mapM BinaryNatCode.decode?)
      (encPair encBits (encList encBits)) (encOption (encList encNat)) :=
    decodeBlocks_polyTime.comp (snd _ _)
  have h := BlockScan.undelimitBlocks_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) blocks => blocks.mapM BinaryNatCode.decode?) (const none) hbody
  convert h using 1
  funext word
  unfold Algorithms.LabelDictionary.decode
  cases undelimitBlocks word <;> rfl

/-- Checking uniqueness charges binary name comparisons and all list scans. -/
@[fun_prop] theorem dictionary_nodup_polyTime : ComputableInPolyTime
    (fun labels : List ℕ => decide labels.Nodup) (encList encNat) encBool :=
  decide_nodup id'

end KFOL.Complexity.Dictionary
