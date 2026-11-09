module

public import KFOL.Complexity.DescriptorValidation
public import KFOL.Complexity.OptionTraversal
public import KFOL.Complexity.GuardSubset
public import KFOL.Algorithms.Normalization

/-! # Native decoded records and normalization under the exact descriptor codec -/

@[expose] public section

namespace KFOL.Complexity.RawRecords

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Words KFOL.Algorithms

abbrev Record := ℕ × List Bool
abbrev recordEncoding := encPair encNat encBits
abbrev Data := List ℕ × List Record
abbrev dataEncoding := encPair (encList encNat) (encList recordEncoding)

private def decodeRecord (word : List Bool) : Option Record := do
  let p ← unpair? word
  let index ← BinaryNatCode.decode? p.1
  return (index, p.2)

private theorem decodeRecord_polyTime :
    ComputableInPolyTime decodeRecord encBits (encOption recordEncoding) := by
  let outer := encPair encBits (encPair encBits encBits)
  have hindex : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => BinaryNatCode.decode? p.2.1)
      outer (encOption encNat) := Dictionary.decode_polyTime.comp (by fun_prop)
  have hfinish : ComputableInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × ℕ => (p.2, p.1.2.2))
      (encPair outer encNat) recordEncoding := by
    apply ComputableInPolyTime.pair (enc₁ := encNat) (enc₂ := encBits)
    · fun_prop
    · fun_prop
  have hinner := hindex.optionMapWithInput (f := fun p index => (index, p.2.2)) hfinish
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => (BinaryNatCode.decode? p.1).map (fun index => (index, p.2)))
    (const none) (by simpa only [Function.comp_def] using hinner)
  convert h using 1
  funext word
  unfold decodeRecord
  cases unpair? word with
  | none => rfl
  | some p =>
    simp only [Option.elim_some]
    cases hi : BinaryNatCode.decode? p.1 <;> simp [hi]

private theorem decodeRecord_encode {n : ℕ} (r : GuardRecord.Record n) :
    decodeRecord (GuardRecord.encode r) = some (r.1.val, Bitset.encode r.2) := by
  simp [decodeRecord, GuardRecord.encode]

private def decodeStream (word : List Bool) : Option (List Record) := do
  let blocks ← undelimitBlocks word
  blocks.mapM decodeRecord

private theorem decodeStream_polyTime :
    ComputableInPolyTime decodeStream encBits (encOption (encList recordEncoding)) := by
  have hrecords : ComputableInPolyTime (fun blocks : List (List Bool) => blocks.mapM decodeRecord)
      (encList encBits) (encOption (encList recordEncoding)) :=
    mapMWithInput_polyTime (id' (encIn := encList encBits))
      (decodeRecord_polyTime.comp (snd _ _)) (0, [])
  have hbody := hrecords.comp (snd encBits (encList encBits))
  have h := BlockScan.undelimitBlocks_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) blocks => blocks.mapM decodeRecord) (const none) hbody
  convert h using 1
  funext word
  unfold decodeStream
  cases undelimitBlocks word <;> rfl

def recordView {n : ℕ} (r : GuardRecord.Record n) : Record :=
  (r.1.val, Bitset.encode r.2)

private theorem decodeStream_encode {n : ℕ} (records : List (GuardRecord.Record n)) :
    decodeStream (GuardRecord.encodeList records) = some (records.map recordView) := by
  unfold decodeStream GuardRecord.encodeList
  rw [undelimitBlocks_flatten_delimit]
  change (records.map GuardRecord.encode).mapM decodeRecord = some (records.map recordView)
  induction records with
  | nil => rfl
  | cons r records ih =>
    simp only [List.map_cons, List.mapM_cons, decodeRecord_encode]
    rw [ih]
    rfl

private def decodeData (word : List Bool) : Option Data := do
  let p ← unpair? word
  let labels ← LabelDictionary.decode p.1
  let records ← decodeStream p.2
  return (labels, records)

private theorem decodeData_polyTime : ComputableInPolyTime decodeData encBits (encOption dataEncoding) := by
  let outer := encPair encBits (encPair encBits encBits)
  let inner := encPair outer (encList encNat)
  have hlabels : ComputableInPolyTime
      (fun p : List Bool × (List Bool × List Bool) => LabelDictionary.decode p.2.1)
      outer (encOption (encList encNat)) := Dictionary.dictionary_decode_polyTime.comp (by fun_prop)
  have hrecords : ComputableInPolyTime
      (fun p : (List Bool × (List Bool × List Bool)) × List ℕ => decodeStream p.1.2.2)
      inner (encOption (encList recordEncoding)) := decodeStream_polyTime.comp (by fun_prop)
  have hfinish : ComputableInPolyTime
      (fun p : ((List Bool × (List Bool × List Bool)) × List ℕ) × List Record => (p.1.2, p.2))
      (encPair inner (encList recordEncoding)) dataEncoding := by
    apply ComputableInPolyTime.pair (enc₁ := encList encNat) (enc₂ := encList recordEncoding)
    · fun_prop
    · fun_prop
  have hrecordMap := hrecords.optionMapWithInput (f := fun p records => (p.2, records)) hfinish
  have hlabelBind := hlabels.optionElimWithInput
    (body := fun p labels => (decodeStream p.2.2).map (fun records => (labels, records)))
    (const none) (by simpa only [Function.comp_def] using hrecordMap)
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => (LabelDictionary.decode p.1).elim none
      (fun labels => (decodeStream p.2).map (fun records => (labels, records))))
    (const none) (by simpa only [Function.comp_def] using hlabelBind)
  convert h using 1
  funext word
  unfold decodeData
  cases unpair? word with
  | none => rfl
  | some p =>
    simp only [Option.elim_some]
    cases hl : LabelDictionary.decode p.1 <;> cases hr : decodeStream p.2 <;> simp [hl, hr]

/-- Native binary labels and membership words of the actual typed descriptor. -/
def view (d : GuardDescriptor) : Data := (d.labels, d.records.map recordView)

private theorem decodeData_encode (d : GuardDescriptor) : decodeData (GuardDescriptor.encode d) = some (view d) := by
  simp [decodeData, GuardDescriptor.encode, decodeStream_encode, view]

/-- The typed descriptor can be read into native list/pair data in polynomial
time under the original exact serialization, without unary label expansion. -/
@[fun_prop] theorem view_polyTime : ComputableInPolyTime view
    DescriptorValidation.descriptorEncoding dataEncoding := by
  have hencode : ComputableInPolyTime GuardDescriptor.encode
      DescriptorValidation.descriptorEncoding encBits := .of_eq (fun _ => rfl)
  have h := (decodeData_polyTime.comp hencode).optionGetDWithInput (const ([], []))
  convert h using 1
  funext d
  dsimp only [Function.comp_def]
  rw [decodeData_encode]
  rfl


/-- Emit the original single-record word format from native field data. -/
def encodeRecord (r : Record) : List Bool := pair (BinaryNatCode.encode r.1) r.2

@[fun_prop] theorem encodeRecord_polyTime : ComputableInPolyTime encodeRecord recordEncoding encBits :=
  Framing.pair_polyTime.comp ((Dictionary.encode_polyTime.comp (fst encNat encBits)).prod (snd encNat encBits))

/-- Frame each emitted record independently, preserving list order. -/
def encodeStream (records : List Record) : List Bool :=
  (records.map (fun r => delimit (encodeRecord r))).flatten

@[fun_prop] theorem encodeStream_polyTime :
    ComputableInPolyTime encodeStream (encList recordEncoding) encBits := by
  have hrecord := (Framing.delimit_polyTime.comp encodeRecord_polyTime).comp
    (snd (encList recordEncoding) recordEncoding)
  have h := flatMapToBitsWithInput (f := fun (_ : List Record) r => delimit (encodeRecord r))
    (id' (encIn := encList recordEncoding)) hrecord
  convert h using 1
  funext records
  simp only [encodeStream, List.flatMap_def]

private theorem dictionary_encode_polyTime :
    ComputableInPolyTime LabelDictionary.encode (encList encNat) encBits := by
  have hlabel := (Framing.delimit_polyTime.comp Dictionary.encode_polyTime).comp
    (snd (encList encNat) encNat)
  have h := flatMapToBitsWithInput (f := fun (_ : List ℕ) j => delimit (BinaryNatCode.encode j))
    (id' (encIn := encList encNat)) hlabel
  convert h using 1
  funext labels
  simp only [LabelDictionary.encode, List.map_map, List.flatMap_def, Function.comp_def]

/-- Emit the original descriptor format, without changing its dictionary or records. -/
def encodeData (data : Data) : List Bool := pair (LabelDictionary.encode data.1) (encodeStream data.2)

@[fun_prop] theorem encodeData_polyTime : ComputableInPolyTime encodeData dataEncoding encBits :=
  Framing.pair_polyTime.comp ((dictionary_encode_polyTime.comp (fst _ _)).prod
    (encodeStream_polyTime.comp (snd _ _)))

@[simp] theorem encodeData_view (d : GuardDescriptor) : encodeData (view d) = GuardDescriptor.encode d := by
  simp only [encodeData, view, GuardDescriptor.encode, encodeStream, GuardRecord.encodeList, List.map_map,
    Function.comp_def, recordView, encodeRecord, GuardRecord.encode]

end KFOL.Complexity.RawRecords
