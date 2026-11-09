module

public import KFOL.Complexity.GuardExtraction

/-! # Shared dictionary compression and the complete binary guard frontend -/

@[expose] public section

namespace KFOL.Complexity.GuardCompression

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms KFOL.Complexity.GuardExtraction

private theorem mem_polyTime : ComputableInPolyTime
    (fun p : ℕ × List ℕ => decide (p.1 ∈ p.2)) (encPair encNat (encList encNat)) encBool := by
  have hlist := snd encNat (encList encNat)
  have hj : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ => p.1.1)
      (encPair (encPair encNat (encList encNat)) encNat) encNat := by fun_prop
  have h := anyWithInput (test := fun (p : ℕ × List ℕ) (q : ℕ) => decide (q = p.1)) hlist
    (decide_eq' (snd _ _) hj)
  convert h using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.any_eq_true]
  simp

/-- Compress listed prerequisite names by membership, retaining no numeric
ambient dimension. Unknown output names are rejected. -/
def compress (D : List ℕ) (p : Entry) : Option RawRecords.Record :=
  if p.1 ∈ D then some (D.idxOf p.1, D.map (fun j => decide (j ∈ p.2))) else none

@[fun_prop] theorem compress_polyTime : ComputableInPolyTime
    (fun p : List ℕ × Entry => compress p.1 p.2)
    (encPair (encList encNat) entryEncoding) (encOption RawRecords.recordEncoding) := by
  let input := encPair (encList encNat) entryEncoding
  have hd := fst (encList encNat) entryEncoding
  have hj : ComputableInPolyTime (fun p : List ℕ × Entry => p.2.1) input encNat := by fun_prop
  have ha : ComputableInPolyTime (fun p : List ℕ × Entry => p.2.2) input (encList encNat) := by fun_prop
  have hmem := mem_polyTime.comp (hj.prod hd)
  have hindex := unary_to_binary.comp (idxOfWithInput hd hj)
  have hnames : ComputableInPolyTime (fun p : (List ℕ × Entry) × ℕ => p.1.2.2)
      (encPair input encNat) (encList encNat) := by fun_prop
  have hmember := mem_polyTime.comp ((snd input encNat).prod hnames)
  have hbits := mapToBitsWithInput (f := fun (p : List ℕ × Entry) (j : ℕ) => decide (j ∈ p.2.2)) hd hmember
  have hsome := (optionSome RawRecords.recordEncoding).comp (hindex.prod hbits)
  have h := hmem.ite hsome (const none)
  convert h using 1
  funext p
  simp only [compress, Function.comp_def, decide_eq_true_eq]

private theorem compress_bitset (D A : List ℕ) :
    Bitset.encode (SupportIndex.compress D A.toFinset) = D.map (fun j => decide (j ∈ A)) := by
  apply List.ext_getElem (by simp [Bitset.encode])
  intro i hi hi'
  simp [Bitset.encode, SupportIndex.compress]

/-- Raw compression is exactly the native view of the established dependent
record compression, without a dictionary uniqueness assumption. -/
theorem compress_view (D : List ℕ) (p : Entry) :
    compress D p = (SupportIndex.compressEntry D (p.1, p.2.toFinset)).map RawRecords.recordView := by
  unfold compress SupportIndex.compressEntry SupportIndex.locate
  split <;> simp_all [RawRecords.recordView, compress_bitset]

/-- Complete traversal, retaining the actual dictionary for subsequent output. -/
def compressAll (D : List ℕ) (records : List Entry) : Option (List RawRecords.Record) :=
  records.mapM (compress D)

@[fun_prop] theorem compressAll_polyTime : ComputableInPolyTime
    (fun p : List ℕ × List Entry => compressAll p.1 p.2)
    (encPair (encList encNat) (encList entryEncoding)) (encOption (encList RawRecords.recordEncoding)) := by
  let input := encPair (encList encNat) (encList entryEncoding)
  have hd : ComputableInPolyTime (fun p : (List ℕ × List Entry) × Entry => p.1.1)
      (encPair input entryEncoding) (encList encNat) := by fun_prop
  have hp := snd input entryEncoding
  exact mapMWithInput_polyTime (f := fun (p : List ℕ × List Entry) entry => compress p.1 entry)
    (snd _ _) (compress_polyTime.comp (hd.prod hp)) (0, [])

private theorem mapM_map_naturality {A B C : Type} (f : A → Option B) (g : B → C) (xs : List A) :
    xs.mapM (fun x => (f x).map g) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons]
    cases hx : f x with
    | none => rfl
    | some b =>
      simp only [Option.map_some]
      rw [ih]
      cases xs.mapM f <;> rfl

/-- The complete raw traversal is the same dependent record list under its
native projection; the equality covers every failure case as well. -/
theorem compressAll_view (D : List ℕ) (records : List Entry) :
    compressAll D records =
      ((records.map (fun p => (p.1, p.2.toFinset))).mapM (SupportIndex.compressEntry D)).map
        (List.map RawRecords.recordView) := by
  have hf : compress D = fun p =>
      (SupportIndex.compressEntry D (p.1, p.2.toFinset)).map RawRecords.recordView :=
    funext (compress_view D)
  simp only [compressAll, List.mapM_map]
  rw [hf]
  exact mapM_map_naturality _ _ records

private def extractTerm (t : Reset.Term ℕ) : Option (List Bool) :=
  (compressAll (SupportIndex.labels t) (collect t).2).map
    (fun records => RawRecords.encodeData (SupportIndex.labels t, records))

private theorem extractTerm_polyTime : ComputableInPolyTime extractTerm
    TermMachine.termEncoding (encOption encBits) := by
  have hd := TermSupport.labels_polyTime
  have hr := (snd encNat (encList entryEncoding)).comp collect_polyTime
  have hrecords := compressAll_polyTime.comp (hd.prod hr)
  have hdict : ComputableInPolyTime (fun p : Reset.Term ℕ × List RawRecords.Record => SupportIndex.labels p.1)
      (encPair TermMachine.termEncoding (encList RawRecords.recordEncoding)) (encList encNat) :=
    hd.comp (fst _ _)
  have hout := RawRecords.encodeData_polyTime.comp (hdict.prod (snd _ _))
  exact hrecords.optionMapWithInput
    (f := fun (t : Reset.Term ℕ) (records : List RawRecords.Record) =>
      RawRecords.encodeData (SupportIndex.labels t, records)) hout

private theorem encodeStream_view {n : ℕ} (records : List (GuardRecord.Record n)) :
    RawRecords.encodeStream (records.map RawRecords.recordView) = GuardRecord.encodeList records := by
  simp only [RawRecords.encodeStream, GuardRecord.encodeList, List.map_map, Function.comp_def,
    RawRecords.encodeRecord, RawRecords.recordView, GuardRecord.encode]

private theorem extractTerm_eq (t : Reset.Term ℕ) : extractTerm t = TermCode.extract (TermCode.encode t) := by
  unfold extractTerm
  rw [compressAll_view, collect_entries]
  conv_rhs => unfold TermCode.extract; rw [TermCode.decode_encode]
  change _ = (t.guardEntries.mapM (SupportIndex.compressEntry (SupportIndex.labels t))).bind
    (fun records => some (Words.pair (LabelDictionary.encode (SupportIndex.labels t)) (GuardRecord.encodeList records)))
  cases hr : t.guardEntries.mapM (SupportIndex.compressEntry (SupportIndex.labels t)) with
  | none => rfl
  | some records =>
    simp only [Option.map_some, Option.bind_some, RawRecords.encodeData, encodeStream_view]

/-- The complete original-tree frontend, including parsing, actual support,
raw guards, finite indexing and exact output framing, is polynomial-time. -/
@[fun_prop] theorem extract_polyTime : ComputableInPolyTime TermCode.extract encBits (encOption encBits) := by
  have hbody := extractTerm_polyTime.comp (snd encBits TermMachine.termEncoding)
  have h := TermMachine.decode_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) t => extractTerm t) (const none) hbody
  convert h using 1
  funext word
  unfold TermCode.extract
  cases ht : TermCode.decode word with
  | none => rfl
  | some t =>
    change (t.guardEntries.mapM (SupportIndex.compressEntry (SupportIndex.labels t))).bind
      (fun records => some (Words.pair (LabelDictionary.encode (SupportIndex.labels t))
        (GuardRecord.encodeList records))) = extractTerm t
    have he := extractTerm_eq t
    conv_rhs at he => unfold TermCode.extract; rw [TermCode.decode_encode]
    exact he.symm

end KFOL.Complexity.GuardCompression
