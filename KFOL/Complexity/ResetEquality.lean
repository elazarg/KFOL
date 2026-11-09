module

public import KFOL.Complexity.GuardCompression
public import KFOL.Complexity.NormalizeMachine
public import KFOL.Algorithms.ResetEquation

/-! # Native equality checking on shared actual binary support -/

@[expose] public section

namespace KFOL.Complexity.ResetEquality

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms KFOL.Complexity.RawRecords

private def sameRecords (a b : List Record) : Bool :=
  a.all (fun p => b.any (fun q => decide (p = q))) &&
    b.all (fun p => a.any (fun q => decide (p = q)))

private theorem sameRecords_polyTime : ComputableInPolyTime
    (fun p : List Record × List Record => sameRecords p.1 p.2)
    (encPair (encList recordEncoding) (encList recordEncoding)) encBool := by
  let input := encPair (encList recordEncoding) (encList recordEncoding)
  have ha := fst (encList recordEncoding) (encList recordEncoding)
  have hb := snd (encList recordEncoding) (encList recordEncoding)
  have hp : ComputableInPolyTime (fun p : ((List Record × List Record) × Record) × Record => p.1.2)
      (encPair (encPair input recordEncoding) recordEncoding) recordEncoding := by fun_prop
  have hq := snd (encPair input recordEncoding) recordEncoding
  have heq := decide_eq' hp hq
  have hab := anyWithInput (test := fun (p : (List Record × List Record) × Record) (q : Record) => decide (p.2 = q))
    (hb.comp (fst input recordEncoding)) heq
  have hba := anyWithInput (test := fun (p : (List Record × List Record) × Record) (q : Record) => decide (p.2 = q))
    (ha.comp (fst input recordEncoding)) heq
  exact bool_and' (allWithInput ha hab) (allWithInput hb hba)

private theorem sameRecords_iff (a b : List Record) :
    sameRecords a b = true ↔ a.toFinset = b.toFinset := by
  simp only [sameRecords, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hb⟩
    apply Finset.Subset.antisymm
    · intro p hp
      obtain ⟨q, hq, he⟩ := ha p (List.mem_toFinset.mp hp)
      exact List.mem_toFinset.mpr (he.symm ▸ hq)
    · intro p hp
      obtain ⟨q, hq, he⟩ := hb p (List.mem_toFinset.mp hp)
      exact List.mem_toFinset.mpr (he.symm ▸ hq)
  · intro he
    constructor <;> intro p hp
    · exact ⟨p, List.mem_toFinset.mp (he ▸ List.mem_toFinset.mpr hp), rfl⟩
    · exact ⟨p, List.mem_toFinset.mp (he.symm ▸ List.mem_toFinset.mpr hp), rfl⟩

private theorem recordView_injective {n : ℕ} : Function.Injective (@recordView n) := by
  intro p q he
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst he)
  · exact Bitset.encode_injective (congrArg Prod.snd he)

private def sameCanonical (p : GuardDescriptor × GuardDescriptor) : Bool :=
  sameRecords (view p.1.normalize).2 (view p.2.normalize).2

private theorem sameCanonical_polyTime : ComputableInPolyTime sameCanonical
    (encPair DescriptorValidation.descriptorEncoding DescriptorValidation.descriptorEncoding) encBool := by
  have hrecords := (snd (encList encNat) (encList recordEncoding)).comp
    (view_polyTime.comp NormalizeMachine.normalize_polyTime)
  exact sameRecords_polyTime.comp ((hrecords.comp (fst _ _)).prod (hrecords.comp (snd _ _)))

private theorem sameCanonical_shared (D : List ℕ) (hD : D.Nodup)
    (left right : List (GuardRecord.Record D.length)) :
    sameCanonical (⟨D, hD, left⟩, ⟨D, hD, right⟩) = true ↔
      ∀ i : Fin D.length,
        (GuardDescriptor.mk D hD left).normalize.guards i =
          (GuardDescriptor.mk D hD right).normalize.guards i := by
  let a : GuardDescriptor := ⟨D, hD, left⟩
  let b : GuardDescriptor := ⟨D, hD, right⟩
  rw [sameCanonical, sameRecords_iff]
  change (a.normalize.records.map recordView).toFinset =
    (b.normalize.records.map recordView).toFinset ↔ _
  have hmap (records : List (GuardRecord.Record D.length)) :
      (records.map recordView).toFinset = records.toFinset.image recordView := by
    ext p
    simp
  rw [hmap, hmap, (Finset.image_injective recordView_injective).eq_iff]
  constructor
  · intro he i
    ext A
    rw [GuardDescriptor.mem_guards, GuardDescriptor.mem_guards]
    simpa only [List.mem_toFinset] using Iff.of_eq (congrArg (fun records => (i, A) ∈ records) he)
  · intro he
    ext p
    simp only [List.mem_toFinset]
    rcases p with ⟨j, A⟩
    change (j, A) ∈ a.normalize.records ↔ (j, A) ∈ b.normalize.records
    rw [← a.normalize.mem_guards j A, ← b.normalize.mem_guards j A]
    exact Iff.of_eq (congrArg (fun guards => A ∈ guards) (he j))

private def emptyDescriptor : GuardDescriptor := ⟨[], by simp, []⟩

private def readData (data : Data) : GuardDescriptor :=
  (GuardDescriptor.decode (encodeData data)).getD emptyDescriptor

private theorem readData_polyTime : ComputableInPolyTime readData dataEncoding DescriptorValidation.descriptorEncoding :=
  (DescriptorValidation.decode_polyTime.comp encodeData_polyTime).optionGetDWithInput (const emptyDescriptor)

private theorem readData_view (D : List ℕ) (hD : D.Nodup) (records : List (GuardRecord.Record D.length)) :
    readData (D, records.map recordView) = ⟨D, hD, records⟩ := by
  change readData (view (GuardDescriptor.mk D hD records)) = _
  simp only [readData, encodeData_view, GuardDescriptor.decode_encode, Option.getD_some]

private def checkData (p : Data × Data) : Bool := sameCanonical (readData p.1, readData p.2)

private theorem checkData_polyTime : ComputableInPolyTime checkData
    (encPair dataEncoding dataEncoding) encBool :=
  sameCanonical_polyTime.comp ((readData_polyTime.comp (fst _ _)).prod (readData_polyTime.comp (snd _ _)))

private def dictionary (p : Reset.Term ℕ × Reset.Term ℕ) : List ℕ := ResetEquation.labels p.1 p.2

private theorem dictionary_polyTime : ComputableInPolyTime dictionary
    (encPair TermMachine.termEncoding TermMachine.termEncoding) (encList encNat) :=
  TermSupport.dedup_polyTime.comp (listAppend' (TermSupport.labels_polyTime.comp (fst _ _))
    (TermSupport.labels_polyTime.comp (snd _ _)))

private def checkTerms (p : Reset.Term ℕ × Reset.Term ℕ) : Bool :=
  let D := dictionary p
  let left := (GuardCompression.compressAll D (GuardExtraction.collect p.1).2).getD []
  let right := (GuardCompression.compressAll D (GuardExtraction.collect p.2).2).getD []
  checkData ((D, left), (D, right))

set_option maxHeartbeats 800000 in
private theorem checkTerms_polyTime : ComputableInPolyTime checkTerms
    (encPair TermMachine.termEncoding TermMachine.termEncoding) encBool := by
  have hl := (snd encNat (encList GuardExtraction.entryEncoding)).comp
    (GuardExtraction.collect_polyTime.comp (fst TermMachine.termEncoding TermMachine.termEncoding))
  have hr := (snd encNat (encList GuardExtraction.entryEncoding)).comp
    (GuardExtraction.collect_polyTime.comp (snd TermMachine.termEncoding TermMachine.termEncoding))
  have hleft := (GuardCompression.compressAll_polyTime.comp (dictionary_polyTime.prod hl)).optionGetDWithInput (const [])
  have hright := (GuardCompression.compressAll_polyTime.comp (dictionary_polyTime.prod hr)).optionGetDWithInput (const [])
  exact checkData_polyTime.comp ((dictionary_polyTime.prod hleft).prod (dictionary_polyTime.prod hright))

private theorem checkTerms_eq (p : Reset.Term ℕ × Reset.Term ℕ) : checkTerms p = ResetEquation.check p.1 p.2 := by
  let D := ResetEquation.labels p.1 p.2
  have hD : D.Nodup := ResetEquation.labels_nodup p.1 p.2
  have hscover : p.1.varFinset ⊆ D.toFinset := by
    rw [ResetEquation.labels_toFinset]
    exact Finset.subset_union_left
  have htcover : p.2.varFinset ⊆ D.toFinset := by
    rw [ResetEquation.labels_toFinset]
    exact Finset.subset_union_right
  obtain ⟨left, hl, _, hs⟩ := SupportIndex.compress_guardEntries_of_cover p.1 D hD hscover
  obtain ⟨right, hr, _, ht⟩ := SupportIndex.compress_guardEntries_of_cover p.2 D hD htcover
  have hleft : GuardCompression.compressAll D (GuardExtraction.collect p.1).2 = some (left.map recordView) := by
    rw [GuardCompression.compressAll_view, GuardExtraction.collect_entries, hl]
    rfl
  have hright : GuardCompression.compressAll D (GuardExtraction.collect p.2).2 = some (right.map recordView) := by
    rw [GuardCompression.compressAll_view, GuardExtraction.collect_entries, hr]
    rfl
  unfold checkTerms
  change checkData
    ((D, (GuardCompression.compressAll D (GuardExtraction.collect p.1).2).getD []),
      (D, (GuardCompression.compressAll D (GuardExtraction.collect p.2).2).getD [])) = _
  rw [hleft, hright]
  simp only [Option.getD_some, checkData, readData_view D hD]
  apply Bool.eq_iff_iff.mpr
  rw [sameCanonical_shared D hD, ResetEquation.check_eq_true]
  exact ResetEquation.normalized_equal_iff D hD p.1 p.2 left right hs ht (by
    rw [ResetEquation.labels_toFinset])

/-- Complete reset equality on original trees, using a shared actual support
and set comparison of normalized guards, has a polynomial-time machine. -/
@[fun_prop] theorem check_polyTime : ComputableInPolyTime
    (fun p : Reset.Term ℕ × Reset.Term ℕ => ResetEquation.check p.1 p.2)
    (encPair TermMachine.termEncoding TermMachine.termEncoding) encBool := by
  convert checkTerms_polyTime using 1
  funext p
  exact (checkTerms_eq p).symm


private def checkPair (p : List Bool × List Bool) : Bool :=
  ([p.1, p.2].mapM TermCode.decode).elim false fun terms =>
    ResetEquation.check (terms.getD 0 (.var 0)) (terms.getD 1 (.var 0))

set_option maxHeartbeats 800000 in
private theorem checkPair_polyTime : ComputableInPolyTime checkPair
    (encPair encBits encBits) encBool := by
  let input := encPair encBits encBits
  have hlist := cons' (fst encBits encBits) (cons' (snd encBits encBits) (const []))
  have hdecode := mapMWithInput_polyTime (f := fun (_ : List Bool × List Bool) word => TermCode.decode word)
    hlist (TermMachine.decode_polyTime.comp (snd input encBits)) (.var 0)
  have hterms := snd input (encList TermMachine.termEncoding)
  have hleft := listGetDWithInput hterms (const 0) (.var 0)
  have hright := listGetDWithInput hterms (const 1) (.var 0)
  have hbody := check_polyTime.comp (hleft.prod hright)
  exact hdecode.optionElimWithInput
    (encC := encBool) (body := fun (_ : List Bool × List Bool) (terms : List (Reset.Term ℕ)) =>
      ResetEquation.check (terms.getD 0 (.var 0)) (terms.getD 1 (.var 0))) (const false) hbody

/-- The complete original binary equation language is decided in polynomial
time, including pair framing, both tree decoders and malformed-input rejection. -/
@[fun_prop] theorem checkWord_polyTime : ComputableInPolyTime ResetEquation.checkWord encBits encBool := by
  have h := Framing.unpair_polyTime.optionElimWithInput
    (body := fun (_ : List Bool) p => checkPair p) (const false)
    (checkPair_polyTime.comp (snd encBits (encPair encBits encBits)))
  convert h using 1
  funext word
  unfold ResetEquation.checkWord
  cases hp : Words.unpair? word with
  | none => rfl
  | some p =>
    rcases p with ⟨left, right⟩
    simp only [Option.elim_some, checkPair]
    cases hl : TermCode.decode left <;> cases hr : TermCode.decode right <;>
      simp [List.mapM_cons, hl, hr]

end KFOL.Complexity.ResetEquality
