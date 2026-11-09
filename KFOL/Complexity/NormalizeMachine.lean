module

public import KFOL.Complexity.RawRecords

/-! # Native polynomial-time complete binary descriptor normalization -/

@[expose] public section

namespace KFOL.Complexity.NormalizeMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms
open KFOL.Complexity.RawRecords

private def subset (a b : List Bool) : Bool := (GuardWords.subsetWord a b).headD false

private theorem subset_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool => subset p.1 p.2) (encPair encBits encBits) encBool := by
  have hargs : ComputableInPolyTime
      (fun p : List Bool × List Bool => fun i : Fin 2 => if i = 0 then p.1 else p.2)
      (encPair encBits encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    by_cases hi : i = 0
    · simp only [hi, ite_true]
      exact fst _ _
    · simp only [hi, ite_false]
      exact snd _ _
  have hscan := GuardSubset.subsetFn_polyTime.comp hargs
  have h := (headD (encA := encBool) (encL := encBits) false).comp hscan
  exact h

private theorem subset_encode {n : ℕ} (A B : Finset (Fin n)) :
    subset (Bitset.encode A) (Bitset.encode B) = decide (A ⊆ B) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  have h := GuardWords.subsetWord_encode A B
  simpa only [subset, GuardWords.subsetWord, List.headD_cons, List.cons.injEq, and_true] using h

private def passes (p q : Record) : Bool :=
  if q.1 = p.1 then if subset q.2 p.2 then subset p.2 q.2 else true else true

private theorem passes_polyTime : ComputableInPolyTime
    (fun p : Record × Record => passes p.1 p.2) (encPair recordEncoding recordEncoding) encBool := by
  let input := encPair recordEncoding recordEncoding
  have hp : ComputableInPolyTime (fun p : Record × Record => p.1.1) input encNat := by fun_prop
  have hq : ComputableInPolyTime (fun p : Record × Record => p.2.1) input encNat := by fun_prop
  have ha : ComputableInPolyTime (fun p : Record × Record => p.1.2) input encBits := by fun_prop
  have hb : ComputableInPolyTime (fun p : Record × Record => p.2.2) input encBits := by fun_prop
  have heq := decide_eq' hq hp
  have hqp := subset_polyTime.comp (hb.prod ha)
  have hpq := subset_polyTime.comp (ha.prod hb)
  have h := heq.ite (hqp.ite hpq (const true)) (const true)
  convert h using 1
  funext p
  by_cases hi : p.2.1 = p.1.1 <;> simp [passes, hi]

private theorem passes_view {n : ℕ} (p q : GuardRecord.Record n) :
    passes (recordView p) (recordView q) = decide (q.1 = p.1 → q.2 ⊆ p.2 → p.2 ⊆ q.2) := by
  simp only [passes, recordView, subset_encode, Fin.val_inj]
  split_ifs <;> simp_all

/-- Keep precisely the minimal prerequisites in a raw native record list. -/
private def normalizeRecords (records : List Record) : List Record :=
  records.filter (fun p => records.all (passes p))

private theorem normalizeRecords_polyTime : ComputableInPolyTime normalizeRecords
    (encList recordEncoding) (encList recordEncoding) := by
  let input := encPair (encList recordEncoding) recordEncoding
  have hrecords : ComputableInPolyTime (fun p : List Record × Record => p.1)
      input (encList recordEncoding) := fst _ _
  have hp : ComputableInPolyTime (fun p : (List Record × Record) × Record => p.1.2)
      (encPair input recordEncoding) recordEncoding := by fun_prop
  have hq : ComputableInPolyTime (fun p : (List Record × Record) × Record => p.2)
      (encPair input recordEncoding) recordEncoding := snd _ _
  have htest := passes_polyTime.comp (hp.prod hq)
  have hall := allWithInput (test := fun (p : List Record × Record) (q : Record) => passes p.2 q) hrecords htest
  exact filterWithInput (test := fun (records : List Record) (p : Record) => records.all (passes p)) id' hall

private theorem normalizeRecords_view (d : GuardDescriptor) :
    normalizeRecords (d.records.map recordView) = d.normalize.records.map recordView := by
  have hpred (p : GuardRecord.Record d.labels.length) :
      (d.records.map recordView).all (passes (recordView p)) =
        decide (∀ q ∈ d.records, q.1 = p.1 → q.2 ⊆ p.2 → p.2 ⊆ q.2) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, Function.comp_def, passes_view, decide_eq_true_eq]
  change (d.records.map recordView).filter _ =
    (d.records.filter (fun p => decide (∀ q ∈ d.records, q.1 = p.1 → q.2 ⊆ p.2 → p.2 ⊆ q.2))).map recordView
  rw [List.filter_map]
  simp only [Function.comp_def, hpred]

private def normalizeData (data : Data) : Data := (data.1, normalizeRecords data.2)

private theorem normalizeData_polyTime : ComputableInPolyTime normalizeData dataEncoding dataEncoding :=
  (fst _ _).prod (normalizeRecords_polyTime.comp (snd _ _))

private theorem normalizeData_view (d : GuardDescriptor) : normalizeData (view d) = view d.normalize := by
  change (d.labels, normalizeRecords (d.records.map recordView)) = _
  rw [normalizeRecords_view]
  rfl

/-- The actual dependent descriptor normalizer is polynomial-time under
its existing complete binary serialization. Every record comparison and
all captured input data are charged by the native machine calculus. -/
@[fun_prop] theorem normalize_polyTime : ComputableInPolyTime GuardDescriptor.normalize
    DescriptorValidation.descriptorEncoding DescriptorValidation.descriptorEncoding := by
  have h := encodeData_polyTime.comp (normalizeData_polyTime.comp view_polyTime)
  apply h.of_enc_eq
  intro d
  change GuardDescriptor.encode d.normalize = encodeData (normalizeData (view d))
  rw [normalizeData_view, encodeData_view]

/-- Complete external normalization, including validation and malformed-input
rejection, has one deterministic polynomial-time machine on original bits. -/
@[fun_prop] theorem normalizeWord_polyTime : ComputableInPolyTime GuardDescriptor.normalizeWord
    encBits (encOption encBits) := by
  have hencode : ComputableInPolyTime GuardDescriptor.encode
      DescriptorValidation.descriptorEncoding encBits := .of_eq (fun _ => rfl)
  have hnormal := (hencode.comp normalize_polyTime).comp
    (snd encBits DescriptorValidation.descriptorEncoding)
  have h := DescriptorValidation.decode_polyTime.optionMapWithInput
    (f := fun (_ : List Bool) (d : GuardDescriptor) => GuardDescriptor.encode d.normalize) hnormal
  convert h using 1
  funext word
  unfold GuardDescriptor.normalizeWord
  cases GuardDescriptor.decode word <;> rfl

end KFOL.Complexity.NormalizeMachine
