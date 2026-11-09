module

public import KFOL.Complexity.ReachMachine

/-! # Complete native polynomial-time realizability recognition -/

@[expose] public section

namespace KFOL.Complexity.RecognitionMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Algorithms KFOL.Complexity.RawRecords

private def zero (word : List Bool) : Bool :=
  ReachMachine.subset word (List.replicate word.length false)

private theorem zero_polyTime : ComputableInPolyTime zero encBits encBool :=
  ReachMachine.subset_polyTime.comp (id'.prod ((bitsReplicate false).comp length_bits))

private theorem zero_encode {n : ℕ} (A : Finset (Fin n)) :
    zero (Bitset.encode A) = decide (A = ∅) := by
  simp only [zero, Bitset.length_encode, ReachMachine.empty_encode, ReachMachine.subset_encode,
    Finset.subset_empty]

private def selfFree (p : Record) : Bool :=
  !(p.2.getD (min p.2.length p.1) false)

private theorem selfFree_polyTime : ComputableInPolyTime selfFree recordEncoding encBool := by
  have hword := snd encNat encBits
  have hindex := binary_min_unary' (length_bits.comp hword) (fst encNat encBits)
  exact bool_not.comp (bitsGetDWithInput hword hindex false)

private theorem selfFree_view {n : ℕ} (p : GuardRecord.Record n) :
    selfFree (recordView p) = decide (p.1 ∉ p.2) := by
  have hm : min n p.1.val = p.1.val := Nat.min_eq_right (Nat.le_of_lt p.1.isLt)
  simp only [selfFree, recordView, Bitset.length_encode, hm, List.getD_eq_getElem?_getD]
  change (!GuardWords.readBit (Bitset.encode p.2) p.1.val) = _
  rw [Bitset.read_encode]
  simp

private def compatible (p q : Record) : Bool :=
  if p.1 = q.1 then if ReachMachine.subset p.2 q.2 then decide (p.2 = q.2) else true else true

private theorem compatible_polyTime : ComputableInPolyTime
    (fun p : Record × Record => compatible p.1 p.2) (encPair recordEncoding recordEncoding) encBool := by
  let input := encPair recordEncoding recordEncoding
  have hp : ComputableInPolyTime (fun p : Record × Record => p.1.1) input encNat := by fun_prop
  have hq : ComputableInPolyTime (fun p : Record × Record => p.2.1) input encNat := by fun_prop
  have ha : ComputableInPolyTime (fun p : Record × Record => p.1.2) input encBits := by fun_prop
  have hb : ComputableInPolyTime (fun p : Record × Record => p.2.2) input encBits := by fun_prop
  have h := (decide_eq' hp hq).ite
    ((ReachMachine.subset_polyTime.comp (ha.prod hb)).ite (decide_eq' ha hb) (const true)) (const true)
  convert h using 1
  funext p
  by_cases hi : p.1.1 = p.2.1 <;> simp [compatible, hi]

private theorem compatible_view {n : ℕ} (p q : GuardRecord.Record n) :
    compatible (recordView p) (recordView q) =
      decide (p.1 = q.1 → p.2 ⊆ q.2 → p.2 = q.2) := by
  simp only [compatible, recordView, ReachMachine.subset_encode, Bitset.encode_injective.eq_iff, Fin.val_inj]
  split_ifs <;> simp_all

private def rootGate (root : ℕ) (p : Record) : Bool :=
  if p.1 = root then zero p.2 else !zero p.2

private theorem rootGate_polyTime : ComputableInPolyTime
    (fun p : ℕ × Record => rootGate p.1 p.2) (encPair encNat recordEncoding) encBool := by
  have hp : ComputableInPolyTime (fun p : ℕ × Record => p.2.1) (encPair encNat recordEncoding) encNat := by fun_prop
  have hr := fst encNat recordEncoding
  have hw : ComputableInPolyTime (fun p : ℕ × Record => p.2.2) (encPair encNat recordEncoding) encBits := by fun_prop
  have hz := zero_polyTime.comp hw
  have h := (decide_eq' hp hr).ite hz (bool_not.comp hz)
  convert h using 1
  funext p
  by_cases hi : p.2.1 = p.1 <;> simp [rootGate, hi]

private theorem rootGate_view {n : ℕ} (root : Fin n) (p : GuardRecord.Record n) :
    rootGate root.val (recordView p) = decide (p.1 = root ↔ p.2 = ∅) := by
  simp only [rootGate, recordView, zero_encode, Fin.val_inj]
  split_ifs <;> simp_all

private def goodRecord (records : List Record) (root : ℕ) (p : Record) : Bool :=
  rootGate root p && selfFree p && ReachMachine.constructible (records, p.2) &&
    records.all (compatible p)

private abbrev Candidate := List Record × ℕ
private abbrev candidateEncoding := encPair (encList recordEncoding) encNat

private theorem goodRecord_polyTime : ComputableInPolyTime
    (fun p : Candidate × Record => goodRecord p.1.1 p.1.2 p.2)
    (encPair candidateEncoding recordEncoding) encBool := by
  let input := encPair candidateEncoding recordEncoding
  have hroot : ComputableInPolyTime (fun p : Candidate × Record => p.1.2) input encNat := by fun_prop
  have hp := snd candidateEncoding recordEncoding
  have hrecords : ComputableInPolyTime (fun p : Candidate × Record => p.1.1) input (encList recordEncoding) := by fun_prop
  have hword : ComputableInPolyTime (fun p : Candidate × Record => p.2.2) input encBits := by fun_prop
  have hpinner : ComputableInPolyTime (fun p : (Candidate × Record) × Record => p.1.2)
      (encPair input recordEncoding) recordEncoding := by fun_prop
  have htest : ComputableInPolyTime
      (fun p : (Candidate × Record) × Record => compatible p.1.2 p.2)
      (encPair input recordEncoding) encBool :=
    compatible_polyTime.comp (hpinner.prod (snd _ _))
  have hall := allWithInput (test := fun (p : Candidate × Record) (q : Record) => compatible p.2 q) hrecords htest
  exact bool_and' (bool_and' (bool_and' (rootGate_polyTime.comp (hroot.prod hp))
    (selfFree_polyTime.comp hp)) (ReachMachine.constructible_polyTime.comp (hrecords.prod hword))) hall

private def candidate (records : List Record) (root : ℕ) : Bool :=
  records.all (goodRecord records root)

private theorem candidate_polyTime : ComputableInPolyTime
    (fun p : Candidate => candidate p.1 p.2) candidateEncoding encBool :=
  allWithInput (test := fun (p : Candidate) (q : Record) => goodRecord p.1 p.2 q)
    (fst _ _) goodRecord_polyTime

private def checkRecords (records : List Record) : Bool :=
  records.any (fun p => zero p.2 && candidate records p.1)

private theorem checkRecords_polyTime : ComputableInPolyTime checkRecords
    (encList recordEncoding) encBool := by
  have hword : ComputableInPolyTime (fun p : List Record × Record => p.2.2)
      (encPair (encList recordEncoding) recordEncoding) encBits := by fun_prop
  have houtput : ComputableInPolyTime (fun p : List Record × Record => p.2.1)
      (encPair (encList recordEncoding) recordEncoding) encNat := by fun_prop
  have h := bool_and' (zero_polyTime.comp hword)
    (candidate_polyTime.comp ((fst _ _).prod houtput))
  exact anyWithInput (test := fun (records : List Record) (p : Record) => zero p.2 && candidate records p.1) id' h


private theorem goodRecord_view (d : GuardDescriptor) (r : Fin d.labels.length)
    (p : GuardRecord.Record d.labels.length) :
    goodRecord (d.records.map recordView) r.val (recordView p) = true ↔
      (p.1 = r ↔ p.2 = ∅) ∧ p.1 ∉ p.2 ∧ (d.table r).Constructible p.2 ∧
        ∀ q ∈ d.records, p.1 = q.1 → p.2 ⊆ q.2 → p.2 = q.2 := by
  simp only [goodRecord, Bool.and_eq_true, rootGate_view, selfFree_view, decide_eq_true_eq,
    List.all_map, List.all_eq_true, Function.comp_def, compatible_view]
  simp only [recordView, ReachMachine.constructible_view d r]
  tauto

private theorem candidate_view (d : GuardDescriptor) (r : Fin d.labels.length) :
    candidate (d.records.map recordView) r.val = true ↔
      ∀ p ∈ d.records, (p.1 = r ↔ p.2 = ∅) ∧ p.1 ∉ p.2 ∧
        (d.table r).Constructible p.2 ∧
        ∀ q ∈ d.records, p.1 = q.1 → p.2 ⊆ q.2 → p.2 = q.2 := by
  simp only [candidate, List.all_map, List.all_eq_true, Function.comp_def, goodRecord_view]

private theorem wellFormed_iff_records (d : GuardDescriptor) (r : Fin d.labels.length) :
    (d.table r).WellFormed ↔ (r, ∅) ∈ d.records ∧
      ∀ p ∈ d.records, (p.1 = r ↔ p.2 = ∅) ∧ p.1 ∉ p.2 ∧
        (d.table r).Constructible p.2 ∧
        ∀ q ∈ d.records, p.1 = q.1 → p.2 ⊆ q.2 → p.2 = q.2 := by
  constructor
  · rintro ⟨ha, hr, hu, hs, hc⟩
    change (d.table r).guards r = {∅} at hr
    have hempty : (r, ∅) ∈ d.records := by
      rw [← d.mem_guards]
      change ∅ ∈ (d.table r).guards r
      rw [hr]
      exact Finset.mem_singleton_self _
    refine ⟨hempty, fun p hp => ?_⟩
    have hguard : p.2 ∈ (d.table r).guards p.1 := (d.mem_guards p.1 p.2).mpr hp
    refine ⟨⟨?_, ?_⟩, hs _ _ hguard, hc _ _ hguard, ?_⟩
    · intro he
      subst he
      rw [hr] at hguard
      exact Finset.mem_singleton.mp hguard
    · intro he
      apply hu
      simpa only [he] using hguard
    · intro q hq he hsub
      apply ha p.1 p.2 hguard q.2
      · rw [he]
        exact (d.mem_guards q.1 q.2).mpr hq
      · exact hsub
  · rintro ⟨he, h⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j A hA B hB hAB
      exact (h (j, A) ((d.mem_guards j A).mp hA)).2.2.2
        (j, B) ((d.mem_guards j B).mp hB) rfl hAB
    · ext A
      rw [Finset.mem_singleton]
      constructor
      · intro hA
        exact (h (r, A) ((d.mem_guards r A).mp hA)).1.mp rfl
      · intro hA
        subst A
        exact (d.mem_guards r ∅).mpr he
    · intro j hj
      exact (h (j, ∅) ((d.mem_guards j ∅).mp hj)).1.mpr rfl
    · intro j A hA
      exact (h (j, A) ((d.mem_guards j A).mp hA)).2.1
    · intro j A hA
      exact (h (j, A) ((d.mem_guards j A).mp hA)).2.2.1

private theorem checkRecords_view (d : GuardDescriptor) :
    checkRecords (d.records.map recordView) = d.check := by
  apply Bool.eq_iff_iff.mpr
  rw [GuardDescriptor.check_eq_true]
  simp only [checkRecords, List.any_map, List.any_eq_true, Function.comp_def,
    Bool.and_eq_true, recordView, zero_encode, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, he, hc⟩
    refine ⟨p.1, (wellFormed_iff_records d p.1).mpr ⟨?_, ?_⟩⟩
    · simpa only [← he, Prod.eta] using hp
    · exact (candidate_view d p.1).mp hc
  · rintro ⟨r, hr⟩
    obtain ⟨he, h⟩ := (wellFormed_iff_records d r).mp hr
    exact ⟨(r, ∅), he, rfl, (candidate_view d r).mpr h⟩

/-- The existing independent semantic checker has a polynomial-time machine
under the original complete descriptor serialization. -/
@[fun_prop] theorem check_polyTime : ComputableInPolyTime GuardDescriptor.check
    DescriptorValidation.descriptorEncoding encBool := by
  have hrecords := (snd (encList encNat) (encList recordEncoding)).comp view_polyTime
  have h := checkRecords_polyTime.comp hrecords
  convert h using 1
  funext d
  exact (checkRecords_view d).symm

/-- Complete external semantic recognition, including all parsing and all
malformed-input rejection, runs in deterministic polynomial time. -/
@[fun_prop] theorem recognize_polyTime : ComputableInPolyTime GuardDescriptor.recognize encBits encBool := by
  have hcheck := check_polyTime.comp (snd encBits DescriptorValidation.descriptorEncoding)
  have h := DescriptorValidation.decode_polyTime.optionMapWithInput
    (f := fun (_ : List Bool) (d : GuardDescriptor) => d.check) hcheck
  have hfalse := h.optionGetDWithInput (const false)
  convert hfalse using 1
  funext word
  unfold GuardDescriptor.recognize
  cases GuardDescriptor.decode word <;> rfl

end KFOL.Complexity.RecognitionMachine
