module

public import KFOL.Algorithms.TermCode
public import KFOL.Reset.Realizability

/-! # Complete binary descriptors and their semantic realizability recognizer -/

@[expose] public section

namespace KFOL.Algorithms.GuardDescriptor

open _root_.Complexity

@[simp] theorem decode_encode (d : GuardDescriptor) : decode (encode d) = some d := by
  cases d with
  | mk labels distinct records => simp [decode, encode, distinct]

theorem encode_of_decode {word : List Bool} {d : GuardDescriptor}
    (h : decode word = some d) : encode d = word := by
  unfold decode at h
  obtain ⟨⟨dict, stream⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨labels, hl, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hd =>
    obtain ⟨records, hr, he⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj he
    unfold encode
    rw [LabelDictionary.encode_of_decode hl, GuardRecord.encodeList_of_decodeList hr]
    exact (eq_pair_of_unpair?_eq_some hp).symm
  next => cases h

theorem decode_eq_some_iff (word : List Bool) (d : GuardDescriptor) :
    decode word = some d ↔ word = encode d :=
  ⟨fun h => (encode_of_decode h).symm, fun h => h ▸ decode_encode d⟩

theorem encode_injective : Function.Injective encode := by
  intro d e h
  have he := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using he

theorem length_encode (d : GuardDescriptor) :
    (encode d).length = 4 * (d.labels.map Nat.size).sum + 4 * d.labels.length + 2 +
      (GuardRecord.encodeList d.records).length := by
  rw [encode, pair_length, LabelDictionary.length_encode]
  omega

theorem width_le_length_encode (d : GuardDescriptor) : d.labels.length ≤ (encode d).length := by
  rw [length_encode]
  omega

theorem records_le_length_encode (d : GuardDescriptor) :
    d.records.length ≤ (encode d).length := by
  have hb : d.records.length ≤ (GuardRecord.encodeList d.records).length := by
    rw [GuardRecord.length_encodeList]
    have h := List.sum_le_sum (l := d.records) (f := fun _ => 1)
      (g := fun r => 2 * d.labels.length + 4 * r.1.val.size + 6) (fun _ _ => by omega)
    simpa using h
  rw [length_encode]
  omega

@[simp] theorem mem_guards (d : GuardDescriptor) (j : Fin d.labels.length)
    (A : Finset (Fin d.labels.length)) : A ∈ d.guards j ↔ (j, A) ∈ d.records := by
  simp only [guards, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨⟨k, B⟩, ⟨hp, hk⟩, hB⟩
    dsimp at hk hB
    subst k
    subst B
    exact hp
  · intro hp
    exact ⟨(j, A), ⟨hp, rfl⟩, rfl⟩

/-- Distinct dictionary names permit exact expansion and recompression of
every record, including repeated occurrences and unused dictionary positions. -/
theorem recompress_records (d : GuardDescriptor) :
    (d.records.map (fun r => (d.labels.get r.1, SupportIndex.expand d.labels r.2))).mapM
      (SupportIndex.compressEntry d.labels) = some d.records := by
  have hi (i : Fin d.labels.length) :=
    (SupportIndex.locate_eq_some_iff d.labels d.distinct (d.labels.get i) i).mpr rfl
  have entry (r : GuardRecord.Record d.labels.length) :
      SupportIndex.compressEntry d.labels (d.labels.get r.1, SupportIndex.expand d.labels r.2) =
        some r := by
    unfold SupportIndex.compressEntry
    rw [hi]
    change some (r.1, SupportIndex.compress d.labels (SupportIndex.expand d.labels r.2)) = some r
    rw [SupportIndex.compress_expand d.labels d.distinct]
  induction d.records with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.mapM_cons, entry, ih]
    rfl

/-- Guard enabling uses precisely the already machine-certified subset
primitive on the listed records. Unlisted outputs have no enabling guard. -/
theorem enabled_iff_subsetWord (d : GuardDescriptor) (r j : Fin d.labels.length)
    (B : Finset (Fin d.labels.length)) :
    (d.table r).Enabled (B : Set (Fin d.labels.length)) j ↔
      ∃ A, (j, A) ∈ d.records ∧
        GuardWords.subsetWord (Bitset.encode A) (Bitset.encode B) = [true] := by
  simp only [Reset.GuardTable.Enabled, table, mem_guards, GuardWords.subsetWord_encode]
  rfl

/-- The mathematical table size is exactly the number of distinct records.
The input list may contain repeated records, without inflating realizability. -/
theorem entryCount_table (d : GuardDescriptor) (r : Fin d.labels.length) :
    (d.table r).entryCount = d.records.toFinset.card := by
  have hf := Finset.card_eq_sum_card_fiberwise
    (s := d.records.toFinset) (t := (Finset.univ : Finset (Fin d.labels.length)))
    (f := Prod.fst) (fun _ _ => Finset.mem_univ _)
  change (∑ j, (d.guards j).card) = _
  rw [hf]
  apply Finset.sum_congr rfl
  intro j _
  unfold guards
  apply Finset.card_image_of_injOn
  rintro ⟨k, A⟩ hk ⟨l, B⟩ hl he
  have hkj := (Finset.mem_filter.mp hk).2
  have hlj := (Finset.mem_filter.mp hl).2
  exact Prod.ext (hkj.trans hlj.symm) he

theorem entryCount_table_le (d : GuardDescriptor) (r : Fin d.labels.length) :
    (d.table r).entryCount ≤ d.records.length := by
  rw [entryCount_table]
  exact List.toFinset_card_le _

theorem root?_eq_some_of_wellFormed (d : GuardDescriptor) (r : Fin d.labels.length)
    (h : (d.table r).WellFormed) : d.root? = some r := by
  have hm : (r, ∅) ∈ d.records := (d.mem_guards r ∅).mp (by
    change ∅ ∈ (d.table r).guards r
    have hr : (d.table r).guards r = {∅} := h.2.1
    rw [hr]
    exact Finset.mem_singleton_self _)
  unfold root?
  cases he : d.records.find? (fun p => decide (p.2 = ∅)) with
  | none =>
    have hn := List.find?_eq_none.mp he (r, ∅) hm
    simp at hn
  | some p =>
    have hp := List.mem_of_find?_eq_some he
    have hp0 : decide (p.2 = ∅) = true := List.find?_some
      (p := fun q : GuardRecord.Record d.labels.length => decide (q.2 = ∅)) (a := p) he
    have hA : p.2 = ∅ := of_decide_eq_true hp0
    have hr : p.1 = r := h.2.2.1 p.1 (by
      change ∅ ∈ d.guards p.1
      rw [mem_guards, ← hA]
      exact hp)
    simp only [Option.map_some, hr]

/-- Root selection is justified by the unique empty-guard condition, not by
a convention that the first dictionary position must be the root. -/
theorem check_eq_true (d : GuardDescriptor) : d.check = true ↔
    ∃ r : Fin d.labels.length, (d.table r).WellFormed := by
  constructor
  · intro h
    unfold check at h
    cases hr : d.root? with
    | none => simp [hr] at h
    | some r =>
      rw [hr] at h
      exact ⟨r, (d.table r).check_eq_true.mp h⟩
  · rintro ⟨r, h⟩
    simp only [check, d.root?_eq_some_of_wellFormed r h]
    exact (d.table r).check_eq_true.mpr h

/-- The descriptor checker certifies an actual primitive tree with the
existing compact bound. Nonminimal lists are not silently normalized. -/
theorem check_iff_bounded_realization (d : GuardDescriptor) : d.check = true ↔
    ∃ t : Reset.Term (Fin d.labels.length), t.table = d.guards ∧
      t.size ≤ 1 + 2 * d.labels.length * d.records.length := by
  constructor
  · intro hc
    obtain ⟨r, hw⟩ := d.check_eq_true.mp hc
    obtain ⟨t, _, ht, hb⟩ := (d.table r).exists_term_bounded hw
    refine ⟨t, ht, hb.trans ?_⟩
    simpa only [Fintype.card_fin] using Nat.add_le_add_left
      (Nat.mul_le_mul_left (2 * d.labels.length) (d.entryCount_table_le r)) 1
  · rintro ⟨t, ht, _⟩
    apply d.check_eq_true.mpr
    refine ⟨t.root, ?_⟩
    change (Reset.GuardTable.mk t.root d.guards).WellFormed
    rw [← ht]
    exact t.guardTable_wellFormed

/-- Malformed external words are rejected. Successful recognition yields
actual syntax, with a size bound measured in the original descriptor bits. -/
theorem recognize_eq_true (word : List Bool) : recognize word = true ↔
    ∃ (d : GuardDescriptor) (t : Reset.Term (Fin d.labels.length)),
      word = encode d ∧ t.table = d.guards ∧
      t.size ≤ 1 + 2 * word.length * word.length := by
  constructor
  · intro h
    unfold recognize at h
    cases hd : decode word with
    | none => simp [hd] at h
    | some d =>
      rw [hd] at h
      obtain ⟨t, ht, hb⟩ := d.check_iff_bounded_realization.mp h
      have he := (decode_eq_some_iff word d).mp hd
      refine ⟨d, t, he, ht, hb.trans ?_⟩
      rw [he]
      exact Nat.add_le_add_left (Nat.mul_le_mul
        (Nat.mul_le_mul_left 2 d.width_le_length_encode) d.records_le_length_encode) 1
  · rintro ⟨d, t, he, ht, _⟩
    rw [he]
    simp only [recognize, decode_encode]
    apply d.check_eq_true.mpr
    refine ⟨t.root, ?_⟩
    change (Reset.GuardTable.mk t.root d.guards).WellFormed
    rw [← ht]
    exact t.guardTable_wellFormed

/-- The binary frontend always produces a valid complete descriptor, even
when its raw guards still require minimization before semantic recognition. -/
theorem decode_extraction {word output : List Bool} (h : TermCode.extract word = some output) :
    ∃ (d : GuardDescriptor) (t : Reset.Term ℕ), decode output = some d ∧
      TermCode.decode word = some t ∧ d.labels = SupportIndex.labels t ∧
      d.records.map (fun r => (d.labels.get r.1, SupportIndex.expand d.labels r.2)) =
        t.guardEntries := by
  have hd : TermCode.decode word ≠ none := by
    intro hn
    have he := (TermCode.extract_eq_none_iff word).mpr hn
    rw [he] at h
    cases h
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hd
  obtain ⟨records, he, _, hr, _⟩ := TermCode.extract_spec ht
  have ho := Option.some.inj (he.symm.trans h)
  let d : GuardDescriptor := ⟨SupportIndex.labels t, SupportIndex.labels_nodup t, records⟩
  refine ⟨d, t, ?_, ht, rfl, hr⟩
  rw [← ho]
  exact decode_encode d

end KFOL.Algorithms.GuardDescriptor
