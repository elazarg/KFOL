module

public import KFOL.Algorithms.Framing
public import KFOL.Algorithms.SupportIndex

/-! # Exact binary guard records and polynomial encoded output sizes -/

@[expose] public section

namespace KFOL.Algorithms

open _root_.KFOL.Words

namespace GuardRecord

@[simp] theorem decode_encode {n : ℕ} (r : Record n) : decode n (encode r) = some r := by
  simp [decode, encode, r.1.isLt]

theorem encode_of_decode {n : ℕ} {word : List Bool} {r : Record n}
    (h : decode n word = some r) : encode r = word := by
  unfold decode at h
  obtain ⟨⟨index, payload⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  next hlt =>
    obtain ⟨A, hA, he⟩ := Option.bind_eq_some_iff.mp h
    have he := Option.some.inj he
    subst r
    have hi := (BinaryNatCode.decode?_eq_some_iff index j).mp hj
    have hbits := (Bitset.decode_eq_some_iff payload A).mp hA
    unfold encode
    rw [← hi, ← hbits]
    exact (eq_pair_of_unpair?_eq_some hp).symm
  next => cases h

theorem decode_eq_some_iff {n : ℕ} (word : List Bool) (r : Record n) :
    decode n word = some r ↔ word = encode r :=
  ⟨fun h => (encode_of_decode h).symm, fun h => h ▸ decode_encode r⟩

@[simp] theorem length_encode {n : ℕ} (r : Record n) :
    (encode r).length = 2 * r.1.val.size + 2 + n := by
  simp [encode]

theorem length_encode_le {n : ℕ} (r : Record n) :
    (encode r).length ≤ n + 2 * n.size + 2 := by
  rw [length_encode]
  have h := Nat.size_le_size r.1.isLt.le
  omega

@[simp] theorem decodeList_encodeList {n : ℕ} (records : List (Record n)) :
    decodeList n (encodeList records) = some records := by
  unfold decodeList encodeList
  rw [undelimitBlocks_flatten_delimit]
  exact Framing.mapM_decode_encode encode (decode n) decode_encode records

theorem encodeList_of_decodeList {n : ℕ} {word : List Bool} {records : List (Record n)}
    (h : decodeList n word = some records) : encodeList records = word := by
  unfold decodeList at h
  obtain ⟨blocks, hb, hd⟩ := Option.bind_eq_some_iff.mp h
  have he := Framing.map_eq_of_mapM_decode encode (decode n)
    (fun _ _ hx => encode_of_decode hx) blocks records hd
  unfold encodeList
  rw [he]
  exact Framing.undelimitBlocks_sound hb

theorem decodeList_eq_some_iff {n : ℕ} (word : List Bool) (records : List (Record n)) :
    decodeList n word = some records ↔ word = encodeList records :=
  ⟨fun h => (encodeList_of_decodeList h).symm, fun h => h ▸ decodeList_encodeList records⟩

/-- Outer framing adds a constant overhead per record and doubles its fields
once; the table tail is not duplicated at every recursive level. -/
theorem length_encodeList {n : ℕ} (records : List (Record n)) :
    (encodeList records).length =
      (records.map (fun r => 2 * n + 4 * r.1.val.size + 6)).sum := by
  induction records with
  | nil => rfl
  | cons r records ih =>
    change (delimit (encode r) ++ encodeList records).length = _
    rw [List.length_append, delimit_length, length_encode, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem length_encodeList_le {n : ℕ} (records : List (Record n)) :
    (encodeList records).length ≤ records.length * (2 * n + 4 * n.size + 6) := by
  rw [length_encodeList]
  have h := List.sum_le_sum (l := records)
    (f := fun r => 2 * n + 4 * r.1.val.size + 6)
    (g := fun _ => 2 * n + 4 * n.size + 6) (fun r _ => by
      have hs := Nat.size_le_size r.1.isLt.le
      omega)
  simpa using h

theorem length_encodeList_linear {n : ℕ} (records : List (Record n)) :
    (encodeList records).length ≤ 6 * records.length * (n + 1) := by
  have hs : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have hc : 2 * n + 4 * n.size + 6 ≤ 6 * (n + 1) := by omega
  have hm := Nat.mul_le_mul_left records.length hc
  simpa only [Nat.mul_assoc, Nat.mul_left_comm records.length 6] using
    (length_encodeList_le records).trans hm

end GuardRecord

namespace LabelDictionary

@[simp] theorem decode_encode (labels : List ℕ) : decode (encode labels) = some labels := by
  unfold decode encode
  rw [undelimitBlocks_flatten_delimit]
  exact Framing.mapM_decode_encode BinaryNatCode.encode BinaryNatCode.decode?
    BinaryNatCode.decode?_encode labels

theorem encode_of_decode {word : List Bool} {labels : List ℕ}
    (h : decode word = some labels) : encode labels = word := by
  unfold decode at h
  obtain ⟨blocks, hb, hd⟩ := Option.bind_eq_some_iff.mp h
  have he := Framing.map_eq_of_mapM_decode BinaryNatCode.encode BinaryNatCode.decode?
    (fun b j hx => ((BinaryNatCode.decode?_eq_some_iff b j).mp hx).symm) blocks labels hd
  unfold encode
  rw [he]
  exact Framing.undelimitBlocks_sound hb

theorem decode_eq_some_iff (word : List Bool) (labels : List ℕ) :
    decode word = some labels ↔ word = encode labels :=
  ⟨fun h => (encode_of_decode h).symm, fun h => h ▸ decode_encode labels⟩

theorem length_encode (labels : List ℕ) :
    (encode labels).length = 2 * (labels.map Nat.size).sum + 2 * labels.length := by
  rw [encode, Framing.length_frames]
  simp only [List.map_map, BinaryNatCode.length_encode, List.length_map, Function.comp_def]

/-- Each original variable label is serialized only once in the dictionary. -/
theorem length_encode_support_le (t : Reset.Term ℕ) :
    (encode (SupportIndex.labels t)).length ≤
      2 * (t.guardEntries.map (fun p => p.1.size)).sum + 2 * t.leafCount := by
  rw [length_encode]
  have hs := SupportIndex.sum_labels_le t Nat.size
  have hl := SupportIndex.length_labels_le t
  omega

end LabelDictionary

/-- The term's own collector and dictionary provide real encodable records,
whose decoded expansion recovers every raw occurrence and its prerequisites. -/
theorem indexed_guard_records (t : Reset.Term ℕ) :
    ∃ records : List (GuardRecord.Record (SupportIndex.labels t).length),
      t.guardEntries.mapM (SupportIndex.compressEntry (SupportIndex.labels t)) = some records ∧
      records.length = t.leafCount ∧
      records.map (fun r => ((SupportIndex.labels t).get r.1,
        SupportIndex.expand (SupportIndex.labels t) r.2)) = t.guardEntries ∧
      GuardRecord.decodeList (SupportIndex.labels t).length (GuardRecord.encodeList records) =
        some records ∧
      (GuardRecord.encodeList records).length ≤ 6 * t.leafCount * (t.leafCount + 1) := by
  obtain ⟨records, hr, hlen, he⟩ := SupportIndex.compress_guardEntries t
  refine ⟨records, hr, hlen, he, GuardRecord.decodeList_encodeList records, ?_⟩
  have hb := GuardRecord.length_encodeList_linear records
  rw [hlen] at hb
  exact hb.trans (Nat.mul_le_mul_left (6 * t.leafCount)
    (Nat.add_le_add_right (SupportIndex.length_labels_le t) 1))

end KFOL.Algorithms
