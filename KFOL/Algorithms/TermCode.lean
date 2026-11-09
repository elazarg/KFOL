module

public import KFOL.Algorithms.GuardRecord

/-! # Exact binary input trees and the executable guard-extraction frontend -/

@[expose] public section

namespace KFOL.Algorithms.TermCode

open _root_.KFOL.Words

@[simp] theorem encode_var (j : ℕ) :
    encode (.var j) = false :: delimit (BinaryNatCode.encode j) := rfl

@[simp] theorem encode_step (s t : Reset.Term ℕ) :
    encode (Reset.Term.step s t) = true :: (encode s ++ encode t) := rfl

/-- Bit size counts every syntax occurrence and every copy of a binary label. -/
theorem length_encode (t : Reset.Term ℕ) :
    (encode t).length = t.size + 2 * t.leafCount +
      2 * (t.guardEntries.map (fun p => p.1.size)).sum := by
  induction t using Reset.Term.induction_reset with
  | var j => simp [encode_var, Reset.Term.guardEntries_var]; omega
  | step s t hs ht =>
    simp only [encode_step, List.length_cons, List.length_append, hs, ht,
      Reset.Term.size_step, Reset.Term.leafCount_step, Reset.Term.guardEntries_step,
      List.map_append, List.map_map, Function.comp_def, List.sum_append]
    omega

theorem size_le_length_encode (t : Reset.Term ℕ) : t.size ≤ (encode t).length := by
  rw [length_encode]
  omega

theorem leafCount_le_length_encode (t : Reset.Term ℕ) : t.leafCount ≤ (encode t).length := by
  rw [length_encode]
  omega

/-- Size-bounded fuel suffices for any following suffix, which is returned
unchanged. The parser clock is independent of the numeric label values. -/
theorem parse_encode (t : Reset.Term ℕ) (rest : List Bool) (fuel : ℕ)
    (hf : t.size ≤ fuel) : parse fuel (encode t ++ rest) = some (t, rest) := by
  induction t using Reset.Term.induction_reset generalizing rest fuel with
  | var j =>
    cases fuel with
    | zero => simp at hf
    | succ fuel => simp [parse, encode_var]
  | step s t hs ht =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [Reset.Term.size_step] at hf
      simp only [encode_step, List.cons_append, List.append_assoc, parse]
      simp [hs (encode t ++ rest) fuel (by omega), ht rest fuel (by omega)]

/-- Every successful partial parse reconstructs its whole input exactly. -/
theorem encode_append_of_parse {fuel : ℕ} {word rest : List Bool} {t : Reset.Term ℕ}
    (h : parse fuel word = some (t, rest)) : encode t ++ rest = word := by
  induction fuel generalizing word rest t with
  | zero => cases h
  | succ fuel ih =>
    cases word with
    | nil => cases h
    | cons b word =>
      cases b with
      | false =>
        simp only [parse] at h
        obtain ⟨⟨name, tail⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        have hn := (BinaryNatCode.decode?_eq_some_iff name j).mp hj
        simp only [encode_var, List.cons_append, ← hn]
        exact congrArg (List.cons false) (eq_delimit_append_of_unpair?_eq_some hp).symm
      | true =>
        simp only [parse] at h
        obtain ⟨⟨s, tail⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨⟨u, suffix⟩, hu, he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        simp only [encode_step, List.cons_append, List.append_assoc, ih hu, ih hs]

/-- The syntax code is prefix-free: a valid tree followed by any nonempty
suffix is rejected by complete decoding. -/
theorem decode_encode_append (t : Reset.Term ℕ) (rest : List Bool) :
    decode (encode t ++ rest) = if rest.isEmpty then some t else none := by
  unfold decode
  rw [parse_encode t rest _ (by
    rw [List.length_append]
    exact (size_le_length_encode t).trans (Nat.le_add_right _ _))]
  rfl

@[simp] theorem decode_encode (t : Reset.Term ℕ) : decode (encode t) = some t := by
  simpa using decode_encode_append t []

theorem encode_of_decode {word : List Bool} {t : Reset.Term ℕ}
    (h : decode word = some t) : encode t = word := by
  unfold decode at h
  obtain ⟨⟨s, rest⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.isEmpty then some s else none) = some t at h
  split at h
  next hr =>
    have he := Option.some.inj h
    subst s
    have hr : rest = [] := List.isEmpty_iff.mp hr
    simpa only [hr, List.append_nil] using encode_append_of_parse hs
  next => cases h

theorem decode_eq_some_iff (word : List Bool) (t : Reset.Term ℕ) :
    decode word = some t ↔ word = encode t :=
  ⟨fun h => (encode_of_decode h).symm, fun h => h ▸ decode_encode t⟩

theorem encode_injective : Function.Injective encode := by
  intro s t h
  have he := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using he

/-- A successful parse consumes at least as many bits as syntax nodes. -/
theorem size_add_length_rest_le {fuel : ℕ} {word rest : List Bool} {t : Reset.Term ℕ}
    (h : parse fuel word = some (t, rest)) : t.size + rest.length ≤ word.length := by
  rw [← encode_append_of_parse h, List.length_append]
  exact Nat.add_le_add_right (size_le_length_encode t) _

/-- Binary dictionary size is already bounded by the original binary input. -/
theorem length_dictionary_le (t : Reset.Term ℕ) :
    (LabelDictionary.encode (SupportIndex.labels t)).length ≤ (encode t).length := by
  have hb := LabelDictionary.length_encode_support_le t
  rw [length_encode]
  omega

/-- Every valid original input produces its actual compressed guard stream.
Both output lengths are measured against the binary input, including sparse
label bits. The conclusion supplies exact expansion, not a detached witness. -/
theorem extract_spec {word : List Bool} {t : Reset.Term ℕ} (h : decode word = some t) :
    let D := SupportIndex.labels t
    ∃ records : List (GuardRecord.Record D.length),
      extract word = some (pair (LabelDictionary.encode D) (GuardRecord.encodeList records)) ∧
      records.length = t.leafCount ∧
      records.map (fun r => (D.get r.1, SupportIndex.expand D r.2)) = t.guardEntries ∧
      (LabelDictionary.encode D).length ≤ word.length ∧
      (GuardRecord.encodeList records).length ≤ 6 * word.length * (word.length + 1) ∧
      (pair (LabelDictionary.encode D) (GuardRecord.encodeList records)).length ≤
        6 * word.length * (word.length + 1) + 2 * word.length + 2 := by
  dsimp only
  obtain ⟨records, hr, hlen, he, _, hb⟩ := indexed_guard_records t
  have hw := encode_of_decode h
  have hl : t.leafCount ≤ word.length := hw ▸ leafCount_le_length_encode t
  have hd : (LabelDictionary.encode (SupportIndex.labels t)).length ≤ word.length := by
    rw [← hw]
    exact length_dictionary_le t
  have hrb := hb.trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 6 hl) (Nat.add_le_add_right hl 1))
  refine ⟨records, ?_, hlen, he, hd, hrb, ?_⟩
  · simp [extract, h, hr]
  · rw [pair_length]
    omega

/-- The frontend accepts exactly the same inputs as the original-tree parser.
Support compression cannot introduce failure on a valid term. -/
theorem extract_eq_none_iff (word : List Bool) : extract word = none ↔ decode word = none := by
  cases hd : decode word with
  | none => simp [extract, hd]
  | some t =>
    obtain ⟨records, he, _⟩ := extract_spec hd
    simp only [he, reduceCtorEq]

end KFOL.Algorithms.TermCode
