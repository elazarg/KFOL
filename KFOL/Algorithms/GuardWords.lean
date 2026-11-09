module

public import KFOL.Definitions.Algorithms
public import KFOL.Definitions.Reset

/-! # Exact bitset codecs and the semantic prerequisite test -/

@[expose] public section

namespace KFOL.Algorithms

namespace Bitset

@[simp] theorem length_encode {n : ℕ} (A : Finset (Fin n)) : (encode A).length = n := by
  simp [encode]

@[simp] theorem read_encode {n : ℕ} (A : Finset (Fin n)) (i : Fin n) :
    GuardWords.readBit (encode A) i.val = decide (i ∈ A) := by
  simp [GuardWords.readBit, encode, i.isLt]

@[simp] theorem decode_encode {n : ℕ} (A : Finset (Fin n)) : decode n (encode A) = some A := by
  simp only [decode, length_encode, ite_true, Option.some.injEq]
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change GuardWords.readBit (encode A) i.val = true ↔ i ∈ A
  rw [read_encode, decide_eq_true_eq]

theorem encode_injective {n : ℕ} : Function.Injective (@encode n) := by
  intro A B he
  have hd := congrArg (decode n) he
  simpa only [decode_encode, Option.some.injEq] using hd

/-- Successful decoding has no extra representations beyond the membership word. -/
theorem encode_of_decode {n : ℕ} {word : List Bool} {A : Finset (Fin n)}
    (h : decode n word = some A) : encode A = word := by
  unfold decode at h
  split at h
  next hw =>
    cases h
    subst n
    simp [encode]
  next => cases h

theorem decode_eq_some_iff {n : ℕ} (word : List Bool) (A : Finset (Fin n)) :
    decode n word = some A ↔ word = encode A :=
  ⟨fun h => (encode_of_decode h).symm, fun h => h ▸ decode_encode A⟩

end Bitset

namespace GuardWords

@[simp] theorem subsetScan_length (r a b : List Bool) : (subsetScan r a b).length = 1 := by
  cases r <;> rfl

/-- The scan visits exactly the positions below the ruler length. -/
theorem subsetScan_correct (r a b : List Bool) :
    (subsetScan r a b).headD false = true ↔
      ∀ i < r.length, readBit a i = true → readBit b i = true := by
  induction r with
  | nil => simp [subsetScan]
  | cons x r ih =>
    change ((subsetScan r a b).headD false &&
      (!readBit a r.length || readBit b r.length)) = true ↔ _
    rw [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', ih]
    simp only [List.length_cons]
    constructor
    · rintro ⟨hprev, hlast⟩ i hi ha
      by_cases he : i = r.length
      · subst i
        rcases hlast with hf | hb
        · rw [hf] at ha
          cases ha
        · exact hb
      · exact hprev i (by omega) ha
    · intro h
      refine ⟨fun i hi => h i (by omega), ?_⟩
      cases ha : readBit a r.length with
      | false => exact Or.inl rfl
      | true => exact Or.inr (h _ (by omega) ha)

/-- Total semantics, including malformed unequal-width input. -/
theorem subsetWord_correct (a b : List Bool) : subsetWord a b = [true] ↔
    a.length = b.length ∧ ∀ i < a.length, readBit a i = true → readBit b i = true := by
  simp only [subsetWord,
    List.cons.injEq, and_true, Bool.and_eq_true]
  rw [subsetScan_correct]
  simp only [decide_eq_true_eq]

theorem subsetFn_length (v : Fin 2 → List Bool) : (subsetFn v).length = 1 := rfl

/-- One width-independent word program implements the actual finite-guard
subset relation, including the zero-width case. -/
theorem subsetWord_encode {n : ℕ} (A B : Finset (Fin n)) :
    subsetWord (Bitset.encode A) (Bitset.encode B) = [true] ↔ A ⊆ B := by
  rw [subsetWord_correct]
  simp only [Bitset.length_encode, true_and]
  constructor
  · intro h i hi
    have ha : readBit (Bitset.encode A) i.val = true := by
      rw [Bitset.read_encode, decide_eq_true_eq]
      exact hi
    have hb := h i.val i.isLt ha
    rw [Bitset.read_encode] at hb
    exact of_decide_eq_true hb
  · intro h i hi ha
    rw [Bitset.read_encode A ⟨i, hi⟩, decide_eq_true_eq] at ha
    rw [Bitset.read_encode B ⟨i, hi⟩, decide_eq_true_eq]
    exact h ha

end GuardWords

/-- The word primitive is exactly the subset test used by the existing guard
enabling predicate; this is a representation bridge, not a new semantics. -/
theorem enabled_iff_subsetWord {n : ℕ} (G : Reset.GuardTable (Fin n))
    (A : Finset (Fin n)) (j : Fin n) :
    G.Enabled (A : Set (Fin n)) j ↔ ∃ C ∈ G.guards j,
      GuardWords.subsetWord (Bitset.encode C) (Bitset.encode A) = [true] := by
  simp only [Reset.GuardTable.Enabled, GuardWords.subsetWord_encode]
  rfl

end KFOL.Algorithms
