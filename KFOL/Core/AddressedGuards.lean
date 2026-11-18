module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Minimal

/-! # Hitting sets of independently addressed rows

An address selects one of two blocks at each bit. Postings may occur in
several blocks or in the fixed set, and either block may be empty.
-/

@[expose] public section
namespace KFOL.Core.AddressedGuards
universe u v
variable {Posting : Type u} {Bit : Type v}

/-- All postings in the row at an address. -/
def row (F : Set Posting) (B : Bit → Bool → Set Posting) (x : Bit → Bool) : Set Posting :=
  F ∪ ⋃ i, B i (x i)

/-- A guard intersects every addressed row. -/
def HitsAll (F : Set Posting) (B : Bit → Bool → Set Posting) (G : Set Posting) : Prop :=
  ∀ x, (G ∩ row F B x).Nonempty

/-- A guard hits every row precisely when a fixed posting witnesses this,
or both alternatives of one bit meet the guard. -/
theorem hitsAll_iff (F : Set Posting) (B : Bit → Bool → Set Posting) (G : Set Posting) :
    HitsAll F B G ↔ (G ∩ F).Nonempty ∨
      ∃ i, (G ∩ B i false).Nonempty ∧ (G ∩ B i true).Nonempty := by
  classical
  constructor
  · intro h
    by_cases hf : (G ∩ F).Nonempty
    · exact Or.inl hf
    right
    by_contra hmiss
    let x (i : Bit) := decide (G ∩ B i false).Nonempty
    obtain ⟨a, ha, haf | hab⟩ := h x
    · exact hf ⟨a, ha, haf⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hab
      by_cases h0 : (G ∩ B i false).Nonempty
      · have h1 : (G ∩ B i true).Nonempty := ⟨a, ha, by simpa [x, h0] using hi⟩
        exact hmiss ⟨i, h0, h1⟩
      · exact h0 ⟨a, ha, by simpa [x, h0] using hi⟩
  · rintro (⟨a, ha, hf⟩ | ⟨i, h0, h1⟩) x
    · exact ⟨a, ha, Or.inl hf⟩
    · obtain ⟨a, ha, hb⟩ : (G ∩ B i (x i)).Nonempty := by cases x i <;> assumption
      exact ⟨a, ha, Or.inr (Set.mem_iUnion.mpr ⟨i, hb⟩)⟩

/-- The candidates before minimization. The pair may be a singleton
when one posting occurs in both alternatives. -/
def Candidate (F : Set Posting) (B : Bit → Bool → Set Posting) (C : Set Posting) : Prop :=
  (∃ a ∈ F, C = {a}) ∨ ∃ i a b, a ∈ B i false ∧ b ∈ B i true ∧ C = {a, b}

/-- Every hitting set contains one enumerated candidate, and every
superset of an enumerated candidate hits all rows. -/
theorem hitsAll_iff_contains_candidate (F : Set Posting) (B : Bit → Bool → Set Posting)
    (G : Set Posting) : HitsAll F B G ↔ ∃ C, Candidate F B C ∧ C ⊆ G := by
  rw [hitsAll_iff]
  constructor
  · rintro (⟨a, ha, hf⟩ | ⟨i, ⟨a, ha, h0⟩, b, hb, h1⟩)
    · exact ⟨{a}, Or.inl ⟨a, hf, rfl⟩, Set.singleton_subset_iff.mpr ha⟩
    · exact ⟨{a, b}, Or.inr ⟨i, a, b, h0, h1, rfl⟩,
        Set.insert_subset ha (Set.singleton_subset_iff.mpr hb)⟩
  · rintro ⟨C, hC, hsub⟩
    rcases hC with ⟨a, hf, rfl⟩ | ⟨i, a, b, h0, h1, rfl⟩
    · exact Or.inl ⟨a, hsub (by simp), hf⟩
    · exact Or.inr ⟨i, ⟨a, hsub (by simp), h0⟩, b, hsub (by simp), h1⟩

/-- Pruning the candidate list by inclusion gives exactly the prime guards. -/
theorem minimal_hitsAll_iff (F : Set Posting) (B : Bit → Bool → Set Posting) (G : Set Posting) :
    Minimal (HitsAll F B) G ↔ Minimal (Candidate F B) G := by
  have hits {C} (h : Candidate F B C) : HitsAll F B C :=
    (hitsAll_iff_contains_candidate F B C).2 ⟨C, h, Set.Subset.rfl⟩
  constructor
  · rintro ⟨hG, hmin⟩
    obtain ⟨C, hC, hCG⟩ := (hitsAll_iff_contains_candidate F B G).1 hG
    have he : C = G := Set.Subset.antisymm hCG (hmin (hits hC) hCG)
    exact ⟨he ▸ hC, fun _ h hsub => hmin (hits h) hsub⟩
  · rintro ⟨hG, hmin⟩
    refine ⟨hits hG, fun H hH hHG => ?_⟩
    obtain ⟨C, hC, hCH⟩ := (hitsAll_iff_contains_candidate F B H).1 hH
    exact (hmin hC (hCH.trans hHG)).trans hCH

/-- On an exact address, the positive clauses for binary increment require
the opposite rail at a carry and the same rail otherwise. The first clause
excludes the last address. The available rails may contain both values. -/
theorem successor_clauses_iff [LT Bit] (bits : Bit → Bool) (available : Bit → Bool → Prop) :
    ((∃ i, bits i = false) ∧
      (∀ i t, bits i = !t ∨ (∃ j, j < i ∧ bits j = false) ∨ available i (!t)) ∧
      (∀ i t j, j < i → bits i = !t ∨ bits j = true ∨ available i t)) ↔
    ((∃ i, bits i = false) ∧
      (∀ i, (∀ j, j < i → bits j = true) → available i (!(bits i))) ∧
      (∀ i, (∃ j, j < i ∧ bits j = false) → available i (bits i))) := by
  classical
  constructor
  · rintro ⟨nonfinal, flips, copies⟩
    refine ⟨nonfinal, fun i carry => ?_, fun i ⟨j, hj, zero⟩ => ?_⟩
    · rcases flips i (bits i) with h | ⟨j, hj, zero⟩ | h
      · cases hbit : bits i <;> simp [hbit] at h
      · exact Bool.noConfusion (zero.symm.trans (carry j hj))
      · exact h
    · rcases copies i (bits i) j hj with h | one | h
      · cases hbit : bits i <;> simp [hbit] at h
      · exact Bool.noConfusion (zero.symm.trans one)
      · exact h
  · rintro ⟨nonfinal, flips, copies⟩
    refine ⟨nonfinal, ?_, ?_⟩
    · intro i t
      by_cases bit : bits i = t
      · by_cases low : ∃ j, j < i ∧ bits j = false
        · exact Or.inr (Or.inl low)
        · have carry (j) (hj : j < i) : bits j = true := by
            cases hjbit : bits j
            · exact (low ⟨j, hj, hjbit⟩).elim
            · rfl
          exact Or.inr (Or.inr (bit ▸ flips i carry))
      · left
        cases t <;> cases hbit : bits i <;> simp_all
    · intro i t j hj
      by_cases bit : bits i = t
      · rcases hjbit : bits j with _ | _
        · exact Or.inr (Or.inr (bit ▸ copies i ⟨j, hj, hjbit⟩))
        · exact Or.inr (Or.inl rfl)
      · left
        cases t <;> cases hbit : bits i <;> simp_all

end KFOL.Core.AddressedGuards
