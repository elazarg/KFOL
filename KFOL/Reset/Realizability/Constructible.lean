module

public import KFOL.Reset.Antimatroid.Basic

/-! # Constructible sets for independent candidate guard data -/

@[expose] public section

namespace KFOL.Reset.GuardTable

universe v

variable {Var : Type v} [DecidableEq Var] {G : GuardTable Var}

omit [DecidableEq Var] in
theorem enabled_mono {B C : Set Var} (hBC : B ⊆ C) {j : Var} (hj : G.Enabled B j) :
    G.Enabled C j := by
  obtain ⟨A, hA, hAB⟩ := hj
  exact ⟨A, hA, hAB.trans hBC⟩

/-- Unions of constructible sets are constructible; an already reached label
is skipped rather than treated as a new occurrence. -/
theorem Constructible.union {A B : Finset Var} (hA : G.Constructible A)
    (hB : G.Constructible B) : G.Constructible (A ∪ B) := by
  induction hB with
  | empty => simpa only [Finset.union_empty] using hA
  | @insert B j hB hf he ih =>
    by_cases hj : j ∈ A ∪ B
    · have hh : A ∪ Insert.insert j B = A ∪ B := by simp [Finset.union_insert, hj]
      rw [hh]
      exact ih
    · rw [Finset.union_insert]
      exact .insert j ih hj (enabled_mono (by
        intro x hx
        exact Finset.mem_union_right _ hx) he)

/-- Every constructed position has an enabling prerequisite avoiding itself. -/
theorem Constructible.enabled_of_mem {A : Finset Var} (hA : G.Constructible A) {j : Var}
    (hj : j ∈ A) : G.Enabled (A.erase j : Set Var) j := by
  induction hA with
  | empty => simp at hj
  | @insert A k hA hf he ih =>
    rcases Finset.mem_insert.mp hj with heq | hj
    · subst k
      simpa only [Finset.erase_insert hf] using he
    · exact enabled_mono (by
        intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
          Finset.mem_insert_of_mem (Finset.mem_erase.mp hx).2⟩) (ih hj)

/-- Monotonicity prevents a greedy choice from blocking a construction:
if a constructible target is not contained in the reached set, some fresh
position of the target is already enabled there. -/
theorem Constructible.exists_enabled {A B : Finset Var} (hA : G.Constructible A)
    (hAB : ¬A ⊆ B) : ∃ j ∈ A, j ∉ B ∧ G.Enabled (B : Set Var) j := by
  induction hA with
  | empty => exact False.elim (hAB (Finset.empty_subset _))
  | @insert A j hA hf he ih =>
    by_cases hab : A ⊆ B
    · have hj : j ∉ B := fun hj => hAB ((by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hj
        · exact hab hx))
      exact ⟨j, Finset.mem_insert_self _ _, hj, enabled_mono hab he⟩
    · obtain ⟨k, hk, hkb, he⟩ := ih hab
      exact ⟨k, Finset.mem_insert_of_mem hk, hkb, he⟩

/-- A construction is accessible by deleting its last fresh addition. -/
theorem Constructible.accessible {A : Finset Var} (hA : G.Constructible A) (hne : A.Nonempty) :
    ∃ j ∈ A, G.Constructible (A.erase j) := by
  cases hA with
  | empty => simp at hne
  | insert j hA hf he =>
    exact ⟨j, Finset.mem_insert_self _ _, by simpa only [Finset.erase_insert hf] using hA⟩

/-- Every position of a constructible set has a nonempty table. -/
theorem Constructible.active {A : Finset Var} (hA : G.Constructible A) {j : Var}
    (hj : j ∈ A) : (G.guards j).Nonempty := by
  obtain ⟨B, hB, _⟩ := hA.enabled_of_mem hj
  exact ⟨B, hB⟩

/-- Finite unions preserve constructibility. -/
theorem constructible_biUnion (S : Finset (Finset Var))
    (hS : ∀ A ∈ S, G.Constructible A) : G.Constructible (S.biUnion id) := by
  induction S using Finset.induction_on with
  | empty => exact .empty
  | @insert A S hf ih =>
    rw [Finset.biUnion_insert]
    exact (hS A (Finset.mem_insert_self _ _)).union
      (ih (fun B hB => hS B (Finset.mem_insert_of_mem hB)))

/-- Root uniqueness alone forces every first addition to be the declared root. -/
theorem Constructible.root_mem {A : Finset Var}
    (hroot : ∀ j, ∅ ∈ G.guards j → j = G.root)
    (hA : G.Constructible A) (hne : A.Nonempty) : G.root ∈ A := by
  induction hA with
  | empty => simp at hne
  | @insert A j hA hf he ih =>
    by_cases ha : A.Nonempty
    · exact Finset.mem_insert_of_mem (ih ha)
    · have ha : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
      subst A
      obtain ⟨B, hB, hb⟩ := he
      have hb0 : B = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun x hx => by simpa using hb hx)
      have hj := hroot j (hb0 ▸ hB)
      simp [hj]

/-- The local completeness condition `reset:eq:complete` is equivalent to
constructibility of every prerequisite, provided outputs do not enable
themselves. No root, antichain or realizability assumption is needed. -/
theorem all_constructible_iff_local (G : GuardTable Var)
    (hself : ∀ j, ∀ A ∈ G.guards j, j ∉ A) :
    (∀ j, ∀ A ∈ G.guards j, G.Constructible A) ↔
      ∀ j, ∀ A ∈ G.guards j, ∀ k ∈ A, ∃ B ∈ G.guards k, B ⊆ A := by
  classical
  constructor
  · intro h j A hA k hk
    obtain ⟨B, hB, hs⟩ := (h j A hA).enabled_of_mem hk
    exact ⟨B, hB, fun x hx => (Finset.mem_erase.mp (hs hx)).2⟩
  · intro h j A hA
    suffices ∀ n (A : Finset Var), A.card = n →
        (∃ j, A ∈ G.guards j) → G.Constructible A from this _ A rfl ⟨j, hA⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rintro A hcard ⟨j, hA⟩
      have hp : ∀ k : A, ∃ B ∈ G.guards k.val, B ⊆ A :=
        fun k => h j A hA k.val k.property
      choose B hB hsub using hp
      let S := A.attach.image (fun k => insert k.val (B k))
      have hc : ∀ C ∈ S, G.Constructible C := by
        intro C hC
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hC
        have hf := hself k.val (B k) (hB k)
        have hltA : (B k).card < A.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub k,
            fun he => hf ((Finset.ext_iff.mp he k.val).mpr k.property)⟩)
        have hlt : (B k).card < n := by omega
        exact .insert k.val (ih _ hlt (B k) rfl ⟨k.val, hB k⟩) hf
          ⟨B k, hB k, subset_rfl⟩
      have he : S.biUnion id = A := by
        ext k
        constructor
        · intro hk
          obtain ⟨C, hC, hk⟩ := Finset.mem_biUnion.mp hk
          obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hC
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact l.property
          · exact hsub l hk
        · intro hk
          let l : A := ⟨k, hk⟩
          exact Finset.mem_biUnion.mpr ⟨insert k (B l),
            Finset.mem_image.mpr ⟨l, Finset.mem_attach _ _, rfl⟩,
            Finset.mem_insert_self _ _⟩
      rw [← he]
      exact constructible_biUnion S hc

end KFOL.Reset.GuardTable
