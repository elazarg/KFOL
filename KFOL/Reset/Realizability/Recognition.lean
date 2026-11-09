module

public import KFOL.Reset.Realizability.Constructible

/-! # Executable bounded greedy recognition of constructibility -/

@[expose] public section

namespace KFOL.Reset.GuardTable

universe v

variable {Var : Type v} [DecidableEq Var] {G : GuardTable Var}

@[simp] theorem mem_advance (G : GuardTable Var) (A B : Finset Var) (j : Var) :
    j ∈ G.advance A B ↔ j ∈ B ∨ (j ∈ A ∧ G.Enabled (B : Set Var) j) := by
  simp only [advance, Finset.mem_union, Finset.mem_filter, Enabled]
  rfl

/-- A batch of positions enabled before the round can be inserted in any order. -/
theorem Constructible.union_enabled {B : Finset Var} (hB : G.Constructible B) (A : Finset Var)
    (hA : ∀ j ∈ A, G.Enabled (B : Set Var) j) : G.Constructible (B ∪ A) := by
  induction A using Finset.induction_on with
  | empty => simpa only [Finset.union_empty] using hB
  | @insert j A hf ih =>
    have hb := ih (fun k hk => hA k (Finset.mem_insert_of_mem hk))
    by_cases hj : j ∈ B ∪ A
    · rw [Finset.union_insert, Finset.insert_eq_of_mem hj]
      exact hb
    · rw [Finset.union_insert]
      exact .insert j hb hj (enabled_mono (by
        intro k hk
        exact Finset.mem_union_left _ hk) (hA j (Finset.mem_insert_self _ _)))

theorem constructible_advance (G : GuardTable Var) (A B : Finset Var)
    (hB : G.Constructible B) : G.Constructible (G.advance A B) := by
  apply hB.union_enabled
  intro j hj
  exact (Finset.mem_filter.mp hj).2

theorem constructible_reached (G : GuardTable Var) (A : Finset Var) (k : ℕ) :
    G.Constructible (G.reached A k) := by
  induction k with
  | zero => exact .empty
  | succ k ih => exact G.constructible_advance A _ ih

theorem reached_subset (G : GuardTable Var) (A : Finset Var) (k : ℕ) : G.reached A k ⊆ A := by
  induction k with
  | zero => exact Finset.empty_subset _
  | succ k ih =>
    intro j hj
    rcases (G.mem_advance A _ j).mp hj with hj | ⟨hj, _⟩
    · exact ih hj
    · exact hj

theorem reached_mono_step (G : GuardTable Var) (A : Finset Var) (k : ℕ) :
    G.reached A k ⊆ G.reached A (k + 1) := Finset.subset_union_left

/-- Every incomplete round on a constructible target makes strict progress. -/
theorem card_reached_lt {A : Finset Var} (hA : G.Constructible A) (k : ℕ)
    (hne : G.reached A k ≠ A) : (G.reached A k).card < (G.reached A (k + 1)).card := by
  have hnsub : ¬A ⊆ G.reached A k := by
    intro hs
    exact hne (Finset.Subset.antisymm (G.reached_subset A k) hs)
  obtain ⟨j, hjA, hj, hen⟩ := hA.exists_enabled hnsub
  have hnew : j ∈ G.reached A (k + 1) :=
    (G.mem_advance A _ j).mpr (Or.inr ⟨hjA, hen⟩)
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨G.reached_mono_step A k,
    fun he => hj (he ▸ hnew)⟩

/-- At most one round per target label is sufficient. -/
theorem reached_eq_of_constructible {A : Finset Var} (hA : G.Constructible A) :
    G.reached A A.card = A := by
  have bound (k : ℕ) : k ≤ (G.reached A k).card ∨ G.reached A k = A := by
    induction k with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ k ih =>
      by_cases he : G.reached A k = A
      · exact Or.inr (Finset.Subset.antisymm (G.reached_subset A (k + 1))
          (by
            intro j hj
            exact G.reached_mono_step A k (he.symm ▸ hj)))
      · have hc := card_reached_lt hA k he
        have hk := ih.resolve_right he
        exact Or.inl (by omega)
  rcases bound A.card with hcard | he
  · exact Finset.eq_of_subset_of_card_le (G.reached_subset A A.card) hcard
  · exact he

/-- The executable test agrees with the independently defined finite construction. -/
@[simp] theorem constructibleCheck_eq_true (G : GuardTable Var) (A : Finset Var) :
    G.constructibleCheck A = true ↔ G.Constructible A := by
  rw [constructibleCheck, decide_eq_true_eq]
  constructor
  · intro he
    rw [← he]
    exact G.constructible_reached A A.card
  · exact reached_eq_of_constructible

/-- All individual bad-guard checks are justified against the logical criteria. -/
theorem badGuards_eq_empty (G : GuardTable Var) (j : Var) : G.badGuards j = ∅ ↔
    ∀ A ∈ G.guards j, j ∉ A ∧ G.Constructible A ∧
      ∀ B ∈ G.guards j, A ⊆ B → A = B := by
  classical
  constructor
  · intro he A hA
    have hn : ¬(j ∈ A ∨ G.constructibleCheck A = false ∨
        ∃ B ∈ G.guards j, A ⊆ B ∧ A ≠ B) := by
      intro hb
      have hm : A ∈ G.badGuards j := Finset.mem_filter.mpr ⟨hA, hb⟩
      rw [he] at hm
      simp at hm
    refine ⟨fun hj => hn (Or.inl hj), ?_, ?_⟩
    · apply (G.constructibleCheck_eq_true A).mp
      cases hb : G.constructibleCheck A with
      | false => exact False.elim (hn (Or.inr (Or.inl hb)))
      | true => rfl
    · intro B hB hAB
      by_contra hne
      exact hn (Or.inr (Or.inr ⟨B, hB, hAB, hne⟩))
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hm
    obtain ⟨hA, hb⟩ := Finset.mem_filter.mp hm
    obtain ⟨hs, hc, ha⟩ := h A hA
    rcases hb with hj | hb | ⟨B, hB, hAB, hne⟩
    · exact hs hj
    · have ht := (G.constructibleCheck_eq_true A).mpr hc
      rw [hb] at ht
      cases ht
    · exact hne (ha B hB hAB)

/-- Correctness of the entire executable recognition procedure. This theorem
states no machine-time bound; the bounded scans are exposed in the definitions. -/
@[simp] theorem check_eq_true [Fintype Var] (G : GuardTable Var) :
    G.check = true ↔ G.WellFormed := by
  classical
  rw [check, decide_eq_true_eq]
  constructor
  · rintro ⟨hr, he⟩
    have hnone (j : Var) : ¬((∅ ∈ G.guards j ∧ j ≠ G.root) ∨ G.badGuards j ≠ ∅) := by
      intro hb
      have hm : j ∈ Finset.univ.filter (fun j : Var =>
          (∅ ∈ G.guards j ∧ j ≠ G.root) ∨ G.badGuards j ≠ ∅) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hb⟩
      rw [he] at hm
      simp at hm
    have hbad (j : Var) : G.badGuards j = ∅ := by
      by_contra hn
      exact hnone j (Or.inr hn)
    have props (j : Var) := (G.badGuards_eq_empty j).mp (hbad j)
    refine ⟨fun j A hA B hB hAB => (props j A hA).2.2 B hB hAB, hr, ?_, ?_, ?_⟩
    · intro j hj
      by_contra hn
      exact hnone j (Or.inl ⟨hj, hn⟩)
    · intro j A hA
      exact (props j A hA).1
    · intro j A hA
      exact (props j A hA).2.1
  · rintro ⟨ha, hr, hu, hs, hc⟩
    refine ⟨hr, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro j hj
    obtain ⟨_, hj⟩ := Finset.mem_filter.mp hj
    rcases hj with ⟨he, hn⟩ | hn
    · exact hn (hu j he)
    · apply hn
      apply (G.badGuards_eq_empty j).mpr
      intro A hA
      exact ⟨hs j A hA, hc j A hA, fun B hB hAB => ha j A hA B hB hAB⟩

end KFOL.Reset.GuardTable
