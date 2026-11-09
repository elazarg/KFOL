module

public import KFOL.Reset.Substitution

/-! # Executable guard extraction and bounds in actual syntax occurrences -/

@[expose] public section

namespace KFOL.Reset.Term

universe v

variable {Var : Type v}

@[simp] theorem leafCount_var (j : Var) : leafCount (.var j) = 1 := rfl
@[simp] theorem leafCount_step (s t : Term Var) : (step s t).leafCount = s.leafCount + t.leafCount :=
  rfl

theorem leafCount_pos (t : Term Var) : 0 < t.leafCount := by
  induction t using induction_reset with
  | var => exact Nat.zero_lt_one
  | step s t hs ht => simp only [leafCount_step]; omega

/-- A primitive binary tree has exactly one more leaf than internal nodes. -/
theorem size_add_one (t : Term Var) : t.size + 1 = 2 * t.leafCount := by
  induction t using induction_reset with
  | var => rfl
  | step s t hs ht => simp only [size_step, leafCount_step]; omega

variable [DecidableEq Var]

@[simp] theorem occurrences_var (i j : Var) : occurrences (.var i) j = if j = i then 1 else 0 :=
  rfl
@[simp] theorem occurrences_step (s t : Term Var) (j : Var) :
    (step s t).occurrences j = s.occurrences j + t.occurrences j := rfl

/-- Sums over any finite set covering the actual support count all leaves. -/
theorem sum_occurrences (t : Term Var) (S : Finset Var) (hS : t.varFinset ⊆ S) :
    ∑ j ∈ S, t.occurrences j = t.leafCount := by
  induction t using induction_reset with
  | var i =>
    have hi := hS (Finset.mem_singleton_self i)
    simp only [occurrences_var, leafCount_var, Finset.sum_ite_eq', hi, ite_true]
  | step s t hs ht =>
    simp only [varFinset_step, Finset.union_subset_iff] at hS
    simp_rw [occurrences_step]
    rw [Finset.sum_add_distrib, hs hS.1, ht hS.2, leafCount_step]

@[simp] theorem collectGuards_root (t : Term Var) : t.collectGuards.1 = t.root := by
  induction t using induction_reset with
  | var => rfl
  | step s t _ ht => exact ht

@[simp] theorem guardEntries_var (j : Var) : guardEntries (.var j) = [(j, ∅)] := rfl

theorem guardEntries_step (s t : Term Var) :
    (step s t).guardEntries = t.guardEntries ++
      s.guardEntries.map (fun p => (p.1, insert t.root p.2)) := by
  change t.collectGuards.2 ++
    s.collectGuards.2.map (fun p => (p.1, insert t.collectGuards.1 p.2)) = _
  rw [collectGuards_root]
  rfl

omit [DecidableEq Var] in
@[simp] theorem relabel_step {Var' : Type*} (f : Var → Var') (s t : Term Var) :
    (step s t).relabel f = step (s.relabel f) (t.relabel f) := by
  simp only [step, FirstOrder.Language.Term.relabel]
  congr 1
  funext i
  by_cases hi : i = 0 <;> simp [hi]

omit [DecidableEq Var] in
@[simp] theorem root_relabel {Var' : Type*} (f : Var → Var') (t : Term Var) :
    root (t.relabel f) = f t.root := by
  induction t using induction_reset with
  | var => rfl
  | step s t _ ht => simp only [relabel_step, root_step, ht]

/-- Raw occurrence extraction commutes with every variable renaming,
including noninjective maps and independent repeated occurrences. -/
theorem guardEntries_relabel {Var' : Type*} [DecidableEq Var'] (f : Var → Var') (t : Term Var) :
    guardEntries (t.relabel f) = t.guardEntries.map (fun p => (f p.1, p.2.image f)) := by
  induction t using induction_reset with
  | var => rfl
  | step s t hs ht =>
    simp only [relabel_step, guardEntries_step, hs, ht, root_relabel,
      List.map_append, List.map_map, Function.comp_def, Finset.image_insert]

/-- Raw entries are indexed by actual leaf occurrences, before normalization. -/
@[simp] theorem length_guardEntries (t : Term Var) : t.guardEntries.length = t.leafCount := by
  induction t using induction_reset with
  | var => rfl
  | step s t hs ht =>
    simp only [guardEntries_step, List.length_append, List.length_map, hs, ht, leafCount_step]
    omega

/-- Filtering the raw occurrence list by an output counts precisely its
syntactic occurrences, even when prerequisites will later merge. -/
theorem countP_guardEntries (t : Term Var) (j : Var) :
    t.guardEntries.countP (fun p => decide (p.1 = j)) = t.occurrences j := by
  induction t using induction_reset with
  | var i => by_cases hi : j = i <;> simp [guardEntries_var, occurrences_var, hi, eq_comm]
  | step s t hs ht =>
    simp only [guardEntries_step, List.countP_append, List.countP_map, Function.comp_def]
    change t.guardEntries.countP _ + s.guardEntries.countP _ =
      s.occurrences j + t.occurrences j
    rw [hs, ht]
    omega

/-- Every collected pair is exactly an entry of the independent structural guards. -/
theorem mem_guardEntries (t : Term Var) (j : Var) (A : Finset Var) :
    (j, A) ∈ t.guardEntries ↔ A ∈ t.guards j := by
  induction t using induction_reset generalizing A with
  | var i => by_cases hi : j = i <;> simp [guardEntries_var, guards, hi]
  | step s t hs ht =>
    simp only [guardEntries_step, List.mem_append, List.mem_map, guards_step,
      Finset.mem_union, Finset.mem_image, ht]
    constructor
    · rintro (hA | ⟨⟨k, B⟩, hB, he⟩)
      · exact Or.inl hA
      · have hk := congrArg Prod.fst he
        have hBA := congrArg Prod.snd he
        dsimp at hk hBA
        subst k
        exact Or.inr ⟨B, (hs B).mp hB, hBA⟩
    · rintro (hA | ⟨B, hB, rfl⟩)
      · exact Or.inl hA
      · exact Or.inr ⟨(j, B), (hs B).mpr hB, rfl⟩

/-- Filtering the traversal by output and deleting duplicates recovers the
raw structural table. This connects executable extraction to its semantics. -/
theorem guards_eq_entries (t : Term Var) (j : Var) :
    t.guards j = ((t.guardEntries.filter (fun p => p.1 = j)).map Prod.snd).toFinset := by
  ext A
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro hA
    exact ⟨(j, A), ⟨(t.mem_guardEntries j A).mpr hA, rfl⟩, rfl⟩
  · rintro ⟨⟨k, B⟩, ⟨hB, hk⟩, he⟩
    dsimp at hk he
    subst k
    subst B
    exact (t.mem_guardEntries j A).mp hB

/-- Canonical normalization of the executable collector gives the existing
table, which was defined independently of the collector. -/
theorem table_eq_entries (t : Term Var) (j : Var) :
    t.table j = minimize
      (((t.guardEntries.filter (fun p => p.1 = j)).map Prod.snd).toFinset) := by
  rw [table, guards_eq_entries]

/-- At most one distinct raw guard survives for each occurrence of its output. -/
theorem card_guards_le_occurrences (t : Term Var) (j : Var) :
    (t.guards j).card ≤ t.occurrences j := by
  induction t using induction_reset with
  | var i => by_cases hi : j = i <;> simp [guards, occurrences, hi]
  | step s t hs ht =>
    have hu := Finset.card_union_le (t.guards j) ((s.guards j).image (insert t.root))
    have him := Finset.card_image_le (s := s.guards j) (f := insert t.root)
    rw [guards_step, occurrences_step]
    omega

theorem card_table_le_occurrences (t : Term Var) (j : Var) :
    (t.table j).card ≤ t.occurrences j :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans (t.card_guards_le_occurrences j)

/-- Every prerequisite label is an actual input of the term. -/
theorem subset_varFinset_of_mem_guards (t : Term Var) (j : Var) {A : Finset Var}
    (hA : A ∈ t.guards j) : A ⊆ t.varFinset := by
  induction t using induction_reset generalizing A with
  | var i =>
    by_cases hi : j = i
    · simp only [guards, ite_eq_left hi, Finset.mem_singleton] at hA
      rw [hA]
      exact Finset.empty_subset _
    · simp [guards, hi] at hA
  | step s t hs ht =>
    rw [guards_step] at hA
    rcases Finset.mem_union.mp hA with hA | hA
    · exact (ht hA).trans (by rw [varFinset_step]; exact Finset.subset_union_right)
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      rw [varFinset_step]
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Finset.mem_union_right _
          (t.mem_varFinset_of_selected Set.univ t.root (t.selected_root Set.univ))
      · exact Finset.mem_union_left _ (hs hB hk)

/-- A raw prerequisite gains at most one position at each left branch. -/
theorem card_guard_add_one_le (t : Term Var) (j : Var) {A : Finset Var}
    (hA : A ∈ t.guards j) : A.card + 1 ≤ t.leafCount := by
  induction t using induction_reset generalizing A with
  | var i =>
    by_cases hi : j = i
    · simp only [guards, ite_eq_left hi, Finset.mem_singleton] at hA
      rw [hA]
      simp
    · simp [guards, hi] at hA
  | step s t hs ht =>
    rw [guards_step] at hA
    rw [leafCount_step]
    rcases Finset.mem_union.mp hA with hA | hA
    · have hb := ht hA
      omega
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
      have hb := hs hB
      have hc := Finset.card_insert_le t.root B
      have hp := t.leafCount_pos
      omega

theorem mem_varFinset_of_mem_guards (t : Term Var) (j : Var) {A : Finset Var}
    (hA : A ∈ t.guards j) : j ∈ t.varFinset :=
  t.mem_varFinset_of_selected (A : Set Var) j
    ((t.selected_iff_guard _ j).mpr ⟨A, hA, subset_rfl⟩)

theorem guards_eq_empty_of_not_mem (t : Term Var) (j : Var) (hj : j ∉ t.varFinset) :
    t.guards j = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr (fun _ hA => hj (t.mem_varFinset_of_mem_guards j hA))

theorem table_eq_empty_of_not_mem (t : Term Var) (j : Var) (hj : j ∉ t.varFinset) :
    t.table j = ∅ := by simp [table, t.guards_eq_empty_of_not_mem j hj, minimize]

theorem card_varFinset_le_leafCount (t : Term Var) : t.varFinset.card ≤ t.leafCount := by
  induction t using induction_reset with
  | var => simp
  | step s t hs ht =>
    rw [varFinset_step, leafCount_step]
    have hu := Finset.card_union_le s.varFinset t.varFinset
    omega

/-- Canonical self-exclusion gives the sharper support-sized prerequisite bound. -/
theorem card_table_guard_add_one_le_support (t : Term Var) (j : Var) {A : Finset Var}
    (hA : A ∈ t.table j) : A.card + 1 ≤ t.varFinset.card := by
  have hraw := ((mem_minimize _ _).mp hA).1
  have hj := t.mem_varFinset_of_mem_guards j hraw
  have hsub := t.subset_varFinset_of_mem_guards j hraw
  have hc : (insert j A).card ≤ t.varFinset.card := Finset.card_le_card (by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hj
    · exact hsub hk)
  rwa [Finset.card_insert_of_notMem (t.not_mem_of_mem_table j hA)] at hc

/-- A whole raw table has at most one entry per syntactic variable occurrence. -/
theorem sum_card_guards_le (t : Term Var) :
    ∑ j ∈ t.varFinset, (t.guards j).card ≤ t.leafCount := by
  calc
    _ ≤ ∑ j ∈ t.varFinset, t.occurrences j :=
      Finset.sum_le_sum (fun j _ => t.card_guards_le_occurrences j)
    _ = t.leafCount := t.sum_occurrences _ subset_rfl

theorem sum_card_table_le (t : Term Var) :
    ∑ j ∈ t.varFinset, (t.table j).card ≤ t.leafCount := by
  calc
    _ ≤ ∑ j ∈ t.varFinset, t.occurrences j :=
      Finset.sum_le_sum (fun j _ => t.card_table_le_occurrences j)
    _ = t.leafCount := t.sum_occurrences _ subset_rfl

omit [DecidableEq Var] in
private theorem sum_guard_sizes_le (G : Var → Finset (Finset Var)) (S : Finset Var) (N : ℕ)
    (hN : ∀ j ∈ S, ∀ A ∈ G j, A.card + 1 ≤ N) :
    ∑ j ∈ S, ∑ A ∈ G j, (A.card + 1) ≤ (∑ j ∈ S, (G j).card) * N := by
  calc
    _ ≤ ∑ j ∈ S, ∑ _A ∈ G j, N :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun A hA => hN j hj A hA))
    _ = _ := by simp [Finset.sum_mul]

/-- Count output labels and prerequisite labels, plus the separately stored
root. These are label occurrences; binary encoding costs belong to the machine layer. -/
theorem table_description_le (t : Term Var) :
    1 + ∑ j ∈ t.varFinset, ∑ A ∈ t.table j, (A.card + 1) ≤
      1 + t.varFinset.card * t.leafCount := by
  have hw := sum_guard_sizes_le t.table t.varFinset t.varFinset.card
    (fun j _ A hA => t.card_table_guard_add_one_le_support j hA)
  have hn := Nat.mul_le_mul_right t.varFinset.card t.sum_card_table_le
  apply Nat.add_le_add_left (hw.trans ?_) 1
  simpa only [Nat.mul_comm] using hn

/-- The pre-normalization data also has a quadratic bound. -/
theorem guards_description_le (t : Term Var) :
    1 + ∑ j ∈ t.varFinset, ∑ A ∈ t.guards j, (A.card + 1) ≤ 1 + t.leafCount ^ 2 := by
  have hw := sum_guard_sizes_le t.guards t.varFinset t.leafCount
    (fun j _ A hA => t.card_guard_add_one_le j hA)
  have hn := Nat.mul_le_mul_right t.leafCount t.sum_card_guards_le
  rw [Nat.pow_two]
  omega

/-- The actual traversal list obeys the same bound before deduplication. -/
theorem guardEntries_description_le (t : Term Var) :
    1 + (t.guardEntries.map (fun p => p.2.card + 1)).sum ≤ 1 + t.leafCount ^ 2 := by
  have hw : (t.guardEntries.map (fun p => p.2.card + 1)).sum ≤
      (t.guardEntries.map (fun _ => t.leafCount)).sum :=
    List.sum_le_sum (fun p hp => t.card_guard_add_one_le p.1
      ((t.mem_guardEntries p.1 p.2).mp hp))
  simpa only [List.map_const', List.sum_replicate, length_guardEntries, nsmul_eq_mul,
    Nat.cast_id, Nat.pow_two] using Nat.add_le_add_left hw 1

/-- Finite ambient padding contributes no entries to the previously defined M. -/
theorem entryCount_guardTable_le [Fintype Var] (t : Term Var) :
    t.guardTable.entryCount ≤ t.leafCount := by
  change (∑ j, (t.table j).card) ≤ t.leafCount
  have he : (∑ j ∈ t.varFinset, (t.table j).card) = ∑ j, (t.table j).card :=
    Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
      rw [t.table_eq_empty_of_not_mem j hj]
      rfl)
  rw [← he]
  exact t.sum_card_table_le

theorem table_description_quadratic (t : Term Var) :
    1 + ∑ j ∈ t.varFinset, ∑ A ∈ t.table j, (A.card + 1) ≤ 1 + t.leafCount ^ 2 := by
  have hn := Nat.mul_le_mul_right t.leafCount t.card_varFinset_le_leafCount
  rw [Nat.pow_two]
  exact t.table_description_le.trans (Nat.add_le_add_left hn 1)

end KFOL.Reset.Term
