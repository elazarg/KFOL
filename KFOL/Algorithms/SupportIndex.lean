module

public import KFOL.Algorithms.GuardWords
public import KFOL.Reset.Extraction

/-! # Exact, compact indexing of the actual variable support -/

@[expose] public section

namespace KFOL.Algorithms.SupportIndex

universe v

variable {Var : Type v} [DecidableEq Var]

@[simp] theorem labels_nodup (t : Reset.Term Var) : (labels t).Nodup := List.nodup_dedup _

/-- The dictionary contains exactly the actual support, independently of
guards, unused declarations or the sizes of variable names. -/
@[simp] theorem labels_toFinset (t : Reset.Term Var) : (labels t).toFinset = t.varFinset := by
  simp only [labels, List.toFinset_dedup]
  induction t using Reset.Term.induction_reset with
  | var => rfl
  | step s t hs ht =>
    simp only [Reset.Term.guardEntries_step, List.map_append, List.map_map,
      List.toFinset_append, Function.comp_def]
    rw [hs, ht, Reset.Term.varFinset_step, Finset.union_comm]

@[simp] theorem mem_labels (t : Reset.Term Var) (j : Var) : j ∈ labels t ↔ j ∈ t.varFinset := by
  rw [← List.mem_toFinset, labels_toFinset]

theorem length_labels (t : Reset.Term Var) : (labels t).length = t.varFinset.card := by
  rw [← labels_toFinset t, List.toFinset_card_of_nodup (labels_nodup t)]

theorem length_labels_le (t : Reset.Term Var) : (labels t).length ≤ t.leafCount := by
  rw [length_labels]
  exact t.card_varFinset_le_leafCount

/-- Keeping one copy of each label cannot increase any nonnegative encoding
cost. This will account for binary names without using their numeric maximum. -/
theorem sum_labels_le (t : Reset.Term Var) (weight : Var → ℕ) :
    ((labels t).map weight).sum ≤ (t.guardEntries.map (fun p => weight p.1)).sum := by
  have h := ((List.dedup_sublist (t.guardEntries.map Prod.fst)).map weight).sum_le_sum
    (fun _ _ => Nat.zero_le _)
  simpa only [labels, List.map_map, Function.comp_def] using h

theorem locate_eq_some_iff (D : List Var) (hD : D.Nodup) (j : Var) (i : Fin D.length) :
    locate D j = some i ↔ D.get i = j := by
  unfold locate
  split
  next hj =>
    simp only [Option.some.injEq]
    constructor
    · intro he
      cases he
      exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hj)
    · intro he
      apply Fin.ext
      simpa only [he] using List.get_idxOf hD i
  next hj =>
    simp only [reduceCtorEq, false_iff]
    intro he
    exact hj (he ▸ List.get_mem D i)

theorem locate_isSome_iff (D : List Var) (j : Var) : (locate D j).isSome = true ↔ j ∈ D := by
  unfold locate
  split <;> simp_all

/-- The compact indices are genuinely equivalent to the actual support. -/
theorem exists_support_equiv (t : Reset.Term Var) :
    ∃ e : Fin (labels t).length ≃ {j // j ∈ t.varFinset},
      ∀ i, (e i).val = (labels t).get i := by
  refine ⟨((labels_nodup t).getEquiv (labels t)).trans
    (Equiv.subtypeEquivRight (mem_labels t)), ?_⟩
  intro i
  rfl

@[simp] theorem mem_compress (D : List Var) (A : Finset Var) (i : Fin D.length) :
    i ∈ compress D A ↔ D.get i ∈ A := by simp [compress]

/-- Expansion is a left inverse on sets covered by the dictionary, even
before assuming the dictionary has no repetitions. -/
theorem expand_compress (D : List Var) (A : Finset Var) (hA : A ⊆ D.toFinset) :
    expand D (compress D A) = A := by
  ext j
  simp only [expand, Finset.mem_image, mem_compress]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (hA hj))
    exact ⟨i, hi ▸ hj, hi⟩

/-- No information about positions is lost when labels are distinct. -/
theorem compress_expand (D : List Var) (hD : D.Nodup) (A : Finset (Fin D.length)) :
    compress D (expand D A) = A := by
  ext i
  simp only [mem_compress, expand, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, he⟩
    exact (hD.get_inj_iff.mp he) ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- Compression reflects subset inclusion whenever the left set is covered.
The right set may contain arbitrary unused ambient labels. -/
theorem compress_subset_iff (D : List Var) (A B : Finset Var) (hA : A ⊆ D.toFinset) :
    compress D A ⊆ compress D B ↔ A ⊆ B := by
  constructor
  · intro h j hj
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (hA hj))
    have hm := h ((mem_compress D A i).mpr (hi ▸ hj))
    exact hi ▸ (mem_compress D B i).mp hm
  · intro h i hi
    exact (mem_compress D B i).mpr (h ((mem_compress D A i).mp hi))

/-- The already certified word primitive tests subsets of covered labels
without a dense dimension based on their numeric values. -/
theorem subsetWord_compress (D : List Var) (A B : Finset Var) (hA : A ⊆ D.toFinset) :
    GuardWords.subsetWord (Bitset.encode (compress D A)) (Bitset.encode (compress D B)) =
      [true] ↔ A ⊆ B :=
  (GuardWords.subsetWord_encode _ _).trans (compress_subset_iff D A B hA)

/-- The original canonical guards feed the word primitive through the
computed support dictionary. Extra ambiguity labels outside support do not matter. -/
theorem enabled_iff_subsetWord (t : Reset.Term Var) (B : Finset Var) (j : Var) :
    t.guardTable.Enabled (B : Set Var) j ↔ ∃ A ∈ t.table j,
      GuardWords.subsetWord (Bitset.encode (compress (labels t) A))
        (Bitset.encode (compress (labels t) B)) = [true] := by
  unfold Reset.GuardTable.Enabled
  apply exists_congr
  intro A
  apply and_congr_right
  intro hA
  exact (subsetWord_compress (labels t) A B (by
    rw [labels_toFinset]
    exact t.subset_varFinset_of_mem_guards j ((Reset.Term.mem_minimize _ _).mp hA).1)).symm

/-- Every covered raw entry has a successful compressed representation, with
exact recovery of the original occurrence list, including duplicates. -/
theorem compressEntries_spec (D : List Var) (hD : D.Nodup) (entries : List (Var × Finset Var))
    (hout : ∀ p ∈ entries, p.1 ∈ D) (hguards : ∀ p ∈ entries, p.2 ⊆ D.toFinset) :
    ∃ records : List (Fin D.length × Finset (Fin D.length)),
      entries.mapM (compressEntry D) = some records ∧ records.length = entries.length ∧
      records.map (fun r => (D.get r.1, expand D r.2)) = entries := by
  induction entries with
  | nil => exact ⟨[], rfl, rfl, rfl⟩
  | cons p entries ih =>
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp (hout p List.mem_cons_self)
    have hl := (locate_eq_some_iff D hD p.1 i).mpr hi
    obtain ⟨records, hread, hlen, he⟩ := ih
      (fun q hq => hout q (List.mem_cons_of_mem _ hq))
      (fun q hq => hguards q (List.mem_cons_of_mem _ hq))
    refine ⟨(i, compress D p.2) :: records, ?_, by simp [hlen], ?_⟩
    · simp [List.mapM_cons, compressEntry, hl, hread]
    · simp only [List.map_cons, hi, expand_compress D p.2 (hguards p List.mem_cons_self), he]

/-- Any distinct covering dictionary can be used, including a shared
dictionary for two terms and dictionaries containing unused positions. -/
theorem compress_guardEntries_of_cover (t : Reset.Term Var) (D : List Var) (hD : D.Nodup)
    (hcover : t.varFinset ⊆ D.toFinset) :
    ∃ records : List (Fin D.length × Finset (Fin D.length)),
      t.guardEntries.mapM (compressEntry D) = some records ∧
      records.length = t.leafCount ∧
      records.map (fun r => (D.get r.1, expand D r.2)) = t.guardEntries := by
  obtain ⟨records, hread, hlen, he⟩ := compressEntries_spec D hD
    t.guardEntries (by
      intro p hp
      apply List.mem_toFinset.mp
      exact hcover (t.mem_varFinset_of_mem_guards p.1 ((t.mem_guardEntries p.1 p.2).mp hp))) (by
      intro p hp
      exact (t.subset_varFinset_of_mem_guards p.1 ((t.mem_guardEntries p.1 p.2).mp hp)).trans hcover)
  exact ⟨records, hread, by simpa only [Reset.Term.length_guardEntries] using hlen, he⟩

/-- Actual term extraction supplies all coverage hypotheses itself. -/
theorem compress_guardEntries (t : Reset.Term Var) :
    ∃ records : List (Fin (labels t).length × Finset (Fin (labels t).length)),
      t.guardEntries.mapM (compressEntry (labels t)) = some records ∧
      records.length = t.leafCount ∧
      records.map (fun r => ((labels t).get r.1, expand (labels t) r.2)) = t.guardEntries :=
  compress_guardEntries_of_cover t (labels t) (labels_nodup t) (by rw [labels_toFinset])

end KFOL.Algorithms.SupportIndex
