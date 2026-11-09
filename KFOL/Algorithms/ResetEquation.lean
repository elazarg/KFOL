module

public import KFOL.Algorithms.Normalization
public import KFOL.Reset.Chain

/-! # Complete equality checking for binary reset equations on shared support -/

@[expose] public section

namespace KFOL.Algorithms.ResetEquation

open _root_.Complexity

@[simp] theorem labels_nodup (s t : Reset.Term ℕ) : (labels s t).Nodup := List.nodup_dedup _

@[simp] theorem labels_toFinset (s t : Reset.Term ℕ) :
    (labels s t).toFinset = s.varFinset ∪ t.varFinset := by
  simp only [labels, List.toFinset_dedup, List.toFinset_append, SupportIndex.labels_toFinset]

theorem length_labels_le (s t : Reset.Term ℕ) :
    (labels s t).length ≤ s.leafCount + t.leafCount := by
  rw [← List.toFinset_card_of_nodup (labels_nodup s t), labels_toFinset]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add s.card_varFinset_le_leafCount t.card_varFinset_le_leafCount)

theorem length_labels_le_input (s t : Reset.Term ℕ) :
    (labels s t).length ≤ (TermCode.encode s).length + (TermCode.encode t).length :=
  (length_labels_le s t).trans (Nat.add_le_add (TermCode.leafCount_le_length_encode s)
    (TermCode.leafCount_le_length_encode t))

/-- Shared compression reflects equality of the original canonical tables,
including outputs outside either individual support. -/
theorem normalized_equal_iff (D : List ℕ) (hD : D.Nodup) (s t : Reset.Term ℕ)
    (left right : List (GuardRecord.Record D.length))
    (hs : left.map (fun r => (D.get r.1, SupportIndex.expand D r.2)) = s.guardEntries)
    (ht : right.map (fun r => (D.get r.1, SupportIndex.expand D r.2)) = t.guardEntries)
    (hcover : s.varFinset ∪ t.varFinset ⊆ D.toFinset) :
    let a : GuardDescriptor := ⟨D, hD, left⟩
    let b : GuardDescriptor := ⟨D, hD, right⟩
    (∀ i : Fin D.length, a.normalize.guards i = b.normalize.guards i) ↔ s.table = t.table := by
  let a : GuardDescriptor := ⟨D, hD, left⟩
  let b : GuardDescriptor := ⟨D, hD, right⟩
  change (∀ i : Fin D.length, a.normalize.guards i = b.normalize.guards i) ↔ _
  have hleft (i : Fin D.length) :
      (a.normalize.guards i).image (SupportIndex.expand D) = s.table (D.get i) := by
    rw [GuardDescriptor.expanded_guards_normalize a i]
    change Reset.Term.minimize (((left.map _).filter _).map Prod.snd).toFinset = _
    rw [hs]
    exact (s.table_eq_entries _).symm
  have hright (i : Fin D.length) :
      (b.normalize.guards i).image (SupportIndex.expand D) = t.table (D.get i) := by
    rw [GuardDescriptor.expanded_guards_normalize b i]
    change Reset.Term.minimize (((right.map _).filter _).map Prod.snd).toFinset = _
    rw [ht]
    exact (t.table_eq_entries _).symm
  have hinj : Function.Injective (SupportIndex.expand D) := by
    intro A B h
    have hc := congrArg (SupportIndex.compress D) h
    simpa only [SupportIndex.compress_expand D hD] using hc
  constructor
  · intro he
    funext j
    by_cases hj : j ∈ D
    · obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hj
      rw [← hleft i, ← hright i, he i]
    · have hns : j ∉ s.varFinset := fun hs => hj (List.mem_toFinset.mp
        (hcover (Finset.mem_union_left _ hs)))
      have hnt : j ∉ t.varFinset := fun ht => hj (List.mem_toFinset.mp
        (hcover (Finset.mem_union_right _ ht)))
      rw [s.table_eq_empty_of_not_mem j hns, t.table_eq_empty_of_not_mem j hnt]
  · intro he i
    apply Finset.image_injective hinj
    rw [hleft, hright, he]

/-- The executable checker compares exactly canonical tables; it supplies
both compressed occurrence lists itself from the shared actual support. -/
theorem check_eq_true (s t : Reset.Term ℕ) : check s t = true ↔ s.table = t.table := by
  let D := labels s t
  have hD : D.Nodup := labels_nodup s t
  have hscover : s.varFinset ⊆ D.toFinset := by
    rw [labels_toFinset]
    exact Finset.subset_union_left
  have htcover : t.varFinset ⊆ D.toFinset := by
    rw [labels_toFinset]
    exact Finset.subset_union_right
  obtain ⟨left, hl, _, hs⟩ := SupportIndex.compress_guardEntries_of_cover s D hD hscover
  obtain ⟨right, hr, _, ht⟩ := SupportIndex.compress_guardEntries_of_cover t D hD htcover
  have hcover : s.varFinset ∪ t.varFinset ⊆ D.toFinset := by rw [labels_toFinset]
  have hnorm := normalized_equal_iff D hD s t left right hs ht hcover
  dsimp only at hnorm
  rw [← hnorm]
  simp [check, D, hl, hr, List.all_eq_true, List.mem_ofFn]

/-- Equality holds on every mixed winner-set valuation exactly when the
finite checker succeeds, for every role set containing three distinct roles. -/
theorem check_iff_eval {Role : Type*} (three : Fin 3 ↪ Role) (s t : Reset.Term ℕ) :
    check s t = true ↔ ∀ v : ℕ → WinnerSet Role, s.eval v = t.eval v :=
  (check_eq_true s t).trans (s.eval_eq_iff_table t three).symm

/-- Complete binary equation language, including rejection of malformed
framing and malformed syntax on either side. -/
theorem checkWord_eq_true {Role : Type*} (three : Fin 3 ↪ Role) (word : List Bool) :
    checkWord word = true ↔ ∃ s t : Reset.Term ℕ,
      word = pair (TermCode.encode s) (TermCode.encode t) ∧
      ∀ v : ℕ → WinnerSet Role, s.eval v = t.eval v := by
  constructor
  · intro h
    unfold checkWord at h
    cases hp : unpair? word with
    | none => simp [hp] at h
    | some p =>
      cases hs : TermCode.decode p.1 with
      | none => simp [hp, hs] at h
      | some s =>
        cases ht : TermCode.decode p.2 with
        | none => simp [hp, hs, ht] at h
        | some t =>
          simp only [hp, hs, ht] at h
          refine ⟨s, t, ?_, (check_iff_eval three s t).mp h⟩
          have he := eq_pair_of_unpair?_eq_some (x := p.1) (y := p.2) hp
          rw [← TermCode.encode_of_decode hs, ← TermCode.encode_of_decode ht] at he
          exact he
  · rintro ⟨s, t, rfl, he⟩
    simp only [checkWord, unpair?_pair, TermCode.decode_encode]
    exact (check_iff_eval three s t).mpr he

end KFOL.Algorithms.ResetEquation
