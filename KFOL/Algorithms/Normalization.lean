module

public import KFOL.Algorithms.GuardDescriptor

/-! # Listed-record normalization and faithful natural-name table expansion -/

@[expose] public section

namespace KFOL.Algorithms.GuardDescriptor

open _root_.KFOL.Words

@[simp] theorem labels_normalize (d : GuardDescriptor) : d.normalize.labels = d.labels := rfl

/-- The executable list filter is exactly mathematical antichain minimization. -/
theorem guards_normalize (d : GuardDescriptor) (j : Fin d.labels.length) :
    d.normalize.guards j = Reset.Term.minimize (d.guards j) := by
  ext A
  rw [mem_guards d.normalize j A, Reset.Term.mem_minimize, mem_guards d j A]
  change (j, A) ∈ d.records.filter _ ↔ _
  simp only [List.mem_filter, decide_eq_true_eq]
  apply and_congr_right
  intro _
  constructor
  · intro h B hB hBA
    exact h (j, B) ((d.mem_guards j B).mp hB) rfl hBA
  · intro h q hq hqj hqA
    apply h q.2
    · rw [mem_guards, ← hqj]
      exact hq
    · exact hqA

theorem enabled_normalize (d : GuardDescriptor) (r j : Fin d.labels.length)
    (B : Set (Fin d.labels.length)) :
    (d.normalize.table r).Enabled B j ↔ (d.table r).Enabled B j := by
  change (∃ A : Finset (Fin d.labels.length), A ∈ d.normalize.guards j ∧
    (A : Set (Fin d.labels.length)) ⊆ B) ↔ _
  rw [guards_normalize]
  exact Reset.Term.exists_minimize_iff _ B

theorem records_normalize_sublist (d : GuardDescriptor) :
    d.normalize.records.Sublist d.records := List.filter_sublist

theorem normalize_idempotent (d : GuardDescriptor) : d.normalize.normalize = d.normalize := by
  have hr : d.normalize.normalize.records = d.normalize.records := by
    change d.normalize.records.filter _ = d.normalize.records
    apply List.filter_eq_self.mpr
    intro p hp
    apply decide_eq_true
    intro q hq hqp hsub
    have hpmin := of_decide_eq_true (List.mem_filter.mp hp).2
    exact hpmin q (List.mem_of_mem_filter hq) hqp hsub
  exact congrArg (fun records => GuardDescriptor.mk d.labels d.distinct records) hr

theorem length_normalize_le (d : GuardDescriptor) : (encode d.normalize).length ≤ (encode d).length := by
  rw [length_encode, length_encode, GuardRecord.length_encodeList,
    GuardRecord.length_encodeList]
  change 4 * (d.labels.map Nat.size).sum + 4 * d.labels.length + 2 + _ ≤ _
  have h := (d.records_normalize_sublist.map
    (fun r => 2 * d.labels.length + 4 * r.1.val.size + 6)).sum_le_sum (fun _ _ => Nat.zero_le _)
  exact Nat.add_le_add_left h _

/-- Expanding the normalized guards gives the minimal natural-name guards
of the expanded raw occurrence list, even with unused dictionary positions. -/
theorem expanded_guards_normalize (d : GuardDescriptor) (j : Fin d.labels.length) :
    (d.normalize.guards j).image (SupportIndex.expand d.labels) =
      Reset.Term.minimize
        ((((d.records.map (fun r => (d.labels.get r.1, SupportIndex.expand d.labels r.2))).filter
          (fun p => p.1 = d.labels.get j)).map Prod.snd).toFinset) := by
  have hraw : (d.guards j).image (SupportIndex.expand d.labels) =
      (((d.records.map (fun r => (d.labels.get r.1, SupportIndex.expand d.labels r.2))).filter
        (fun p => p.1 = d.labels.get j)).map Prod.snd).toFinset := by
    ext A
    simp only [Finset.mem_image, mem_guards, List.mem_toFinset, List.mem_map, List.mem_filter,
      decide_eq_true_eq]
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact ⟨(d.labels.get j, SupportIndex.expand d.labels B),
        ⟨⟨(j, B), hB, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨k, B⟩, ⟨⟨q, hq, he⟩, hk⟩, hB⟩
      have hj : q.1 = j := d.distinct.get_inj_iff.mp ((congrArg Prod.fst he).trans hk)
      have hA := (congrArg Prod.snd he).trans hB
      refine ⟨q.2, ?_, hA⟩
      rw [← hj]
      exact hq
  rw [guards_normalize, ← hraw]
  exact (Reset.Term.minimize_image d.labels.get (fun _ _ h => d.distinct.get_inj_iff.mp h) _).symm

/-- A faithful raw representation of an actual term normalizes to a
realizable finite-index table. The proof transports syntax itself back to
dictionary positions; no realizability certificate is assumed. -/
theorem check_normalize_of_entries (d : GuardDescriptor) (t : Reset.Term ℕ)
    (he : d.records.map (fun r => (d.labels.get r.1, SupportIndex.expand d.labels r.2)) =
      t.guardEntries) : d.normalize.check = true := by
  have hlen : d.records.length = t.leafCount := by
    have h := congrArg List.length he
    simpa only [List.length_map, Reset.Term.length_guardEntries] using h
  cases hr : d.records with
  | nil =>
    have hp := t.leafCount_pos
    rw [hr] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons p rest =>
    let f : ℕ → Fin d.labels.length := fun j => (SupportIndex.locate d.labels j).getD p.1
    have hf (i : Fin d.labels.length) : f (d.labels.get i) = i := by
      dsimp only [f]
      rw [(SupportIndex.locate_eq_some_iff d.labels d.distinct (d.labels.get i) i).mpr rfl]
      rfl
    have himage (A : Finset (Fin d.labels.length)) : (SupportIndex.expand d.labels A).image f = A := by
      simp only [SupportIndex.expand, Finset.image_image, Function.comp_def, hf, Finset.image_id']
    let u : Reset.Term (Fin d.labels.length) := t.relabel f
    have hu : u.guardEntries = d.records := by
      rw [Reset.Term.guardEntries_relabel, ← he, List.map_map]
      simp only [Function.comp_def, hf, himage, Prod.eta, List.map_id_fun']
      rfl
    have hraw (j : Fin d.labels.length) : u.guards j = d.guards j := by
      ext A
      rw [← u.mem_guardEntries j A, hu, d.mem_guards]
    have hcanon : u.table = d.normalize.guards := by
      funext j
      rw [Reset.Term.table, hraw, guards_normalize]
    apply d.normalize.check_eq_true.mpr
    refine ⟨u.root, ?_⟩
    change (Reset.GuardTable.mk u.root d.normalize.guards).WellFormed
    rw [← hcanon]
    exact u.guardTable_wellFormed

/-- Original extraction and normalization recover exactly the independently
defined canonical tables at every dictionary position. -/
theorem normalized_extraction {word output : List Bool}
    (h : TermCode.extract word = some output) :
    ∃ (d : GuardDescriptor) (t : Reset.Term ℕ), decode output = some d ∧
      TermCode.decode word = some t ∧ d.labels = SupportIndex.labels t ∧
      d.normalize.check = true ∧ ∀ j : Fin d.labels.length,
        (d.normalize.guards j).image (SupportIndex.expand d.labels) = t.table (d.labels.get j) := by
  obtain ⟨d, t, hd, ht, hl, hr⟩ := decode_extraction h
  refine ⟨d, t, hd, ht, hl, check_normalize_of_entries d t hr, ?_⟩
  intro j
  rw [expanded_guards_normalize, hr]
  exact (t.table_eq_entries _).symm

@[simp] theorem normalizeWord_encode (d : GuardDescriptor) :
    normalizeWord (encode d) = some (encode d.normalize) := by
  simp [normalizeWord]

theorem normalizeWord_eq_none_iff (word : List Bool) : normalizeWord word = none ↔ decode word = none := by
  cases hd : decode word <;> simp [normalizeWord, hd]

theorem normalizeWord_spec {word output : List Bool} (h : normalizeWord word = some output) :
    ∃ d : GuardDescriptor, decode word = some d ∧ output = encode d.normalize ∧
      decode output = some d.normalize ∧ output.length ≤ word.length := by
  unfold normalizeWord at h
  obtain ⟨d, hd, he⟩ := Option.bind_eq_some_iff.mp h
  have he := Option.some.inj he
  refine ⟨d, hd, he.symm, ?_, ?_⟩
  · rw [← he]
    exact decode_encode _
  · rw [← he, ← encode_of_decode hd]
    exact length_normalize_le d

theorem normalizeWord_idempotent {word output : List Bool} (h : normalizeWord word = some output) :
    normalizeWord output = some output := by
  obtain ⟨d, _, ho, _⟩ := normalizeWord_spec h
  rw [ho, normalizeWord_encode, normalize_idempotent]

end KFOL.Algorithms.GuardDescriptor
