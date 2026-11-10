module
public import KFOL.Algorithms.GuardDescriptor
/-! # Raw-record synthesis with a physical-width greedy clock

Each original guard record contributes one path, in original list order and
with repetitions retained. Extra greedy steps after completing a target do
nothing, so the native width-clocked construction realizes the same table.
-/
@[expose] public section
namespace KFOL.Reset.GuardTable
universe v
variable {Var : Type v} [LinearOrder Var] (G : GuardTable Var)

/-- Once all target positions have been collected, the greedy list is fixed. -/
theorem greedyOrder_succ_eq_of_support {A : Finset Var} {k : ℕ}
    (hs : insert G.root (G.greedyOrder A k).toFinset = A) :
    G.greedyOrder A (k+1) = G.greedyOrder A k := by
  have hc : G.greedyCandidates A (G.greedyOrder A k) = ∅ := by
    ext j
    simp [mem_greedyCandidates,hs]
    tauto
  simp only [greedyOrder,hc,Finset.not_nonempty_empty,dite_false]

/-- The target-cardinality bound is sufficient for every larger clock too. -/
theorem greedyOrder_eq_of_card_le {A : Finset Var} (hr : G.root ∈ A)
    (hA : G.Constructible A) {k : ℕ} (hk : A.card ≤ k) :
    G.greedyOrder A k = G.greedyOrder A A.card := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k _ ih =>
    calc G.greedyOrder A (k+1) = G.greedyOrder A k :=
      G.greedyOrder_succ_eq_of_support (by rw [ih]; exact G.greedyOrder_support hr hA)
      _ = _ := ih

/-- A listed selector remains exact when the greedy clock is any sufficient
physical dimension, rather than the target's cardinality. -/
theorem synthesisPath_steps_spec [Fintype Var] (h : G.WellFormed) (j : Var)
    {A : Finset Var} (hA : A ∈ G.guards j) (steps : ℕ) (hsteps : (insert j A).card ≤ steps) :
    let t := Term.pathTerm G.root (G.greedyOrder (insert j A) steps).reverse
    t.root = G.root ∧ t.varFinset = insert j A ∧
      (∀ B k, t.Selected B k → G.Enabled B k) ∧ t.size + 1 ≤ 2 * Fintype.card Var := by
  have hb : G.Constructible (insert j A) :=
    .insert j (h.2.2.2.2 _ _ hA) (h.2.2.2.1 _ _ hA) ⟨A,hA,subset_rfl⟩
  have hr := hb.root_mem h.2.2.1 (Finset.insert_nonempty _ _)
  have he := G.greedyOrder_eq_of_card_le hr hb hsteps
  dsimp only
  rw [he]
  exact G.synthesisPath_spec h j hA
end KFOL.Reset.GuardTable

namespace KFOL.Algorithms.GuardDescriptor
open KFOL.Reset

/-- One literal path for one original guard record. -/
def recordPath (d : GuardDescriptor) (root : Fin d.labels.length)
    (p : GuardRecord.Record d.labels.length) : Reset.Term (Fin d.labels.length) :=
  Reset.Term.pathTerm root
    ((d.table root).greedyOrder (insert p.1 p.2) d.labels.length).reverse

/-- Preserve raw record order and repetitions; no mathematical sorting or
set enumeration is hidden in the executable output construction. -/
def recordPaths (d : GuardDescriptor) (root : Fin d.labels.length) :
    List (Reset.Term (Fin d.labels.length)) := d.records.map (recordPath d root)

/-- Join the original-record paths against the chosen root projection. -/
def recordTerm (d : GuardDescriptor) (root : Fin d.labels.length) : Reset.Term (Fin d.labels.length) :=
  Reset.Term.joinPaths root (recordPaths d root)

@[simp] theorem mem_recordPaths (d : GuardDescriptor) (root : Fin d.labels.length)
    (t : Reset.Term (Fin d.labels.length)) :
    t ∈ recordPaths d root ↔ ∃ p ∈ d.records, recordPath d root p = t := by
  simp only [recordPaths,List.mem_map]

@[simp] theorem length_recordPaths (d : GuardDescriptor) (root : Fin d.labels.length) :
    (recordPaths d root).length = d.records.length := by simp [recordPaths]

theorem recordPath_spec (d : GuardDescriptor) (root : Fin d.labels.length)
    (h : (d.table root).WellFormed) (p : GuardRecord.Record d.labels.length) (hp : p ∈ d.records) :
    (recordPath d root p).root = root ∧
      (recordPath d root p).varFinset = insert p.1 p.2 ∧
      (∀ B j, (recordPath d root p).Selected B j → (d.table root).Enabled B j) ∧
      (recordPath d root p).size + 1 ≤ 2 * d.labels.length := by
  have hguard : p.2 ∈ (d.table root).guards p.1 := (d.mem_guards p.1 p.2).mpr hp
  have hsteps : (insert p.1 p.2).card ≤ d.labels.length := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (insert p.1 p.2)
  simpa only [recordPath,table,Fintype.card_fin] using
    (d.table root).synthesisPath_steps_spec h p.1 hguard d.labels.length hsteps

/-- The exact raw-list construction returns the required original canonical
table and the compact primitive-tree bound, even with repeated records. -/
theorem recordTerm_spec (d : GuardDescriptor) (root : Fin d.labels.length)
    (h : (d.table root).WellFormed) :
    (recordTerm d root).root = root ∧ (recordTerm d root).table = d.guards ∧
      (recordTerm d root).size ≤ 1 + 2 * d.labels.length * d.records.length := by
  have hroots : ∀ t ∈ recordPaths d root, t.root = root := by
    intro t ht
    obtain ⟨p,hp,rfl⟩ := (mem_recordPaths d root t).mp ht
    exact (recordPath_spec d root h p hp).1
  have hsel : ∀ B j, (recordTerm d root).Selected B j ↔ (d.table root).Enabled B j := by
    intro B j
    rw [recordTerm,Reset.Term.selected_joinPaths _ _ _ _ hroots]
    constructor
    · rintro (he | ⟨s,hs,hj⟩)
      · subst j
        exact ⟨∅,by
          change ∅ ∈ (d.table root).guards (d.table root).root
          rw [h.2.1]
          simp,by simp⟩
      · obtain ⟨p,hp,rfl⟩ := (mem_recordPaths d root s).mp hs
        exact (recordPath_spec d root h p hp).2.2.1 B j hj
    · rintro ⟨A,hA,hAB⟩
      have hp : (j,A) ∈ d.records := (d.mem_guards j A).mp hA
      have hs := (recordPath_spec d root h (j,A) hp).2.1
      refine Or.inr ⟨recordPath d root (j,A),
        (mem_recordPaths d root _).mpr ⟨(j,A),hp,rfl⟩,?_⟩
      apply Reset.Term.selected_of_support_insert
      · rw [hs]
        exact Finset.mem_insert_self _ _
      · rw [hs]
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact Or.inl rfl
        · exact Or.inr (hAB hk)
  refine ⟨Reset.Term.root_joinPaths _ _,(d.table root).table_eq_of_selected h.1 _ hsel,?_⟩
  have hp : ∀ t ∈ recordPaths d root, t.size + 1 ≤ 2 * d.labels.length := by
    intro t ht
    obtain ⟨p,hp,rfl⟩ := (mem_recordPaths d root t).mp ht
    exact (recordPath_spec d root h p hp).2.2.2
  have hb := Reset.Term.size_joinPaths_le root (recordPaths d root) (2 * d.labels.length) hp
  simpa only [recordTerm,length_recordPaths,Nat.mul_comm d.records.length (2 * d.labels.length)] using hb
end KFOL.Algorithms.GuardDescriptor
