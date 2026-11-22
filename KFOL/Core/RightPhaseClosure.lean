module

public import Mathlib.Data.Set.Lattice.Order

/-! # Right-phase closures in the three-owner selector construction

Each rail group can add enabled heads only once the opposite group is full.
The activation comparison preserves those foreign postings that fill the
second group and hit the designated pair of the first group.
-/

@[expose] public section
namespace KFOL.Core.RightPhaseClosure

variable {Input : Type*}

/-- Add the enabled heads whose opposite groups are full. -/
noncomputable def close (right scratch enabledRight enabledScratch seed : Set Input) : Set Input := by
  classical
  exact seed ∪ (if scratch ⊆ seed then enabledRight else ∅) ∪
    (if right ⊆ seed then enabledScratch else ∅)

theorem subset_close (right scratch enabledRight enabledScratch seed : Set Input) :
    seed ⊆ close right scratch enabledRight enabledScratch seed :=
  fun _ h => Or.inl (Or.inl h)

theorem close_eq_self {right scratch enabledRight enabledScratch seed : Set Input}
    (hr : ¬ right ⊆ seed) (hs : ¬ scratch ⊆ seed) :
    close right scratch enabledRight enabledScratch seed = seed := by
  simp [close, hr, hs]

theorem close_monotone (right scratch enabledRight enabledScratch : Set Input) :
    Monotone (close right scratch enabledRight enabledScratch) := by
  classical
  intro s t hst
  refine Set.union_subset_union (Set.union_subset_union hst ?_) ?_
  · by_cases hs : scratch ⊆ s
    · simp [hs, hs.trans hst]
    · simp [hs]
  · by_cases hr : right ⊆ s
    · simp [hr, hr.trans hst]
    · simp [hr]

theorem close_idempotent {right scratch enabledRight enabledScratch seed : Set Input}
    (her : enabledRight ⊆ right) (hes : enabledScratch ⊆ scratch) :
    close right scratch enabledRight enabledScratch
        (close right scratch enabledRight enabledScratch seed) =
      close right scratch enabledRight enabledScratch seed := by
  classical
  let closed := close right scratch enabledRight enabledScratch seed
  have hseed : seed ⊆ closed := subset_close _ _ _ _ _
  change close right scratch enabledRight enabledScratch closed = closed
  apply Set.Subset.antisymm _ (subset_close _ _ _ _ _)
  unfold close
  refine Set.union_subset (Set.union_subset (fun _ h => h) ?_) ?_
  · by_cases hs : scratch ⊆ closed
    · rw [ite_eq_left hs]
      by_cases hs' : scratch ⊆ seed
      · exact fun x hx => by
          change x ∈ close right scratch enabledRight enabledScratch seed
          exact Or.inl (Or.inr (by simpa [hs'] using hx))
      · have hr' : right ⊆ seed := by
          by_contra hr'
          exact hs' ((close_eq_self hr' hs').symm ▸ hs)
        exact her.trans (hr'.trans hseed)
    · simp [hs]
  · by_cases hr : right ⊆ closed
    · rw [ite_eq_left hr]
      by_cases hr' : right ⊆ seed
      · exact fun x hx => by
          change x ∈ close right scratch enabledRight enabledScratch seed
          exact Or.inr (by simpa [hr'] using hx)
      · have hs' : scratch ⊆ seed := by
          by_contra hs'
          exact hr' ((close_eq_self hr' hs').symm ▸ hr)
        exact hes.trans (hs'.trans hseed)
    · simp [hr]

/-- A foreign posting set is visible to the primary comparison only when it
fills the scratch group and hits the designated right pair. -/
noncomputable def effective (pair scratch foreign : Set Input) : Set Input := by
  classical
  exact if scratch ⊆ foreign ∧ (pair ∩ foreign).Nonempty then foreign else ∅

/-- The two conditions of the one-owner activation formula for the foreign
posting set suffice for monotonicity of the effective flags. -/
theorem effective_subset_of_activation
    {right scratch enabledRight enabledScratch pair targetNative targetForeign
      sourceForeign : Set Input}
    (hpair : pair ⊆ right) (hscratch : scratch.Nonempty)
    (houtside : sourceForeign \ close right scratch enabledRight enabledScratch targetNative ⊆
      targetForeign \ close right scratch enabledRight enabledScratch targetNative)
    (hspans : close right scratch enabledRight enabledScratch
      (close right scratch enabledRight enabledScratch targetNative \ sourceForeign) =
        close right scratch enabledRight enabledScratch targetNative) :
    effective pair scratch sourceForeign ⊆ effective pair scratch targetForeign := by
  classical
  by_cases hs : scratch ⊆ sourceForeign ∧ (pair ∩ sourceForeign).Nonempty
  · obtain ⟨x, hxpair, hxsource⟩ := hs.2
    obtain ⟨y, hyscratch⟩ := hscratch
    let closed := close right scratch enabledRight enabledScratch targetNative
    change close right scratch enabledRight enabledScratch (closed \ sourceForeign) = closed at hspans
    rw [close_eq_self (fun h => (h (hpair hxpair)).2 hxsource)
      (fun h => (h hyscratch).2 (hs.1 hyscratch))] at hspans
    have hsub : sourceForeign ⊆ targetForeign := by
      intro z hz
      have hnot : z ∉ closed := by
        intro h
        exact ((hspans.symm ▸ h : z ∈ closed \ sourceForeign).2 hz)
      exact (houtside ⟨hz, hnot⟩).1
    have ht : scratch ⊆ targetForeign ∧ (pair ∩ targetForeign).Nonempty :=
      ⟨hs.1.trans hsub, ⟨x, hxpair, hsub hxsource⟩⟩
    simpa [effective, hs, ht] using hsub
  · simp [effective, hs]

end KFOL.Core.RightPhaseClosure
