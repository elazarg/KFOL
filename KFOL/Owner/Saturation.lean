module

public import KFOL.Definitions.Owner

/-! Exact saturation updates, strengthening, progress and explicit finite clocks. -/

@[expose] public section

namespace KFOL.Owner

universe v

namespace SaturationState

variable {Var : Type v} [DecidableEq Var]

omit [DecidableEq Var] in
@[ext] theorem ext {S R : SaturationState Var} (hm : S.many = R.many) (ho : S.outside = R.outside) : S = R := by
  cases S
  cases R
  cases hm
  cases ho
  rfl

@[simp] theorem update_many (S : SaturationState Var) (w z : Var) :
    (S.update w z).many = insert w S.many := rfl

@[simp] theorem update_outside (S : SaturationState Var) (w z : Var) :
    (S.update w z).outside = (S.outside ∪ {w, z}) \ insert w S.many := rfl

theorem update_union (S : SaturationState Var) (w z : Var) :
    (S.update w z).many ∪ (S.update w z).outside = S.many ∪ S.outside ∪ {w, z} := by
  ext x
  simp only [update_many, update_outside, Finset.mem_insert, Finset.mem_union,
    Finset.mem_sdiff, Finset.mem_singleton]
  tauto

theorem update_disjoint (S : SaturationState Var) (w z : Var) :
    Disjoint (S.update w z).many (S.update w z).outside := by
  apply Finset.disjoint_left.mpr
  intro x hx ho
  exact (Finset.mem_sdiff.mp ho).2 hx

theorem below_update (S : SaturationState Var) (w z : Var) : S.Below (S.update w z) := by
  constructor
  · exact Finset.subset_insert _ _
  · rw [update_union]
    exact Finset.subset_union_left

theorem rank_update_lt (S : SaturationState Var) (w z : Var)
    (hdis : Disjoint S.many S.outside) (hne : S.update w z ≠ S) :
    S.rank < (S.update w z).rank := by
  have hm := S.below_update w z
  have hcm := Finset.card_le_card hm.1
  have hcu := Finset.card_le_card hm.2
  by_contra hn
  have hmEq : S.many = (S.update w z).many := Finset.eq_of_subset_of_card_le hm.1 (by
    unfold rank at hn
    omega)
  have huEq : S.many ∪ S.outside = (S.update w z).many ∪ (S.update w z).outside :=
    Finset.eq_of_subset_of_card_le hm.2 (by unfold rank at hn; omega)
  have hoEq : S.outside = (S.update w z).outside := by
    rw [← Finset.union_sdiff_cancel_left hdis, huEq, hmEq,
      Finset.union_sdiff_cancel_left (S.update_disjoint w z)]
  exact hne (ext hmEq hoEq).symm

theorem rank_le_of_subset (S : SaturationState Var) (P : Finset Var)
    (h : S.many ∪ S.outside ⊆ P) : S.rank ≤ 2 * P.card := by
  have hu := Finset.card_le_card h
  have hm := Finset.card_le_card ((Finset.subset_union_left : S.many ⊆ S.many ∪ S.outside).trans h)
  unfold rank
  omega

/-- The written rank 2|C|+|D| on disjoint accumulated layers. -/
theorem rank_eq (S : SaturationState Var) (hd : Disjoint S.many S.outside) :
    S.rank = 2 * S.many.card + S.outside.card := by
  unfold rank
  rw [Finset.card_union_of_disjoint hd]
  omega

theorem below_refl (S : SaturationState Var) : S.Below S := ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

theorem below_trans {S R Q : SaturationState Var} (hSR : S.Below R) (hRQ : R.Below Q) : S.Below Q :=
  ⟨hSR.1.trans hRQ.1, hSR.2.trans hRQ.2⟩

theorem below_antisymm {S R : SaturationState Var} (hS : Disjoint S.many S.outside)
    (hR : Disjoint R.many R.outside) (hSR : S.Below R) (hRS : R.Below S) : S = R := by
  have hm := Finset.Subset.antisymm hSR.1 hRS.1
  have hu := Finset.Subset.antisymm hSR.2 hRS.2
  apply ext hm
  rw [← Finset.union_sdiff_cancel_left hS, hu, hm, Finset.union_sdiff_cancel_left hR]

theorem update_mono {S R : SaturationState Var} (h : S.Below R) (w z : Var) :
    (S.update w z).Below (R.update w z) := by
  constructor
  · exact Finset.insert_subset_insert w h.1
  · rw [update_union, update_union]
    exact Finset.union_subset_union h.2 (Finset.Subset.refl _)

end SaturationState

namespace GuardTable

variable {Var : Type v} [DecidableEq Var]

/-- Permitted contributions remain permitted when the accumulated tests strengthen. -/
theorem permitted_mono (T : GuardTable Var) (j : Var) (S R : SaturationState Var)
    (hSR : S.Below R) (h : T.Permitted j S.many S.outside) : T.Permitted j R.many R.outside := by
  obtain ⟨g, hg, hm, ho⟩ := h
  refine ⟨g, hg, hm.trans hSR.1, ?_⟩
  intro i hi
  rcases Finset.mem_union.mp (ho hi) with hi | hi
  · exact Finset.mem_union_left _ (hSR.2 hi)
  · exact Finset.mem_union_right _ hi

/-- The Boolean scan returns exactly an allowed changing update. -/
theorem next_spec (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) {p : Var × Var} (h : T.next positions j g S = some p) :
    T.UpdateAllowed j g S p.1 p.2 := by
  exact of_decide_eq_true (List.find?_some
    (p := fun p : Var × Var => decide (T.UpdateAllowed j g S p.1 p.2)) (a := p) h)

/-- Every run state has disjoint test layers. -/
theorem run_disjoint (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var) (k : ℕ) :
    Disjoint (T.run positions j g k).1.many (T.run positions j g k).1.outside := by
  induction k with
  | zero => exact Finset.disjoint_empty_right _
  | succ k ih =>
    cases hn : T.next positions j g (T.run positions j g k).1 with
    | none => simpa only [run, hn] using ih
    | some p => simpa only [run, hn] using SaturationState.update_disjoint (T.run positions j g k).1 p.1 p.2

/-- Ambiguous positions stay inside A, and all tests stay inside A∪B∪{j}. -/
theorem run_subsets (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (hr : T.root ∈ g.many) (k : ℕ) :
    (T.run positions j g k).1.many ⊆ g.many ∧
      (T.run positions j g k).1.many ∪ (T.run positions j g k).1.outside ⊆ target j g := by
  induction k with
  | zero =>
    constructor
    · exact Finset.singleton_subset_iff.mpr hr
    · change ({T.root} ∪ ∅ : Finset Var) ⊆ target j g
      rw [Finset.union_empty]
      apply Finset.singleton_subset_iff.mpr
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hr)
  | succ k ih =>
    cases hn : T.next positions j g (T.run positions j g k).1 with
    | none => simpa only [run, hn] using ih
    | some p =>
      have hp := T.next_spec positions j g _ hn
      simp only [run, hn]
      constructor
      · exact Finset.insert_subset_iff.mpr ⟨hp.1, ih.1⟩
      · rw [SaturationState.update_union]
        apply Finset.union_subset ih.2
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp.1)
        · exact hp.2.1

/-- Every logged frame uses only the target's permitted positive/negative positions. -/
theorem run_frames (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var) (k : ℕ) :
    ∀ p ∈ (T.run positions j g k).2, p.1 ∈ g.many ∧ p.2 ∈ target j g := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    cases hn : T.next positions j g (T.run positions j g k).1 with
    | none => simpa only [run, hn] using ih
    | some q =>
      simp only [run, hn, List.mem_append, List.mem_singleton]
      intro p hp
      rcases hp with hp | rfl
      · exact ih p hp
      · have hq := T.next_spec positions j g _ hn
        exact ⟨hq.1, hq.2.1⟩

/-- The recorded path length is bounded by the same increasing rank. -/
theorem run_frames_rank (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var) (k : ℕ) :
    (T.run positions j g k).2.length + 2 ≤ (T.run positions j g k).1.rank := by
  induction k with
  | zero => simp [run, SaturationState.initial, SaturationState.rank]
  | succ k ih =>
    cases hn : T.next positions j g (T.run positions j g k).1 with
    | none => simpa only [run, hn] using ih
    | some p =>
      have hp := T.next_spec positions j g _ hn
      have hlt := SaturationState.rank_update_lt _ p.1 p.2 (T.run_disjoint positions j g k) hp.2.2.2.2
      simp only [run, hn, List.length_append, List.length_singleton]
      omega

/-- At most 2n actual frames are recorded, including all copied syntax nodes
in the later size calculation. -/
theorem run_frames_length_le (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (hr : T.root ∈ g.many) (hcover : target j g ⊆ positions.toFinset) (k : ℕ) :
    (T.run positions j g k).2.length ≤ 2 * positions.length := by
  have hlen := T.run_frames_rank positions j g k
  have hs := (T.run_subsets positions j g hr k).2.trans hcover
  have hb := SaturationState.rank_le_of_subset _ _ hs
  have hc := List.toFinset_card_le positions
  omega

/-- Progress is strict until a fixed point is reached. -/
theorem run_progress_or_fixed (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var) (k : ℕ) :
    k + 2 ≤ (T.run positions j g k).1.rank ∨
      T.next positions j g (T.run positions j g k).1 = none := by
  induction k with
  | zero => left; simp [run, SaturationState.initial, SaturationState.rank]
  | succ k ih =>
    cases hn : T.next positions j g (T.run positions j g k).1 with
    | none => right; simp only [run, hn]
    | some p =>
      have hp := T.next_spec positions j g _ hn
      have hlt := SaturationState.rank_update_lt _ p.1 p.2 (T.run_disjoint positions j g k) hp.2.2.2.2
      have hprev : k + 2 ≤ (T.run positions j g k).1.rank := by
        rcases ih with h | h
        · exact h
        · rw [hn] at h
          cases h
      left
      simpa only [run, hn] using (show k + 1 + 2 ≤ ((T.run positions j g k).1.update p.1 p.2).rank by omega)

/-- The exact 2n scan clock suffices whenever the input listing covers the
finite target. It never depends on the largest numeric variable label. -/
theorem run_fixed (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (hr : T.root ∈ g.many) (hcover : target j g ⊆ positions.toFinset) :
    T.next positions j g (T.run positions j g (2 * positions.length)).1 = none := by
  rcases T.run_progress_or_fixed positions j g (2 * positions.length) with h | h
  · have hs := (T.run_subsets positions j g hr (2 * positions.length)).2.trans hcover
    have hb := SaturationState.rank_le_of_subset _ _ hs
    have hc := List.toFinset_card_le positions
    omega
  · exact h

/-- Closure under every semantically enabled update, independently of scan order. -/
def Closed (T : GuardTable Var) (j : Var) (g : GuardPair Var) (S : SaturationState Var) : Prop :=
  ∀ w ∈ g.many, ∀ z ∈ target j g,
    T.Permitted w S.many (S.outside ∪ {w, z}) →
    T.Permitted z S.many (S.outside ∪ {w, z}) → S.update w z = S

/-- Appending the same two non-owner tests preserves strengthening. -/
theorem permitted_add_pair_mono (T : GuardTable Var) (i w z : Var)
    {S R : SaturationState Var} (h : S.Below R)
    (hp : T.Permitted i S.many (S.outside ∪ {w, z})) :
    T.Permitted i R.many (R.outside ∪ {w, z}) := by
  apply T.permitted_mono i ⟨S.many, S.outside ∪ {w, z}⟩ ⟨R.many, R.outside ∪ {w, z}⟩ ?_ hp
  refine ⟨h.1, ?_⟩
  simpa only [Finset.union_assoc] using Finset.union_subset_union h.2 (Finset.Subset.refl {w, z})

/-- Exhaustion of the explicit pair scan is exactly semantic closure. -/
theorem next_eq_none_iff (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    (S : SaturationState Var) (hcover : target j g ⊆ positions.toFinset) :
    T.next positions j g S = none ↔ T.Closed j g S := by
  rw [next, List.find?_eq_none]
  constructor
  · intro h w hw z hz hpw hpz
    by_contra hn
    have hwP : w ∈ positions := List.mem_toFinset.mp (hcover (Finset.mem_union_left _ (Finset.mem_union_left _ hw)))
    have hzP : z ∈ positions := List.mem_toFinset.mp (hcover hz)
    exact h (w, z) (List.mem_product.mpr ⟨hwP, hzP⟩) (by
      simpa only [decide_eq_true_eq] using (show T.UpdateAllowed j g S w z from ⟨hw, hz, hpw, hpz, hn⟩))
  · intro h p _ hp
    have hp := of_decide_eq_true hp
    exact hp.2.2.2.2 (h p.1 hp.1 p.2 hp.2.1 hp.2.2.1 hp.2.2.2.1)

/-- Every chosen update lies below every closed extension of the initial tests.
Thus the scan order supplies an execution, not an additional mathematical choice. -/
theorem run_le_closed (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var)
    {R : SaturationState Var} (hinit : (SaturationState.initial T.root).Below R)
    (hc : T.Closed j g R) (k : ℕ) : (T.run positions j g k).1.Below R := by
  induction k with
  | zero => exact hinit
  | succ k ih =>
    cases hn : T.next positions j g (T.run positions j g k).1 with
    | none => simpa only [run, hn] using ih
    | some p =>
      have hp := T.next_spec positions j g _ hn
      have hR := hc p.1 hp.1 p.2 hp.2.1
        (T.permitted_add_pair_mono p.1 p.1 p.2 ih hp.2.2.1)
        (T.permitted_add_pair_mono p.2 p.1 p.2 ih hp.2.2.2.1)
      simpa only [run, hn, hR] using SaturationState.update_mono ih p.1 p.2

/-- Every intermediate run state strengthens the initial tests. -/
theorem initial_le_run (T : GuardTable Var) (positions : List Var) (j : Var) (g : GuardPair Var) (k : ℕ) :
    (SaturationState.initial T.root).Below (T.run positions j g k).1 := by
  induction k with
  | zero => exact SaturationState.below_refl _
  | succ k ih =>
    cases hn : T.next positions j g (T.run positions j g k).1 with
    | none => simpa only [run, hn] using ih
    | some p => simpa only [run, hn] using SaturationState.below_trans ih (SaturationState.below_update _ p.1 p.2)

/-- The fixed point is independent of dictionary order and of unused listed
positions. Each list need only cover the finite target. -/
theorem run_order_independent (T : GuardTable Var) (left right : List Var) (j : Var) (g : GuardPair Var)
    (hr : T.root ∈ g.many) (hl : target j g ⊆ left.toFinset) (hright : target j g ⊆ right.toFinset) :
    (T.run left j g (2 * left.length)).1 = (T.run right j g (2 * right.length)).1 := by
  apply SaturationState.below_antisymm (T.run_disjoint ..) (T.run_disjoint ..)
  · exact T.run_le_closed left j g (T.initial_le_run right j g _)
      ((T.next_eq_none_iff right j g _ hright).mp (T.run_fixed right j g hr hright)) _
  · exact T.run_le_closed right j g (T.initial_le_run left j g _)
      ((T.next_eq_none_iff left j g _ hl).mp (T.run_fixed left j g hr hl)) _

end GuardTable
end KFOL.Owner
