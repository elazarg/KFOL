module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card

/-! # Greedy address tracks for bounded-incidence rows

A track must distinguish every pair of labels used in the same row, including
its mark. The bound depends only on the row width and label frequencies. -/

@[expose] public section
namespace KFOL.Core.AddressConflictColoring

variable {Label Row : Type*} [DecidableEq Label]

/-- Rows on which a label occurs. -/
def occurrences (rows : Finset Row) (labels : Row → Finset Label) (x : Label) : Finset Row :=
  rows.filter (fun i => x ∈ labels i)

/-- Labels that must receive a different track from `x`. -/
def neighbors (rows : Finset Row) (labels : Row → Finset Label) (x : Label) : Finset Label :=
  (occurrences rows labels x).biUnion (fun i => (labels i).erase x)

theorem mem_neighbors_iff {rows : Finset Row} {labels : Row → Finset Label} {x y : Label} :
    y ∈ neighbors rows labels x ↔ x ≠ y ∧ ∃ i ∈ rows, x ∈ labels i ∧ y ∈ labels i := by
  simp only [neighbors, Finset.mem_biUnion, occurrences, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨i, ⟨hi,hx⟩, ne,hy⟩
    exact ⟨Ne.symm ne,i,hi,hx,hy⟩
  · rintro ⟨ne,i,hi,hx,hy⟩
    exact ⟨i,⟨hi,hx⟩,Ne.symm ne,hy⟩

/-- Each occurrence can contribute at most the remaining positions of its row. -/
theorem degree_bound (rows : Finset Row) (labels : Row → Finset Label) (width frequency : ℕ)
    (size : ∀ i ∈ rows, (labels i).card ≤ width)
    (count : ∀ x, (occurrences rows labels x).card ≤ frequency) (x : Label) :
    (neighbors rows labels x).card ≤ frequency * (width - 1) := by
  apply (Finset.card_biUnion_le_card_mul _ _ (width - 1) ?_).trans
    (Nat.mul_le_mul_right _ (count x))
  intro i hi
  obtain ⟨row, mem⟩ := Finset.mem_filter.mp hi
  rw [Finset.card_erase_of_mem mem]
  exact Nat.sub_le_sub_right (size i row) 1

/-- Least unused color in a palette with one more track than the degree bound. -/
def unused {d : ℕ} (forbidden : Finset (Fin (d + 1))) (bound : forbidden.card ≤ d) :
    Fin (d + 1) :=
  (Finset.univ \ forbidden).min' (by
    apply Finset.sdiff_nonempty.mpr
    intro sub
    have h := Finset.card_le_card sub
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega)

private theorem unused_notMem {d : ℕ} (forbidden : Finset (Fin (d + 1))) (bound : forbidden.card ≤ d) :
    unused forbidden bound ∉ forbidden :=
  (Finset.mem_sdiff.mp (Finset.min'_mem _ _)).2

/-- Scan the list from right to left, recoloring its next label with the least
track absent from its neighbors. The initial color of unprocessed labels is zero. -/
def greedy {d : ℕ} (adj : Label → Finset Label) (bound : ∀ x, (adj x).card ≤ d) :
    List Label → Label → Fin (d + 1)
  | [] => fun _ => 0
  | x :: tail =>
    let previous := greedy adj bound tail
    let forbidden := (adj x).image previous
    let color := unused forbidden (Finset.card_image_le.trans (bound x))
    Function.update previous x color

private theorem greedy_proper {d : ℕ} (adj : Label → Finset Label) (bound : ∀ x, (adj x).card ≤ d)
    (symmetric : ∀ x y, y ∈ adj x → x ∈ adj y) (irreflexive : ∀ x, x ∉ adj x)
    (order : List Label) :
    ∀ x ∈ order, ∀ y ∈ order, y ∈ adj x → greedy adj bound order x ≠ greedy adj bound order y := by
  induction order with
  | nil => simp
  | cons z tail ih =>
    let previous := greedy adj bound tail
    let banned := (adj z).image previous
    have limit : banned.card ≤ d := Finset.card_image_le.trans (bound z)
    have fresh (u : Label) (hu : u ∈ adj z) : unused banned limit ≠ previous u := by
      intro eq
      exact unused_notMem banned limit (eq ▸ Finset.mem_image_of_mem previous hu)
    intro x hx y hy edge
    by_cases xz : x = z
    · subst x
      have yz : y ≠ z := fun eq => irreflexive z (eq ▸ edge)
      simpa only [greedy, Function.update_self, Function.update_of_ne yz] using fresh y edge
    · by_cases yz : y = z
      · subst y
        simpa only [greedy, Function.update_self, Function.update_of_ne xz] using
          Ne.symm (fresh x (symmetric x z edge))
      · simpa only [greedy, Function.update_of_ne xz, Function.update_of_ne yz] using
          ih x ((List.mem_cons.mp hx).resolve_left xz) y ((List.mem_cons.mp hy).resolve_left yz) edge

/-- One more track than the maximum conflict degree suffices. Any ordering
containing all labels can be used for the greedy construction. -/
theorem tracks_of_incidence (rows : Finset Row) (labels : Row → Finset Label)
    (width frequency : ℕ) (size : ∀ i ∈ rows, (labels i).card ≤ width)
    (count : ∀ x, (occurrences rows labels x).card ≤ frequency)
    (order : List Label) (all : ∀ x, x ∈ order) :
    ∃ track : Label → Fin (frequency * (width - 1) + 1),
      ∀ i ∈ rows, Set.InjOn track (labels i) := by
  let adj := neighbors rows labels
  let bound := degree_bound rows labels width frequency size count
  refine ⟨greedy adj bound order, ?_⟩
  intro i hi x hx y hy eq
  by_contra ne
  apply greedy_proper adj bound _ _ order x (all x) y (all y)
    (mem_neighbors_iff.mpr ⟨ne,i,hi,hx,hy⟩) eq
  · intro a b edge
    obtain ⟨different, row, hr, ha,hb⟩ := mem_neighbors_iff.mp edge
    exact mem_neighbors_iff.mpr ⟨Ne.symm different,row,hr,hb,ha⟩
  · intro a loop
    exact (mem_neighbors_iff.mp loop).1 rfl

/-- Posting and marking frequencies add. This includes unmarked rows and
permits different rows to mark the same label. -/
theorem tracks_of_postings [DecidableEq Row] (rows : Finset Row)
    (posted marked : Row → Finset Label) (w m h t : ℕ)
    (postWidth : ∀ i ∈ rows, (posted i).card ≤ w)
    (markWidth : ∀ i ∈ rows, (marked i).card ≤ m)
    (postFrequency : ∀ x, (occurrences rows posted x).card ≤ h)
    (markFrequency : ∀ x, (occurrences rows marked x).card ≤ t)
    (order : List Label) (all : ∀ x, x ∈ order) :
    ∃ track : Label → Fin ((h + t) * (w + m - 1) + 1),
      ∀ i ∈ rows, Set.InjOn track ↑(posted i ∪ marked i) := by
  let labels (i : Row) := posted i ∪ marked i
  apply tracks_of_incidence rows labels (w + m) (h + t) _ _ order all
  · intro i hi
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (postWidth i hi) (markWidth i hi))
  · intro x
    have eq : occurrences rows labels x = occurrences rows posted x ∪ occurrences rows marked x := by
      ext i
      simp [occurrences, labels, and_or_left]
    rw [eq]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (postFrequency x) (markFrequency x))

end KFOL.Core.AddressConflictColoring
