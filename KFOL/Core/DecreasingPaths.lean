module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.List.Induction

/-! # The size of a tree with all smaller children

A path is recorded in root-to-vertex order. If all labels are available at
the root and every smaller label is available after the last one, every
strictly decreasing list occurs. Its set of labels recovers the path.
-/

@[expose] public section

namespace KFOL.Core.DecreasingPaths

variable {α : Type*} [LinearOrder α] {paths : Set (List α)}

/-- Local branching hypotheses on the set of label sequences that occur. -/
structure HasSmallerChildren (paths : Set (List α)) : Prop where
  root : [] ∈ paths
  first : ∀ i : α, [i] ∈ paths
  child : ∀ (stem : List α) (i j : α), stem ++ [i] ∈ paths → j < i → (stem ++ [i]) ++ [j] ∈ paths

/-- Every strictly decreasing root-to-vertex history occurs, including the empty one. -/
theorem mem_of_pairwise_gt (h : HasSmallerChildren paths) (p : List α) (hp : p.Pairwise (· > ·)) :
    p ∈ paths := by
  induction p using List.reverseRecOn with
  | nil => exact h.root
  | append_singleton initial j ih =>
    obtain ⟨hprefix, _, hlast⟩ := List.pairwise_append.mp hp
    specialize ih hprefix
    cases initial using List.reverseRecOn with
    | nil => exact h.first j
    | append_singleton stem i _ =>
      exact h.child stem i j ih (hlast i (by simp) j (by simp))

/-- Each finite subset labels an actual path, and its descending history determines the subset. -/
def subsetPathEmbedding (h : HasSmallerChildren paths) : Finset α ↪ paths where
  toFun s := ⟨s.sort (· ≥ ·), mem_of_pairwise_gt h _ s.sortedGT_sort.pairwise⟩
  inj' := by
    intro s t he
    simpa using congrArg (fun p : paths => p.val.toFinset) he

/-- If each vertex has a root-to-vertex history, the branching rules force at
least one distinct vertex per subset of the finite label set. -/
theorem two_pow_le_card_vertices [Fintype α] {Vertex : Type*} [Fintype Vertex]
    (history : Vertex → List α) (h : HasSmallerChildren paths) (realized : paths ⊆ Set.range history) :
    2 ^ Fintype.card α ≤ Fintype.card Vertex := by
  classical
  let embed := subsetPathEmbedding h
  choose vertex hvertex using fun s : Finset α => realized (embed s).property
  have inj : Function.Injective vertex := by
    intro s t he
    apply embed.injective
    exact Subtype.ext ((hvertex s).symm.trans ((congrArg history he).trans (hvertex t)))
  simpa only [Fintype.card_finset] using Fintype.card_le_of_injective vertex inj

end KFOL.Core.DecreasingPaths
