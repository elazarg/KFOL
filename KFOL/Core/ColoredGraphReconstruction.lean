module

public import KFOL.Core.ColoredGraphDecomposition
public import KFOL.Core.ColoredGraphSemantics
public import KFOL.Algebra.Views
public import Mathlib.Data.Set.Card

/-! # Reconstruction from colored graphs

The forbidden induced patterns force a monochromatic cut. Recursing on its
two smaller regions constructs an owned-choice term. The clique laws identify
both its singleton outputs and its possible winners at every valuation.
-/

@[expose] public section

namespace KFOL.Core.ColoredGraph

universe u v w
variable {Role : Type u} {Vertex : Type v} {Var : Type w}

namespace Graph

/-- Every finite nonempty region of a graph with neither forbidden induced
pattern has exactly the clique semantics of one core term. -/
theorem exists_term [Finite Vertex] (G : Graph Role Vertex)
    (hTri : G.NoRainbow) (hPath : G.NoAlternatingPath) (label : Vertex → Var)
    {A : Set Vertex} (hA : A.Nonempty) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ v k,
      (t.eval v = WinnerSet.singleton k ↔ G.Blocks A label v k) ∧
      (k ∈ (t.eval v).val ↔ G.Wins A label v k) := by
  classical
  have build (n : ℕ) : ∀ A : Set Vertex, A.ncard = n → A.Nonempty →
      ∃ t : Term Role Var, t.IsCore ∧ ∀ v k,
        (t.eval v = WinnerSet.singleton k ↔ G.Blocks A label v k) ∧
        (k ∈ (t.eval v).val ↔ G.Wins A label v k) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hn hA
      by_cases hsingle : A.Subsingleton
      · obtain ⟨x, rfl⟩ := Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr
          ⟨hA, hsingle⟩
        refine ⟨.var (label x), trivial, ?_⟩
        intro v k
        exact ⟨(blocks_singleton x label v).symm, (wins_singleton x label v k).symm⟩
      · obtain ⟨r, L, R, hc⟩ := G.exists_cut hTri hPath hA hsingle
        have hLA : L ⊆ A := by
          rw [← hc.2.2.2.1]
          exact Set.subset_union_left
        have hRA : R ⊆ A := by
          rw [← hc.2.2.2.1]
          exact Set.subset_union_right
        have hLlt : L.ncard < n := by
          rw [← hn]
          apply Set.ncard_lt_ncard (ht := Set.toFinite A)
          refine ⟨hLA, ?_⟩
          intro hAL
          obtain ⟨x, hx⟩ := hc.2.1
          exact Set.disjoint_left.mp hc.2.2.1 (hAL (hRA hx)) hx
        have hRlt : R.ncard < n := by
          rw [← hn]
          apply Set.ncard_lt_ncard (ht := Set.toFinite A)
          refine ⟨hRA, ?_⟩
          intro hAR
          obtain ⟨x, hx⟩ := hc.1
          exact Set.disjoint_left.mp hc.2.2.1 hx (hAR (hLA hx))
        obtain ⟨s, hs, hS⟩ := ih L.ncard hLlt L rfl hc.1
        obtain ⟨t, ht, hT⟩ := ih R.ncard hRlt R rfl hc.2.1
        refine ⟨.choice r s t, ⟨hs, ht⟩, ?_⟩
        intro v k
        constructor
        · exact (blocks_cut_choice hc label v (s.eval v) (t.eval v)
            (fun q => (hS v q).1.symm) (fun q => (hT v q).1.symm) k).symm
        · exact (wins_cut_choice hc label v (s.eval v) (t.eval v)
            (fun q => (hS v q).2.symm) (fun q => (hT v q).2.symm)
            (hS v r).1.symm (hT v r).1.symm k).symm
  exact build A.ncard A rfl hA

end Graph

end KFOL.Core.ColoredGraph
