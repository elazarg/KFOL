module

public import KFOL.Core.GraphPruning
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! # Bisimplicial rectangles and graph pruning

A closed walk of length five is the only local odd-walk obstruction needed for
the necessity of a bisimplicial rectangle cover. In particular the criterion
applies to every finite bipartite graph.
-/

@[expose] public section
namespace KFOL.Core.GraphPruning

open ProfileBudgets
variable {V : Type*}

/-- No closed walk of length five. A triangle also gives such a walk by backtracking. -/
def NoClosedFiveWalk (G : SimpleGraph V) : Prop :=
  ∀ a b c d e, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → ¬ G.Adj e a

theorem noClosedFiveWalk_of_bipartite {G : SimpleGraph V} (h : G.IsBipartite) :
    NoClosedFiveWalk G := by
  obtain ⟨c, hc⟩ := h
  intro a b d e f ab bd de ef fa
  have h₁ := hc ab
  have h₂ := hc bd
  have h₃ := hc de
  have h₄ := hc ef
  have h₅ := hc fa
  simp only [SimpleGraph.top_adj] at h₁ h₂ h₃ h₄ h₅
  lia

/-- Both full neighborhoods form the shores of a complete bipartite subgraph. -/
def Bisimplicial (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ x ∈ G.neighborSet v, ∀ y ∈ G.neighborSet u, G.Adj x y

/-- Each oriented edge lies in the rectangle of some bisimplicial edge. -/
def BisimplicialCover (G : SimpleGraph V) : Prop :=
  ∀ a b, G.Adj a b → ∃ u v, G.Adj u v ∧ G.Adj a v ∧ G.Adj u b ∧ Bisimplicial G u v

private def SideTail (G : SimpleGraph V) (u v x : V) : Set V :=
  {z | z ≠ u ∧ (∃ w, G.Adj u w ∧ G.Adj w z) ∧ (z = x ∨ ¬G.Adj v z)}

private theorem sideTail_spec {G : SimpleGraph V} (odd : NoClosedFiveWalk G)
    {u v x : V} (uv : G.Adj u v) (vx : G.Adj v x) (xu : x ≠ u)
    (minimal : ∀ w, G.Adj u w → G.neighborSet w ⊆ G.neighborSet v →
      G.neighborSet v ⊆ G.neighborSet w) :
    (∀ w, G.Adj u w → ∃ z ∈ SideTail G u v x, G.Adj w z) ∧
    G.IsIndepSet (SideTail G u v x) ∧
    (∀ z ∈ SideTail G u v x, ¬G.Adj z u ∧ (z = x ∨ ¬G.Adj z v)) ∧
    u ∉ SideTail G u v x := by
  classical
  refine ⟨?_, ?_, ?_, fun h => h.1 rfl⟩
  · intro w uw
    by_cases wx : G.Adj w x
    · exact ⟨x, ⟨xu, ⟨v, uv, vx⟩, Or.inl rfl⟩, wx⟩
    · have h : ¬ G.neighborSet w ⊆ G.neighborSet v :=
        fun sub => wx (minimal w uw sub vx)
      obtain ⟨z, wz, vz⟩ := Set.not_subset.mp h
      refine ⟨z, ⟨?_, ⟨w, uw, wz⟩, Or.inr vz⟩, wz⟩
      exact fun e => vz (e ▸ uv.symm)
  · rintro p ⟨_,⟨w,uw,wp⟩,_⟩ q ⟨_,⟨s,us,sq⟩,_⟩ _ pq
    exact odd u w p q s uw wp pq sq.symm us.symm
  · rintro z ⟨_,⟨w,uw,wz⟩,zz⟩
    exact ⟨odd u w u w z uw uw.symm uw wz, zz.imp_right (fun h zv => h zv.symm)⟩

private theorem bisimplicial_of_minimal {G : SimpleGraph V} (odd : NoClosedFiveWalk G)
    {u v : V} (uv : G.Adj u v) {t : CoreTerm Bool V} (ok : Compatible G t)
    (minv : ∀ w, G.Adj u w → G.neighborSet w ⊆ G.neighborSet v →
      G.neighborSet v ⊆ G.neighborSet w)
    (minu : ∀ w, G.Adj v w → G.neighborSet w ⊆ G.neighborSet u →
      G.neighborSet u ⊆ G.neighborSet w) : Bisimplicial G u v := by
  classical
  intro x vx y uy
  by_contra xy
  have xu : x ≠ u := fun e => xy (e ▸ uy)
  have yv : y ≠ v := fun e => xy (e ▸ (show G.Adj v x from vx).symm)
  obtain ⟨du,iu,fu,nu⟩ := sideTail_spec odd uv vx xu minv
  obtain ⟨dv,iv,fv,nv⟩ := sideTail_spec odd uv.symm uy yv minu
  let P := ({x,y} : Set V)ᶜ
  have cover : G.IsVertexCover P := by
    apply G.isVertexCover_compl.mpr
    intro a ha b hb _ ab
    rcases (show a = x ∨ a = y from ha) with rfl | rfl <;>
      rcases (show b = _ ∨ b = _ from hb) with rfl | rfl
    · exact G.loopless.irrefl _ ab
    · exact xy ab
    · exact xy ab.symm
    · exact G.loopless.irrefl _ ab
  refine incompatible_of_edge_cut G uv P _ _ cover du dv iu iv ?_ nu nv t ok
  intro z hz hp
  have nzx : z ≠ x := fun e => hp (Or.inl e)
  have nzy : z ≠ y := fun e => hp (Or.inr e)
  rcases hz with h | h
  · exact ⟨(fu z h).1, (fu z h).2.resolve_left nzx⟩
  · exact ⟨(fv z h).2.resolve_left nzy, (fv z h).1⟩

/-- Below each edge in the order of neighborhood inclusion there is a
bisimplicial edge, provided a compatible word exists. -/
theorem bisimplicialCover_of_compatible [Finite V] {G : SimpleGraph V}
    (odd : NoClosedFiveWalk G) {t : CoreTerm Bool V} (ok : Compatible G t) :
    BisimplicialCover G := by
  classical
  intro a b ab
  let weight (u v : V) := (G.neighborSet u).ncard + (G.neighborSet v).ncard
  let P (n : Nat) := ∃ u v, G.Adj u v ∧ G.neighborSet u ⊆ G.neighborSet a ∧
    G.neighborSet v ⊆ G.neighborSet b ∧ weight u v = n
  have ex : ∃ n, P n := ⟨_,a,b,ab,Set.Subset.rfl,Set.Subset.rfl,rfl⟩
  obtain ⟨u,v,uv,ua,vb,eq⟩ := Nat.find_spec ex
  have least {u' v' : V} (h : G.Adj u' v') (hu : G.neighborSet u' ⊆ G.neighborSet a)
      (hv : G.neighborSet v' ⊆ G.neighborSet b) : weight u v ≤ weight u' v' := by
    rw [eq]
    exact Nat.find_min' ex ⟨u',v',h,hu,hv,rfl⟩
  refine ⟨u,v,uv,ua uv,(vb uv.symm).symm,bisimplicial_of_minimal odd uv ok ?_ ?_⟩
  · intro w uw sub
    by_contra ns
    have lt := Set.ncard_lt_ncard (show G.neighborSet w ⊂ G.neighborSet v from ⟨sub, ns⟩)
    have le := least uw ua (sub.trans vb)
    simp only [weight] at le
    omega
  · intro w vw sub
    by_contra ns
    have lt := Set.ncard_lt_ncard (show G.neighborSet w ⊂ G.neighborSet u from ⟨sub, ns⟩)
    have le := least vw.symm (sub.trans ua) vb
    simp only [weight] at le
    omega

/-- The rectangles of the covering bisimplicial edges give a compatible word. -/
theorem exists_compatible_of_bisimplicialCover [Finite V] (G : SimpleGraph V)
    (edge : ∃ u v, G.Adj u v) (cover : BisimplicialCover G) :
    ∃ t : CoreTerm Bool V, Compatible G t := by
  let E := {p : V × V // G.Adj p.1 p.2 ∧ Bisimplicial G p.1 p.2}
  apply exists_compatible_of_rectangles G edge
    (fun p : E => G.neighborSet p.val.2) (fun p : E => G.neighborSet p.val.1)
  · exact fun p => ⟨_, p.property.1.symm⟩
  · exact fun p => ⟨_, p.property.1⟩
  · exact fun p => p.property.2
  · intro a b ab
    obtain ⟨u,v,uv,av,ub,rect⟩ := cover a b ab
    exact ⟨⟨(u,v),uv,rect⟩, Or.inl ⟨av.symm,ub⟩⟩
  · exact fun p => neighborhood_robust G p.val.2
  · exact fun p => neighborhood_robust G p.val.1

/-- For graphs having no closed walk of length five, the full edge and
minimal-cover pruning problem is equivalent to a bisimplicial rectangle cover. -/
theorem exists_compatible_iff_bisimplicialCover [Finite V] (G : SimpleGraph V)
    (odd : NoClosedFiveWalk G) (edge : ∃ u v, G.Adj u v) :
    (∃ t : CoreTerm Bool V, Compatible G t) ↔ BisimplicialCover G :=
  ⟨fun ⟨_, ht⟩ => bisimplicialCover_of_compatible odd ht,
   exists_compatible_of_bisimplicialCover G edge⟩

/-- The characterization on arbitrary finite bipartite graphs. -/
theorem exists_compatible_iff_bisimplicialCover_of_bipartite [Finite V] (G : SimpleGraph V)
    (bip : G.IsBipartite) (edge : ∃ u v, G.Adj u v) :
    (∃ t : CoreTerm Bool V, Compatible G t) ↔ BisimplicialCover G :=
  exists_compatible_iff_bisimplicialCover G (noClosedFiveWalk_of_bipartite bip) edge

end KFOL.Core.GraphPruning
