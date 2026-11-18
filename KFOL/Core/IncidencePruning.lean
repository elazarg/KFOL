module

public import KFOL.Core.BipartitePruning
public import KFOL.Core.NeighborhoodLattice
public import Mathlib.Data.Fintype.Sum

/-! # Compatibility on an incidence matrix

The vertices on each side of a binary relation are distinct input names of
the core word. The neighborhood rows belong to the right-hand vertex set. -/

@[expose] public section
namespace KFOL.Core.GraphPruning

open ProfileBudgets
variable {X Y : Type*}

/-- The simple bipartite graph of a binary incidence relation. -/
def incidenceGraph (E : X → Y → Prop) : SimpleGraph (X ⊕ Y) where
  Adj
    | .inl x, .inr y | .inr y, .inl x => E x y
    | _, _ => False
  symm := ⟨by rintro (a | a) (b | b) h <;> exact h⟩
  loopless := ⟨by rintro (a | a) <;> exact id⟩

theorem incidenceGraph_isBipartite (E : X → Y → Prop) : (incidenceGraph E).IsBipartite := by
  refine ⟨Sum.elim (fun _ => (0 : Fin 2)) (fun _ => 1), ?_⟩
  rintro (a | a) (b | b) h
  · exact h.elim
  · exact (by decide : (0 : Fin 2) ≠ 1)
  · exact (by decide : (1 : Fin 2) ≠ 0)
  · exact h.elim

private theorem incidence_rectangle (E : X → Y → Prop) (u : X) (v : Y) :
    Bisimplicial (incidenceGraph E) (.inl u) (.inr v) ↔
    ∀ a b, E a v → E u b → E a b := by
  constructor
  · intro h a b hav hub
    exact h (.inl a) hav (.inr b) hub
  · intro h
    rintro (a | a) ha (b | b) hb
    · contradiction
    · exact h a b ha hb
    · contradiction
    · contradiction

private theorem bisimplicial_swap {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : Bisimplicial G u v) : Bisimplicial G v u :=
  fun x hx y hy => (h y hy x hx).symm

private theorem incidence_cover (E : X → Y → Prop) :
    BisimplicialCover (incidenceGraph E) ↔
    ∀ a b, E a b → ∃ u v, E u v ∧ E a v ∧ E u b ∧
      ∀ i j, E i v → E u j → E i j := by
  constructor
  · intro cover a b ab
    obtain ⟨u,v,uv,av,ub,rect⟩ := cover (.inl a) (.inr b) ab
    cases u with
    | inr u => contradiction
    | inl u =>
      cases v with
      | inl v => contradiction
      | inr v => exact ⟨u,v,uv,av,ub,(incidence_rectangle E u v).mp rect⟩
  · intro h
    rintro (a | a) (b | b) ab
    · contradiction
    · obtain ⟨u,v,uv,av,ub,rect⟩ := h a b ab
      exact ⟨.inl u,.inr v,uv,av,ub,(incidence_rectangle E u v).mpr rect⟩
    · obtain ⟨u,v,uv,bv,ua,rect⟩ := h b a ab
      exact ⟨.inr v,.inl u,uv,ua,bv,bisimplicial_swap ((incidence_rectangle E u v).mpr rect)⟩
    · contradiction

/-- Orienting the graph cover from rows to columns recovers the matrix cover. -/
theorem bisimplicialCover_incidenceGraph_iff (E : X → Y → Prop) :
    BisimplicialCover (incidenceGraph E) ↔ NeighborhoodLattice.EdgeCover E := by
  rw [incidence_cover]
  constructor
  · intro h a b ab
    obtain ⟨u,v,uv,av,ub,rect⟩ := h a b ab
    exact ⟨u,v,⟨uv,fun i iv j uj => rect i j iv uj⟩,av,ub⟩
  · intro h a b ab
    obtain ⟨u,v,⟨uv,rect⟩,av,ub⟩ := h a b ab
    exact ⟨u,v,uv,av,ub,fun i j iv uj => rect i iv j uj⟩

/-- A finite nonempty incidence relation admits the required core word exactly
when the lattice of unions of its rows is distributive. -/
theorem exists_compatible_incidenceGraph_iff_distributive [Finite X] [Finite Y]
    (E : X → Y → Prop) (nonempty : ∃ x y, E x y) :
    (∃ t : CoreTerm Bool (X ⊕ Y), Compatible (incidenceGraph E) t) ↔
    ∀ U V W : NeighborhoodLattice.RowUnion E, U ⊓ (V ⊔ W) = (U ⊓ V) ⊔ (U ⊓ W) := by
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite Y
  obtain ⟨x,y,xy⟩ := nonempty
  rw [exists_compatible_iff_bisimplicialCover_of_bipartite (incidenceGraph E)
    (incidenceGraph_isBipartite E) ⟨.inl x,.inr y,xy⟩, bisimplicialCover_incidenceGraph_iff]
  exact (NeighborhoodLattice.distributive_iff_edgeCover E).symm

end KFOL.Core.GraphPruning
