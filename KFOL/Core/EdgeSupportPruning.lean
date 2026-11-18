module

public import KFOL.Core.GraphPruning

/-! # When every positive pruning consists of a single graph edge -/

@[expose] public section
namespace KFOL.Core.GraphPruning

open ProfileBudgets
variable {V : Type*} {G : SimpleGraph V}

/-- A complete rectangle with robust shores containing an oriented edge. -/
def InRobustRectangle (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ L R : Set V, Robust G L ∧ Robust G R ∧ u ∈ L ∧ v ∈ R ∧
    ∀ x ∈ L, ∀ y ∈ R, G.Adj x y

private abbrev IsEdge (G : SimpleGraph V) (S : Set V) :=
  ∃ x y, G.Adj x y ∧ S = {x, y}

private theorem support_nonempty (r : Bool) (t : CoreTerm Bool V) {S : Set V}
    (h : S ∈ Supports r t) : S.Nonempty := by
  induction t using induction_choice generalizing S with
  | var x => obtain rfl : S = {x} := h; exact ⟨x,rfl⟩
  | choice q l other il ih =>
    by_cases qr : q = r
    · subst q
      obtain ⟨L, hl, R, _, rfl⟩ := owned.mp h
      exact (il hl).mono Set.subset_union_left
    · exact ((foreign qr).mp h).elim il ih

private theorem subset_pair {S : Set V} {u v : V} (ne : S.Nonempty)
    (sub : S ⊆ {u,v}) : (∃ x, S = {x}) ∨ S = {u,v} := by
  classical
  by_cases hu : u ∈ S
  · by_cases hv : v ∈ S
    · exact .inr (Set.Subset.antisymm sub (fun _ h => h.elim (fun e => e ▸ hu) (fun e => e ▸ hv)))
    · exact .inl ⟨u, Set.Subset.antisymm (fun _ hx => (sub hx).resolve_right
        (fun h => hv (h ▸ hx))) (Set.singleton_subset_iff.mpr hu)⟩
  · have one : S ⊆ {v} := fun _ hx => (sub hx).resolve_left (fun h => hu (h ▸ hx))
    obtain ⟨x,hx⟩ := ne
    exact .inl ⟨v,Set.Subset.antisymm one (Set.singleton_subset_iff.mpr (one hx ▸ hx))⟩

private theorem edge_subset_pair {u v : V} {Q : Set V} (e : IsEdge G Q) (sub : Q ⊆ {u,v}) : Q = {u,v} := by
  rcases subset_pair (by obtain ⟨a,b,_,rfl⟩ := e; exact ⟨a,by simp⟩) sub with ⟨z,hz⟩ | h
  · obtain ⟨a,b,ab,rfl⟩ := e
    have ha : a = z := (Set.ext_iff.mp hz a).mp (by simp)
    have hb : b = z := (Set.ext_iff.mp hz b).mp (by simp)
    exact (ab.ne (ha.trans hb.symm)).elim
  · exact h

private theorem edge_hits_cover {S H : Set V} (edge : IsEdge G S) (cov : G.IsVertexCover H) :
    (S ∩ H).Nonempty := by
  obtain ⟨x,y,h,rfl⟩ := edge
  exact (cov h).elim (fun hx => ⟨x,by simp,hx⟩) (fun hy => ⟨y,by simp,hy⟩)

private theorem negative_inside_cover (t : CoreTerm Bool V) {H : Set V} (cov : G.IsVertexCover H)
    (edges : ∀ S ∈ Supports false t, IsEdge G S) : ∃ B ∈ Supports true t, B ⊆ H :=
  (support_transversal_iff false t H).mp fun S h => edge_hits_cover (edges S h) cov

private def Singletons (t : CoreTerm Bool V) : Set V := {x | {x} ∈ Supports false t}

private theorem singleton_shore {t : CoreTerm Bool V}
    (small : ∀ S ∈ Supports false t, (∃ x, S = {x}) ∨ IsEdge G S)
    (rob : ∀ H ∈ Supports true t, Robust G H) : Robust G (Singletons t) := by
  intro C cov sub x hx
  obtain ⟨H,hH,hC⟩ := (support_transversal_iff false t C).mp (by
    intro S h
    rcases small S h with ⟨z, rfl⟩ | he
    · exact ⟨z, rfl, sub h⟩
    · exact edge_hits_cover he cov)
  have both : ({x} ∩ H).Nonempty :=
    (support_transversal_iff false t H).mpr ⟨H,hH,Set.Subset.rfl⟩ {x} hx
  exact rob H hH cov hC x (by simpa using both)

private theorem rectangle_symm {u v : V} (h : InRobustRectangle G u v) :
    InRobustRectangle G v u := by
  obtain ⟨L,R,l,r,ul,vr,c⟩ := h
  exact ⟨R,L,r,l,vr,ul,fun x hx y hy => (c y hy x hx).symm⟩

private theorem rectangle_of_small_shore [Finite V] {u v : V} (uv : G.Adj u v)
    {S : Set V} (rob : Robust G S) (ne : S.Nonempty) (small : S ⊆ {u,v}) :
    InRobustRectangle G u v := by
  classical
  have star {a b : V} (ab : G.Adj a b) (aS : a ∈ S) (s : S ⊆ {a,b}) :
      InRobustRectangle G a b := by
    refine ⟨{a}, G.neighborSet a, ?_, neighborhood_robust G a, rfl, ab, ?_⟩
    · intro H cov sub x hx
      have hxa : x = a := hx
      subst x
      by_cases hb : b ∈ H
      · exact rob cov (s.trans (fun _ h => h.elim (fun e => e ▸ sub rfl) (fun e => e ▸ hb))) a aS
      · exact minimal_cover_through cov ab (fun _ h => (cov h).resolve_left hb)
    · rintro x rfl y hy
      exact hy
  obtain ⟨x,hx⟩ := ne
  rcases small hx with rfl | (rfl : x = v)
  · exact star uv hx small
  · exact rectangle_symm (star uv.symm hx (fun _ h => (small h).symm))

private theorem rectangle_of_local [Finite V] (t : CoreTerm Bool V) {u v : V} (uv : G.Adj u v)
    (edges : ∀ S ∈ Supports false t, IsEdge G S)
    (rob : ∀ H ∈ Supports true t, Robust G H)
    (hit : ∃ P ∈ Supports false t, P ⊆ {u,v}) : InRobustRectangle G u v := by
  classical
  induction t using induction_choice with
  | var x =>
    obtain ⟨a,b,ab,eq⟩ := edges {x} rfl
    have ha : a = x := (Set.ext_iff.mp eq a).mpr (by simp)
    have hb : b = x := (Set.ext_iff.mp eq b).mpr (by simp)
    exact (ab.ne (ha.trans hb.symm)).elim
  | choice q l r il ir =>
    cases q with
    | true =>
      have el := fun S h => edges S ((foreign (by decide : true ≠ false)).mpr (.inl h))
      have er := fun S h => edges S ((foreign (by decide : true ≠ false)).mpr (.inr h))
      obtain ⟨P,hP,sub⟩ := hit
      rcases (foreign (by decide : true ≠ false)).mp hP with ph | ph
      · apply il el _ ⟨P,ph,sub⟩
        intro H hH C cov inc x hx
        obtain ⟨B,hB,hC⟩ := negative_inside_cover r cov er
        exact rob _ (owned.mpr ⟨H,hH,B,hB,rfl⟩) cov (Set.union_subset inc hC) x (.inl hx)
      · apply ir er _ ⟨P,ph,sub⟩
        intro H hH C cov inc x hx
        obtain ⟨B,hB,hC⟩ := negative_inside_cover l cov el
        exact rob _ (owned.mpr ⟨B,hB,H,hH,rfl⟩) cov (Set.union_subset hC inc) x (.inr hx)
    | false =>
      have rl := fun H h => rob H ((foreign (by decide : false ≠ true)).mpr (.inl h))
      have rr := fun H h => rob H ((foreign (by decide : false ≠ true)).mpr (.inr h))
      obtain ⟨_, hP, inside⟩ := hit
      obtain ⟨A,hA,B,hB,rfl⟩ := owned.mp hP
      have aSub := Set.subset_union_left (s := A) (t := B) |>.trans inside
      have bSub := Set.subset_union_right (s := A) (t := B) |>.trans inside
      have combine {X Y} (x : X ∈ Supports false l) (y : Y ∈ Supports false r) :
          IsEdge G (X ∪ Y) := edges _ (owned.mpr ⟨X,x,Y,y,rfl⟩)
      have shape {s : CoreTerm Bool V} {H U : Set V} (hH : H ∈ Supports false s)
          (sub : H ⊆ U) (hU : IsEdge G U) : (∃ z, H = {z}) ∨ IsEdge G H := by
        obtain ⟨x,y,xy,rfl⟩ := hU
        exact (subset_pair (support_nonempty _ _ hH) sub).imp id (fun eq => ⟨x,y,xy,eq⟩)
      have sl := fun X x => shape (s := l) x (Set.subset_union_left (s := X) (t := B)) (combine x hB)
      have sr := fun Y y => shape (s := r) y (Set.subset_union_right (s := A) (t := Y)) (combine hA y)
      by_cases nl : (Singletons l).Nonempty
      · by_cases nr : (Singletons r).Nonempty
        · have lk := singleton_shore sl rl
          have rk := singleton_shore sr rr
          have cross (x) (hx : x ∈ Singletons l) (y) (hy : y ∈ Singletons r) : G.Adj x y := by
            obtain ⟨a,b,ab,eq⟩ := combine hx hy
            have hx' : x = a ∨ x = b := (Set.ext_iff.mp eq x).mp (.inl rfl)
            have hy' : y = a ∨ y = b := (Set.ext_iff.mp eq y).mp (.inr rfl)
            have ne : x ≠ y := by
              rintro rfl
              have xa := (Set.ext_iff.mp eq a).mpr (by simp)
              have xb := (Set.ext_iff.mp eq b).mpr (by simp)
              simp only [Set.union_self, Set.mem_singleton_iff] at xa xb
              exact ab.ne (xa.trans xb.symm)
            rcases hx' with xa | xb <;> rcases hy' with ya | yb
            · exact (ne (xa.trans ya.symm)).elim
            · exact xa ▸ yb ▸ ab
            · exact xb ▸ ya ▸ ab.symm
            · exact (ne (xb.trans yb.symm)).elim
          rcases sl A hA with ⟨x,rfl⟩ | aEdge
          · rcases sr B hB with ⟨y,rfl⟩ | bEdge
            · have xy := cross x hA y hB
              have xx : x = u ∨ x = v := aSub rfl
              have yy : y = u ∨ y = v := bSub rfl
              rcases xx with xu | xv <;> rcases yy with yu | yv
              · exact (xy.ne (xu.trans yu.symm)).elim
              · exact ⟨_,_,lk,rk,xu ▸ hA,yv ▸ hB,cross⟩
              · exact rectangle_symm ⟨_,_,lk,rk,xv ▸ hA,yu ▸ hB,cross⟩
              · exact (xy.ne (xv.trans yv.symm)).elim
            · obtain rfl := edge_subset_pair bEdge bSub
              apply rectangle_of_small_shore uv lk nl
              intro z hz
              have e := combine hz hB
              obtain ⟨a,b,_,heq⟩ := e
              have incl : ({u,v} : Set V) ⊆ {a,b} := heq ▸ Set.subset_union_right
              have same := edge_subset_pair bEdge incl
              exact same ▸ (heq ▸ (Or.inl (rfl : z ∈ ({z} : Set V))))
          · obtain rfl := edge_subset_pair aEdge aSub
            apply rectangle_of_small_shore uv rk nr
            intro z hz
            obtain ⟨a,b,_,heq⟩ := combine hA hz
            have incl : ({u,v} : Set V) ⊆ {a,b} := heq ▸ Set.subset_union_left
            have same := edge_subset_pair aEdge incl
            exact same ▸ (heq ▸ (Or.inr (rfl : z ∈ ({z} : Set V))))
        · apply ir (fun S hs => (sr S hs).resolve_left (by rintro ⟨z,rfl⟩; exact nr ⟨z,hs⟩)) rr
          exact ⟨B,hB,bSub⟩
      · apply il (fun S hs => (sl S hs).resolve_left (by rintro ⟨z,rfl⟩; exact nl ⟨z,hs⟩)) rl
        exact ⟨A,hA,aSub⟩

/-- A graph has a compatible word whose every positive pruning is an edge
exactly when its edges are covered by complete rectangles with robust shores. -/
theorem exists_edge_supports_iff_robust_rectangles [Finite V] (G : SimpleGraph V)
    (edge : ∃ u v, G.Adj u v) :
    (∃ t : CoreTerm Bool V, Compatible G t ∧
      ∀ H ∈ Supports false t, ∃ x y, G.Adj x y ∧ H = {x,y}) ↔
      ∀ u v, G.Adj u v → InRobustRectangle G u v := by
  classical
  constructor
  · rintro ⟨t,ht,pairs⟩ u v uv
    apply rectangle_of_local t uv pairs
    · intro H hH C _ sub x hx
      obtain ⟨D,hD,m,xd⟩ := (ht.2 H hH).2 x hx
      exact ⟨D,hD.trans sub,m,xd⟩
    · apply (support_transversal_iff true t {u,v}).mp
      intro H hH
      exact ((ht.2 H hH).1 uv).elim (fun hu => ⟨u,hu,by simp⟩) (fun hv => ⟨v,hv,by simp⟩)
  · intro rect
    let E := {e : V × V | G.Adj e.1 e.2}
    choose L R safeL safeR left right cross using fun e : E => rect e.1.1 e.1.2 e.2
    exact exists_compatible_edge_supports_of_rectangles G edge L R
      (fun e => ⟨_,left e⟩) (fun e => ⟨_,right e⟩) cross
      (fun u v uv => ⟨⟨(u,v),uv⟩, .inl ⟨left _,right _⟩⟩) safeL safeR

end KFOL.Core.GraphPruning
