module

public import KFOL.Core.ProfileBudgets.Pruning
public import Mathlib.Combinatorics.SimpleGraph.VertexCover

/-! # Graph edges and minimal vertex covers as pruning supports

The two gates have distinct owners. A pruning keeps both children at its
own gate and one child at the other gate. -/

@[expose] public section
namespace KFOL.Core.GraphPruning

open ProfileBudgets
variable {V : Type*}

/-- The sets of input names reached by the different prunings at one owner. -/
def Supports (r : Bool) : CoreTerm Bool V → Set (Set V)
  | .var x => {{x}}
  | .func (.choice q) a =>
    if q = r then {H | ∃ S ∈ Supports r (a 0), ∃ T ∈ Supports r (a 1), S ∪ T = H}
    else Supports r (a 0) ∪ Supports r (a 1)

@[simp] private theorem supports_var (r : Bool) (x : V) (H : Set V) :
    H ∈ Supports r (.var x) ↔ H = {x} := Iff.rfl

theorem owned {r : Bool} {s t : CoreTerm Bool V} {H : Set V} :
    H ∈ Supports r (choiceTerm r s t) ↔
      ∃ S ∈ Supports r s, ∃ T ∈ Supports r t, S ∪ T = H := by simp [Supports, choiceTerm]

theorem foreign {r q : Bool} (h : q ≠ r) {s t : CoreTerm Bool V} {H : Set V} :
    H ∈ Supports r (choiceTerm q s t) ↔ H ∈ Supports r s ∨ H ∈ Supports r t := by
  simp [Supports, choiceTerm, h]

private theorem varSet_choice [DecidableEq V] (r : Bool) (s t : CoreTerm Bool V) :
    ((choiceTerm r s t).varFinset : Set V) = (s.varFinset : Set V) ∪ t.varFinset := by
  simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2]

/-- This support semantics is exactly the support of one of the library prunings. -/
theorem supports_iff_prunes [DecidableEq V] (r : Bool) (t : CoreTerm Bool V) (H : Set V) :
    H ∈ Supports r t ↔ ∃ u, Prunes r t u ∧ (u.varFinset : Set V) = H := by
  constructor
  · induction t using induction_choice generalizing H with
    | var j =>
      rintro (rfl : H = {j})
      exact ⟨_, .var j, by simp [FirstOrder.Language.Term.varFinset]⟩
    | choice q s t hs ht =>
      by_cases e : q = r
      · subst q
        rintro h
        obtain ⟨S, hS, T, hT, rfl⟩ := owned.mp h
        obtain ⟨u, hu, rfl⟩ := hs _ hS
        obtain ⟨v, hv, rfl⟩ := ht _ hT
        exact ⟨_, .owned hu hv, varSet_choice _ _ _⟩
      · intro h
        rcases (foreign e).mp h with h | h
        · obtain ⟨u, hu, hh⟩ := hs _ h
          exact ⟨_, .left e hu, hh⟩
        · obtain ⟨u, hu, hh⟩ := ht _ h
          exact ⟨_, .right e hu, hh⟩
  · rintro ⟨u, hu, rfl⟩
    induction hu with
    | var j => simp [FirstOrder.Language.Term.varFinset]
    | owned hx hy hs ht => exact owned.mpr ⟨_, hs, _, ht, (varSet_choice _ _ _).symm⟩
    | left e _ ih => exact (foreign e).mpr (.inl ih)
    | right e _ ih => exact (foreign e).mpr (.inr ih)

private def Wins (r : Bool) (t : CoreTerm Bool V) (P : Set V) :=
  ∀ H ∈ Supports r t, (H ∩ P).Nonempty

private theorem wins_owned {r : Bool} {s t : CoreTerm Bool V} {P : Set V} :
    Wins r (choiceTerm r s t) P ↔ Wins r s P ∨ Wins r t P := by
  classical
  constructor
  · contrapose!
    rintro ⟨hs, ht⟩
    simp only [Wins, not_forall] at hs ht ⊢
    obtain ⟨S,hS,hSP⟩ := hs
    obtain ⟨T,hT,hTP⟩ := ht
    exact ⟨_, owned.mpr ⟨_, hS, _, hT, rfl⟩, fun ⟨x,hx,hp⟩ =>
      hx.elim (fun h => hSP ⟨x,h,hp⟩) (fun h => hTP ⟨x,h,hp⟩)⟩
  · intro h H hH
    obtain ⟨S,hS,T,hT,rfl⟩ := owned.mp hH
    rcases h with h | h
    · obtain ⟨x,hx,hp⟩ := h S hS
      exact ⟨x, Or.inl hx, hp⟩
    · obtain ⟨x,hx,hp⟩ := h T hT
      exact ⟨x, Or.inr hx, hp⟩

private theorem wins_foreign {r q : Bool} (e : q ≠ r) {s t : CoreTerm Bool V} {P : Set V} :
    Wins r (choiceTerm q s t) P ↔ Wins r s P ∧ Wins r t P := by
  simp only [Wins, foreign e, or_imp, forall_and]

private theorem wins_iff (r : Bool) (t : CoreTerm Bool V) (P : Set V) :
    Wins r t P ↔ ∃ H ∈ Supports (!r) t, H ⊆ P := by
  induction t using induction_choice with
  | var j => simp [Wins]
  | choice q s t hs ht =>
    by_cases eq : q = r
    · subst q
      rw [wins_owned, hs, ht]
      simp only [foreign (show r ≠ !r by cases r <;> decide), exists_or, or_and_right]
    · have e : q = !r := by cases q <;> cases r <;> simp_all
      subst q
      rw [wins_foreign eq, hs, ht]
      constructor
      · rintro ⟨⟨S,hS,hs⟩,T,hT,ht⟩
        exact ⟨_, owned.mpr ⟨_, hS, _, hT, rfl⟩, Set.union_subset hs ht⟩
      · rintro ⟨_,h,u⟩
        obtain ⟨S,hS,T,hT,rfl⟩ := owned.mp h
        exact ⟨⟨S,hS,Set.subset_union_left.trans u⟩,⟨T,hT,Set.subset_union_right.trans u⟩⟩

/-- The transversals of the prunings at one owner are the supersets of the
opposite owner's pruning supports. -/
theorem support_transversal_iff (r : Bool) (t : CoreTerm Bool V) (P : Set V) :
    (∀ H ∈ Supports r t, (H ∩ P).Nonempty) ↔ ∃ H ∈ Supports (!r) t, H ⊆ P :=
  wins_iff r t P

/-- A row forbids a pruning that reaches its head and misses its whole tail. -/
def Respects (rows : Set (V × Set V)) (H : Set V) :=
  ∀ ⦃j T⦄, (j,T) ∈ rows → j ∈ H → (H ∩ T).Nonempty

/-- An alternating obstruction. Each selected tail rules out an opposite-owner
pruning contained in that tail which also meets the opposite profile request. -/
theorem alternating_cut (rows : Bool → Set (V × Set V)) (P : Bool → Set V)
    (blocked : ∀ r j T, (j,T) ∈ rows r → ∀ H ⊆ T, Respects (rows (!r)) H →
      ¬ (H ∩ P (!r)).Nonempty)
    (covered : ∀ j ∈ P false ∩ P true, ∃ r T, (j,T) ∈ rows r ∧ j ∉ T)
    (t : CoreTerm Bool V)
    (safe : ∀ r H, H ∈ Supports r t → Respects (rows r) H)
    (wins : ∀ r H, H ∈ Supports r t → (H ∩ P r).Nonempty) : False := by
  classical
  induction t using induction_choice with
  | var j =>
    have h (r) : j ∈ P r := by simpa using wins r {j} rfl
    obtain ⟨r,T,hr,hn⟩ := covered j ⟨h false,h true⟩
    have hp := safe r {j} rfl hr (Set.mem_singleton j)
    simp [hn] at hp
  | choice q s t hs ht =>
    have e : q ≠ !q := by cases q <;> decide
    have pass {z : CoreTerm Bool V} (child : ∀ H ∈ Supports (!q) z,
        H ∈ Supports (!q) (choiceTerm q s t)) j T (row : (j,T) ∈ rows q) :
        ¬ Wins q z T := by
      intro h
      obtain ⟨H,hH,sub⟩ := (wins_iff q z T).mp h
      exact blocked q j T row H sub (safe _ _ (child H hH)) (wins _ _ (child H hH))
    have both (r H) :
        (H ∈ Supports r s → Respects (rows r) H) ∧
        (H ∈ Supports r t → Respects (rows r) H) := by
      by_cases eq : q = r
      · subst r
        constructor
        · intro h j T row hj
          obtain ⟨W,hW,miss⟩ : ∃ W ∈ Supports q t, ¬(W ∩ T).Nonempty := by
            simpa only [Wins, not_forall, exists_prop] using pass (fun _ hw => (foreign e).mpr (.inr hw)) _ _ row
          obtain ⟨x,hx,hT⟩ := safe q _ (owned.mpr ⟨H,h,W,hW,rfl⟩) row (.inl hj)
          exact ⟨x,hx.resolve_right (fun h => miss ⟨x,h,hT⟩),hT⟩
        · intro h j T row hj
          obtain ⟨W,hW,miss⟩ : ∃ W ∈ Supports q s, ¬(W ∩ T).Nonempty := by
            simpa only [Wins, not_forall, exists_prop] using pass (fun _ hw => (foreign e).mpr (.inl hw)) _ _ row
          obtain ⟨x,hx,hT⟩ := safe q _ (owned.mpr ⟨W,hW,H,h,rfl⟩) row (.inr hj)
          exact ⟨x,hx.resolve_left (fun h => miss ⟨x,h,hT⟩),hT⟩
      · exact ⟨fun h => safe _ _ ((foreign eq).mpr (.inl h)),
          fun h => safe _ _ ((foreign eq).mpr (.inr h))⟩
    rcases wins_owned.mp (wins q) with w | w
    · apply hs (fun r H => (both r H).1)
      intro r
      by_cases eq : q = r
      · exact eq ▸ w
      · exact (wins_foreign eq |>.mp (wins r)).1
    · apply ht (fun r H => (both r H).2)
      intro r
      by_cases eq : q = r
      · exact eq ▸ w
      · exact (wins_foreign eq |>.mp (wins r)).2


/-- Positive prunings are unions of edges. Negative prunings are unions of
inclusion-minimal vertex covers, with at least one such cover in each support. -/
def Compatible (G : SimpleGraph V) (t : CoreTerm Bool V) : Prop :=
  (∀ H ∈ Supports false t, H.Nonempty ∧ ∀ x ∈ H, ∃ y ∈ H, G.Adj x y) ∧
  (∀ H ∈ Supports true t, G.IsVertexCover H ∧
    ∀ x ∈ H, ∃ C ⊆ H, Minimal G.IsVertexCover C ∧ x ∈ C)

private theorem neighbor_outside {G : SimpleGraph V} {C : Set V} {x : V}
    (h : Minimal G.IsVertexCover C) (hx : x ∈ C) : ∃ y ∉ C, G.Adj x y := by
  classical
  by_contra! hn
  have cov : G.IsVertexCover (C \ {x}) := by
    intro u v uv
    rcases h.1 uv with hu | hv
    · by_cases eq : u = x
      · subst u
        exact .inr ⟨by_contra fun nv => hn v nv uv, uv.ne'⟩
      · exact .inl ⟨hu,eq⟩
    · by_cases eq : v = x
      · subst v
        exact .inl ⟨by_contra fun nu => hn u nu uv.symm, uv.ne⟩
      · exact .inr ⟨hv,eq⟩
  exact (h.2 cov Set.sdiff_subset hx).2 rfl

theorem minimal_cover_through [Finite V] {G : SimpleGraph V} {H : Set V}
    (cov : G.IsVertexCover H) {x u : V} (xu : G.Adj x u) (neigh : G.neighborSet u ⊆ H) :
    ∃ C ⊆ H, Minimal G.IsVertexCover C ∧ x ∈ C := by
  classical
  have rem : G.IsVertexCover (H \ {u}) := by
    intro a b ab
    by_cases ea : a = u
    · subst a
      exact .inr ⟨neigh ab, ab.ne'⟩
    by_cases eb : b = u
    · subst b
      exact .inl ⟨neigh ab.symm, ab.ne⟩
    exact (cov ab).imp (fun h => ⟨h,ea⟩) (fun h => ⟨h,eb⟩)
  obtain ⟨C,sub,minimal⟩ := exists_minimal_le_of_wellFoundedLT G.IsVertexCover _ rem
  exact ⟨C, sub.trans Set.sdiff_subset, minimal,
    (minimal.1 xu).resolve_right (fun hu => (sub hu).2 rfl)⟩

/-- An edge with independent second-neighbor sets at its endpoints obstructs
compatibility whenever the selected cover separates all their incident postings. -/
theorem incompatible_of_edge_cut (G : SimpleGraph V) {u v : V} (uv : G.Adj u v)
    (P U W : Set V) (cover : G.IsVertexCover P)
    (hu : ∀ y, G.Adj u y → ∃ x ∈ U, G.Adj y x)
    (hv : ∀ y, G.Adj v y → ∃ x ∈ W, G.Adj y x)
    (indU : G.IsIndepSet U) (indW : G.IsIndepSet W)
    (sep : ∀ x ∈ U ∪ W, x ∈ P → ¬ G.Adj x u ∧ ¬ G.Adj x v)
    (noU : u ∉ U) (noV : v ∉ W) (t : CoreTerm Bool V) : ¬ Compatible G t := by
  classical
  rintro ⟨edges,covers⟩
  let Q : Bool → Set V := fun r => if r then {u,v} else P
  let L : Bool → Set (V × Set V) := fun r => if r then {(u,U),(v,W)}
    else {p | p.1 ∈ (U ∪ W) ∩ P ∧ p.2 = G.neighborSet p.1}
  have atNeg {x : V} {T H : Set V}
      (dom : ∀ y, G.Adj x y → ∃ z ∈ T, G.Adj y z)
      (hc : ∀ y ∈ H, ∃ C ⊆ H, Minimal G.IsVertexCover C ∧ y ∈ C)
      (hx : x ∈ H) : (H ∩ T).Nonempty := by
    obtain ⟨C,sub,mc,hx⟩ := hc _ hx
    obtain ⟨y,hy,xy⟩ := neighbor_outside mc hx
    obtain ⟨z,hz,yz⟩ := dom _ xy
    exact ⟨z,sub ((mc.1 yz).resolve_left hy),hz⟩
  apply alternating_cut L Q _ _ t
  · intro r H hH j T row hj
    cases r with
    | false =>
      change j ∈ (U ∪ W) ∩ P ∧ T = G.neighborSet j at row
      obtain ⟨_,rfl⟩ := row
      obtain ⟨y,hy,jy⟩ := (edges H hH).2 j hj
      exact ⟨y,hy,jy⟩
    | true =>
      rcases (show (j,T) = (u,U) ∨ (j,T) = (v,W) from row) with h | h
      · cases h
        exact atNeg hu (covers H hH).2 hj
      · cases h
        exact atNeg hv (covers H hH).2 hj
  · intro r H hH
    cases r with
    | false =>
      obtain ⟨x,hx⟩ := (edges H hH).1
      obtain ⟨y,hy,xy⟩ := (edges H hH).2 x hx
      exact (cover xy).elim (fun hp => ⟨x,hx,hp⟩) (fun hp => ⟨y,hy,hp⟩)
    | true =>
      exact ((covers H hH).1 uv).elim (fun h => ⟨u,h,by simp [Q]⟩)
        (fun h => ⟨v,h,by simp [Q]⟩)
  · intro r j T row H sub ok hit
    cases r with
    | false =>
      change j ∈ (U ∪ W) ∩ P ∧ T = G.neighborSet j at row
      obtain ⟨⟨jUW,jP⟩,rfl⟩ := row
      obtain ⟨x,hx,hq⟩ := hit
      rcases (show x = u ∨ x = v from hq) with rfl | rfl
      · exact (sep _ jUW jP).1 (sub hx)
      · exact (sep _ jUW jP).2 (sub hx)
    | true =>
      have impossible (T : Set V) (hT : T ⊆ U ∪ W) (ind : G.IsIndepSet T) (sub : H ⊆ T) :
          False := by
        obtain ⟨x,hx,hP⟩ := hit
        have rowx : (x,G.neighborSet x) ∈ L false := ⟨⟨hT (sub hx),hP⟩,rfl⟩
        obtain ⟨y,hy,xy⟩ := ok rowx hx
        exact ind (sub hx) (sub hy) (G.ne_of_adj xy) xy
      rcases (show (j,T) = (u,U) ∨ (j,T) = (v,W) from row) with h | h
      · cases h
        exact impossible _ Set.subset_union_left indU sub
      · cases h
        exact impossible _ Set.subset_union_right indW sub
  · intro z hz
    rcases (show z = u ∨ z = v from hz.2) with rfl | rfl
    · exact ⟨true,U,by simp [L],noU⟩
    · exact ⟨true,W,by simp [L],noV⟩


/-- Every independent set outside the closed neighborhood of a shedding vertex
can be extended by a neighbor of that vertex. -/
def Shedding (G : SimpleGraph V) (x : V) : Prop :=
  ∀ I : Set V, G.IsIndepSet I → x ∉ I → (∀ i ∈ I, ¬G.Adj x i) →
    ∃ y, G.Adj x y ∧ ∀ i ∈ I, ¬G.Adj y i

/-- A chord of every quadrilateral, equivalently exclusion of induced four-cycles. -/
def NoInducedFourCycle (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d⦄, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
    G.Adj a c ∨ G.Adj b d

private theorem shedding_witness {G : SimpleGraph V} {x : V} (h : ¬ Shedding G x) :
    ∃ I : Set V, G.IsIndepSet I ∧ x ∉ I ∧ (∀ i ∈ I, ¬G.Adj x i) ∧
      ∀ y, G.Adj x y → ∃ i ∈ I, G.Adj y i := by
  classical
  simpa [Shedding, not_forall] using h

/-- A compatible graph with two adjacent non-shedding vertices must contain
an induced four-cycle. -/
theorem shedding_of_compatible {G : SimpleGraph V} (square : NoInducedFourCycle G)
    {t : CoreTerm Bool V} (ok : Compatible G t) {u v : V} (uv : G.Adj u v) :
    Shedding G u ∨ Shedding G v := by
  classical
  by_contra! hn
  obtain ⟨U,indU,nu,farU,du⟩ := shedding_witness hn.1
  obtain ⟨W,indW,nv,farW,dv⟩ := shedding_witness hn.2
  let B := (U ∩ G.neighborSet v) ∪ (W ∩ G.neighborSet u)
  have cross {a b : V} (ha : a ∈ U ∩ G.neighborSet v) (hb : b ∈ W ∩ G.neighborSet u)
      (ab : G.Adj a b) : False := by
    have ua : u ≠ a := fun eq => nu (eq ▸ ha.1)
    have vb : v ≠ b := fun eq => nv (eq ▸ hb.1)
    exact (square ua vb uv ha.2 ab (show G.Adj u b from hb.2).symm).elim (farU a ha.1) (farW b hb.1)
  have ind : G.IsIndepSet B := by
    intro a ha b hb e ab
    rcases ha with h | h <;> rcases hb with k | k
    · exact indU h.1 k.1 e ab
    · exact cross h k ab
    · exact cross k h ab.symm
    · exact indW h.1 k.1 e ab
  apply incompatible_of_edge_cut G uv Bᶜ U W ((G.isVertexCover_compl).mpr ind)
    du dv indU indW _ nu nv t ok
  intro x hx nx
  rcases hx with h | h
  · exact ⟨fun xu => farU x h xu.symm, fun xv => nx (.inl ⟨h,xv.symm⟩)⟩
  · exact ⟨fun xu => nx (.inr ⟨h,xu.symm⟩), fun xv => farW x h xv.symm⟩

private theorem collect {ι : Type*} [DecidableEq ι] (r : Bool) (S : Finset ι)
    (nonempty : S.Nonempty) (f : ι → CoreTerm Bool V) :
    ∃ t : CoreTerm Bool V,
      (∀ H, H ∈ Supports (!r) t ↔ ∃ i ∈ S, H ∈ Supports (!r) (f i)) ∧
      ∀ H ∈ Supports r t,
        (∀ i ∈ S, ∃ W ∈ Supports r (f i), W ⊆ H) ∧
        ∀ x ∈ H, ∃ i ∈ S, ∃ W ∈ Supports r (f i), W ⊆ H ∧ x ∈ W := by
  classical
  induction S using Finset.cons_induction with
  | empty => simp at nonempty
  | cons i S hi ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨t,forg,keep⟩ := ih hS
      refine ⟨choiceTerm r (f i) t,?_,?_⟩
      · intro H
        rw [foreign (show r ≠ !r by cases r <;> decide), forg]
        simp
      · intro H hH
        obtain ⟨L,hL,R,hR,rfl⟩ := owned.mp hH
        obtain ⟨all,points⟩ := keep R hR
        constructor
        · intro j hj
          rcases Finset.mem_cons.mp hj with rfl | hj
          · exact ⟨_,hL,Set.subset_union_left⟩
          · obtain ⟨W,hw,sub⟩ := all _ hj
            exact ⟨_,hw,sub.trans Set.subset_union_right⟩
        · rintro x (hx | hx)
          · exact ⟨i,by simp,L,hL,Set.subset_union_left,hx⟩
          · obtain ⟨j,hj,W,hw,sub,hx⟩ := points _ hx
            exact ⟨j,Finset.mem_cons.mpr (.inr hj),W,hw,sub.trans Set.subset_union_right,hx⟩
    · have eq := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨f i,by simp, fun H hh => ⟨by simpa using (show ∃ W ∈ Supports r (f i), W ⊆ H from
        ⟨H,hh,Set.Subset.rfl⟩), fun x hx => ⟨i,by simp,H,hh,Set.Subset.rfl,hx⟩⟩⟩

private theorem disjunction [Finite V] (S : Set V) (hS : S.Nonempty) :
    ∃ t : CoreTerm Bool V,
      (∀ H ∈ Supports false t, ∃ x ∈ S, H = {x}) ∧
      ∀ H ∈ Supports true t, H = S := by
  classical
  let N := S.toFinite.toFinset
  obtain ⟨z,hz⟩ := hS
  obtain ⟨t,p,n⟩ := collect true N ⟨z,by simpa [N] using hz⟩ (fun j : V => .var j)
  refine ⟨t,?_,?_⟩
  · intro H hH
    obtain ⟨u,hu,rfl⟩ := (p _).mp hH
    exact ⟨u,by simpa [N] using hu,rfl⟩
  · intro H hH
    obtain ⟨whole,part⟩ := n H hH
    ext x
    constructor
    · intro hx
      obtain ⟨j,hj,_,rfl,_,rfl⟩ := part x hx
      simpa [N] using hj
    · intro hx
      obtain ⟨_,rfl,sub⟩ := whole x (by simpa [N] using hx)
      exact sub rfl

/-- Every point of the shore belongs to a minimal cover inside any vertex
cover containing the entire shore. -/
def Robust (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃H⦄, G.IsVertexCover H → S ⊆ H →
    ∀ x ∈ S, ∃ C ⊆ H, Minimal G.IsVertexCover C ∧ x ∈ C

theorem neighborhood_robust [Finite V] (G : SimpleGraph V) (u : V) :
    Robust G (G.neighborSet u) :=
  fun _ cov sub _ hx => minimal_cover_through cov (show G.Adj u _ from hx).symm sub

/-- A union of complete bipartite rectangles with robust shores realizes the
graph edges and the minimal covers simultaneously. Rectangles may overlap. -/
theorem exists_compatible_edge_supports_of_rectangles [Finite V] {ι : Type*} [Finite ι]
    (G : SimpleGraph V) (edge : ∃ u v, G.Adj u v) (L R : ι → Set V)
    (left : ∀ i, (L i).Nonempty) (right : ∀ i, (R i).Nonempty)
    (cross : ∀ i, ∀ x ∈ L i, ∀ y ∈ R i, G.Adj x y)
    (cover : ∀ x y, G.Adj x y → ∃ i, (x ∈ L i ∧ y ∈ R i) ∨ (y ∈ L i ∧ x ∈ R i))
    (safeL : ∀ i, Robust G (L i)) (safeR : ∀ i, Robust G (R i)) :
    ∃ t : CoreTerm Bool V, Compatible G t ∧
      ∀ H ∈ Supports false t, ∃ x y, G.Adj x y ∧ H = {x, y} := by
  classical
  obtain ⟨a,b,ab⟩ := edge
  obtain ⟨index,_⟩ := cover a b ab
  choose l lp ln using fun i => disjunction (L i) (left i)
  choose r rp rn using fun i => disjunction (R i) (right i)
  let f (i : ι) := choiceTerm false (l i) (r i)
  have sides (i H) (h : H ∈ Supports true (f i)) : H = L i ∨ H = R i := by
    exact ((foreign (by decide : false ≠ true)).mp h).imp (ln i H) (rn i H)
  let _ := Fintype.ofFinite ι
  obtain ⟨t,p,n⟩ := collect true Finset.univ ⟨index,by simp⟩ f
  have pairs (H) (hH : H ∈ Supports false t) : ∃ x y, G.Adj x y ∧ H = {x, y} := by
    obtain ⟨i,_,hi⟩ := (p _).mp hH
    obtain ⟨A,hA,B,hB,rfl⟩ := owned.mp hi
    obtain ⟨x,hx,rfl⟩ := lp i A hA
    obtain ⟨y,hy,rfl⟩ := rp i B hB
    exact ⟨x, y, cross i x hx y hy, by ext z; simp [or_comm]⟩
  refine ⟨t, ⟨?_, ?_⟩, pairs⟩
  · intro H hH
    obtain ⟨x, y, xy, rfl⟩ := pairs H hH
    refine ⟨⟨x, by simp⟩, ?_⟩
    rintro z (rfl | rfl)
    · exact ⟨y, by simp, xy⟩
    · exact ⟨x, by simp, xy.symm⟩
  · intro H hH
    obtain ⟨all,points⟩ := n H hH
    have cov : G.IsVertexCover H := by
      intro x y xy
      obtain ⟨i,hi⟩ := cover x y xy
      obtain ⟨S,hS,sub⟩ := all i (by simp)
      rcases sides i S hS with rfl | rfl
      · exact hi.elim (fun h => .inl (sub h.1)) (fun h => .inr (sub h.1))
      · exact hi.elim (fun h => .inr (sub h.2)) (fun h => .inl (sub h.2))
    refine ⟨cov,?_⟩
    intro x hx
    obtain ⟨i,_,S,hS,sub,hxs⟩ := points x hx
    rcases sides i S hS with rfl | rfl
    · exact safeL i cov sub x hxs
    · exact safeR i cov sub x hxs

/-- A finite edge cover by complete rectangles with robust shores supplies a
compatible word. -/
theorem exists_compatible_of_rectangles [Finite V] {ι : Type*} [Finite ι]
    (G : SimpleGraph V) (edge : ∃ u v, G.Adj u v) (L R : ι → Set V)
    (left : ∀ i, (L i).Nonempty) (right : ∀ i, (R i).Nonempty)
    (cross : ∀ i, ∀ x ∈ L i, ∀ y ∈ R i, G.Adj x y)
    (cover : ∀ x y, G.Adj x y → ∃ i, (x ∈ L i ∧ y ∈ R i) ∨ (y ∈ L i ∧ x ∈ R i))
    (safeL : ∀ i, Robust G (L i)) (safeR : ∀ i, Robust G (R i)) :
    ∃ t : CoreTerm Bool V, Compatible G t := by
  obtain ⟨t, ht, _⟩ := exists_compatible_edge_supports_of_rectangles G edge L R
    left right cross cover safeL safeR
  exact ⟨t, ht⟩

private theorem shedding_neighbor {G : SimpleGraph V} {H : Set V}
    (cover : G.IsVertexCover H) {x : V} (hx : x ∈ H) (hs : Shedding G x) :
    ∃ u, G.Adj x u ∧ G.neighborSet u ⊆ H := by
  classical
  by_cases h : ∃ i ∈ Hᶜ, G.Adj x i
  · obtain ⟨i,hi,xi⟩ := h
    exact ⟨i,xi,fun _ hiy => (cover hiy).resolve_left hi⟩
  · have far : ∀ i ∈ Hᶜ, ¬G.Adj x i := fun i hi hxi => h ⟨i,hi,hxi⟩
    obtain ⟨y,xy,hy⟩ := hs Hᶜ (G.isIndepSet_compl_iff_isVertexCover.mpr cover)
      (by simpa using hx) far
    exact ⟨y,xy,fun z yz => by_contra fun hz => hy z hz yz⟩

/-- The disjunction of the stars of shedding centers realizes the two prescribed
pruning families whenever the centers cover all edges. -/
theorem exists_compatible_of_shedding [Finite V] (G : SimpleGraph V) (edge : ∃ u v, G.Adj u v)
    (every : ∀ u v, G.Adj u v → Shedding G u ∨ Shedding G v) :
    ∃ t : CoreTerm Bool V, Compatible G t := by
  classical
  let C := {v : V | Shedding G v ∧ (G.neighborSet v).Nonempty}
  apply exists_compatible_of_rectangles G edge (fun v : C => {v.val})
      (fun v : C => G.neighborSet v.val)
  · exact fun v => ⟨v.val,rfl⟩
  · exact fun v => v.property.2
  · intro v x hx y hy
    obtain rfl : x = v.val := hx
    exact hy
  · intro x y xy
    rcases every _ _ xy with hx | hy
    · exact ⟨⟨x,hx,y,xy⟩,.inl ⟨rfl,xy⟩⟩
    · exact ⟨⟨y,hy,x,xy.symm⟩,.inr ⟨rfl,xy.symm⟩⟩
  · intro v H cov sub x hx
    obtain rfl : x = v.val := hx
    obtain ⟨y,xy,hy⟩ := shedding_neighbor cov (sub rfl) v.property.1
    exact minimal_cover_through cov xy hy
  · exact fun v => neighborhood_robust G v.val

/-- For an arbitrary finite graph without induced four-cycles and with an edge,
compatibility holds exactly when its shedding vertices form a vertex cover. -/
theorem exists_compatible_iff_shedding [Finite V] (G : SimpleGraph V)
    (square : NoInducedFourCycle G) (edge : ∃ u v, G.Adj u v) :
    (∃ t : CoreTerm Bool V, Compatible G t) ↔ G.IsVertexCover {x | Shedding G x} := by
  constructor
  · rintro ⟨t,ht⟩ u v uv
    exact shedding_of_compatible square ht uv
  · exact fun h => exists_compatible_of_shedding G edge (fun _ _ uv => h uv)

end KFOL.Core.GraphPruning
