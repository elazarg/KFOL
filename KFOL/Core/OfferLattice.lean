module

public import Mathlib.Order.Irreducible
public import Mathlib.Data.Fintype.Order
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod

/-! # Which finite lattices can record uncovered source rows?

An offer removes every row containing its coalition at its owner. In a finite
lattice of survivor sets, a row is represented by the least element containing
it. The join- and meet-irreducibles determine the admissible owner colorings.
-/

@[expose] public section
namespace KFOL.Core.OfferLattice

variable {L Role Row Var : Type*} [Lattice L] [BoundedOrder L]

/-- Offers are nonempty. Omitting an offer needs no move in the history. -/
abbrev Offer (Role Var : Type*) := Role × {A : Set Var // A.Nonempty}

/-- Membership after all offers of a history have been made. -/
def Survives (block : Row → Role → Set Var) (h : Finset (Offer Role Var)) (z : Row) : Prop :=
  ∀ e ∈ h, ¬e.2.val ⊆ block z e.1

/-- These are exactly the rows that all histories preserving `T` must preserve.
A single offer of the offending block separates any other row. -/
theorem survives_every_history_iff (block : Row → Role → Set Var) (T : Set Row) (z : Row) :
    (∀ h, (∀ y ∈ T, Survives block h y) → Survives block h z) ↔
      ∀ r, (block z r).Nonempty → ∃ y ∈ T, block z r ⊆ block y r := by
  classical
  constructor
  · intro hp r hr
    by_contra! hn
    let e : Offer Role Var := (r, ⟨block z r, hr⟩)
    have hy (y : Row) (hy : y ∈ T) : Survives block {e} y := by
      intro f hf
      obtain rfl := Finset.mem_singleton.mp hf
      exact hn y hy
    exact hp {e} hy e (Finset.mem_singleton_self _) (fun _ h => h)
  · intro hp h keep e he sub
    obtain ⟨y, hy, hsub⟩ := hp e.1 (e.2.property.mono sub)
    exact keep y hy e he (sub.trans hsub)

/-- A presentation by proper rows. The point of a row is its singleton
closure: it lies below precisely the lattice elements containing the row.
The last two fields say that an offer has its stated effect and every
lattice element is reached by a finite history of offers. -/
structure Presentation (L Role Row Var : Type*) [Lattice L] [BoundedOrder L] where
  point : Row → L
  separates : ∀ x y : L, (∀ z, point z ≤ x → point z ≤ y) → x ≤ y
  block : Row → Role → Set Var
  proper : ∀ z, ∃ r, block z r = ∅
  cut : Offer Role Var → L
  mem_cut : ∀ z e, point z ≤ cut e ↔ ¬e.2.val ⊆ block z e.1
  generates : ∀ x : L, ∃ h : Finset (Offer Role Var), h.inf cut = x

/-- The extent of the meet of the cuts is the actual surviving set. -/
theorem Presentation.le_history_iff (p : Presentation L Role Row Var)
    (z : Row) (h : Finset (Offer Role Var)) :
    p.point z ≤ h.inf p.cut ↔ Survives p.block h z := by
  exact ⟨fun hz e he => (p.mem_cut z e).1 (hz.trans (Finset.inf_le he)),
    fun hs => Finset.le_inf fun e he => (p.mem_cut z e).2 (hs e he)⟩

/-- Actual states, ordered by inclusion of the rows surviving a finite history. -/
abbrev State (block : Row → Role → Set Var) :=
  {S : Set Row // ∃ h : Finset (Offer Role Var), S = {z | Survives block h z}}

/-- The state reached by a specified history. -/
def afterOffers (block : Row → Role → Set Var) (h : Finset (Offer Role Var)) :
    State block := ⟨_, h, rfl⟩

/-- A presentation identifies the given lattice with the actual sets of surviving rows. -/
noncomputable def Presentation.orderIso (p : Presentation L Role Row Var) :
    L ≃o State p.block := by
  classical
  let extent (x : L) : State p.block := ⟨{z | p.point z ≤ x}, by
    obtain ⟨h, rfl⟩ := p.generates x
    exact ⟨h, Set.ext fun z => p.le_history_iff z h⟩⟩
  have hmem (z : Row) (x : L) : z ∈ (extent x).val ↔ p.point z ≤ x := by
    rfl
  have hord (x y : L) : extent x ≤ extent y ↔ x ≤ y := by
    constructor
    · intro h
      exact p.separates x y fun z hz => (hmem z y).1 (h ((hmem z x).2 hz))
    · intro h z hz
      exact (hmem z y).2 (((hmem z x).1 hz).trans h)
  refine OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff extent (fun _ _ => hord _ _)) ?_
  rintro ⟨_, h, rfl⟩
  refine ⟨h.inf p.cut, Subtype.ext (Set.ext fun z => ?_)⟩
  exact (hmem z _).trans (p.le_history_iff z h)

/-- Every finite survivor system admits the point presentation used in the
coloring criterion. Offer all coalitions that leave a particular row unhit
to obtain the least reachable state containing that row. -/
noncomputable def ofOrderIso [Fintype Role] [Fintype Var]
    (block : Row → Role → Set Var) (proper : ∀ z, ∃ r, block z r = ∅)
    (f : L ≃o State block) : Presentation L Role Row Var := by
  classical
  let preserve (z : Row) : Finset (Offer Role Var) :=
    Finset.univ.filter fun e => ¬e.2.val ⊆ block z e.1
  let point (z : Row) := f.symm (afterOffers block (preserve z))
  have hmem (z : Row) (x : L) : point z ≤ x ↔ z ∈ (f x).val := by
    change f.symm _ ≤ x ↔ _
    rw [f.symm_apply_le]
    constructor
    · intro h
      apply h
      exact fun e he => (Finset.mem_filter.mp he).2
    · intro hz
      obtain ⟨h, hh⟩ := (f x).property
      change {y | Survives block (preserve z) y} ⊆ (f x).val
      rw [hh] at hz ⊢
      intro y hy e he
      exact hy e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz e he⟩)
  let cut (e : Offer Role Var) : L := f.symm (afterOffers block {e})
  have hcut (e : Offer Role Var) (z : Row) : point z ≤ cut e ↔ ¬e.2.val ⊆ block z e.1 := by
    rw [hmem z]
    dsimp only [cut]
    rw [f.apply_symm_apply]
    simp [afterOffers, Survives]
  have hsep (x y : L) (h : ∀ z, point z ≤ x → point z ≤ y) : x ≤ y := by
    apply f.le_iff_le.mp
    intro z hz
    exact (hmem z y).1 (h z ((hmem z x).2 hz))
  refine { point := point, separates := hsep, block := block, proper := proper,
           cut := cut, mem_cut := fun z e => hcut e z, generates := ?_ }
  intro x
  obtain ⟨h, hh⟩ := (f x).property
  have hx (z : Row) : point z ≤ h.inf cut ↔ point z ≤ x := by
    rw [hmem z x, hh]
    exact ⟨fun hz e he => (hcut e z).1 (hz.trans (Finset.inf_le he)),
      fun hz => Finset.le_inf fun e he => (hcut e z).2 (hz e he)⟩
  exact ⟨h, le_antisymm (hsep _ _ fun z => (hx z).1) (hsep _ _ fun z => (hx z).2)⟩

abbrev MeetIrred (L : Type*) [Lattice L] := {m : L // InfIrred m}
abbrev JoinIrred (L : Type*) [Lattice L] := {j : L // SupIrred j}

/-- Every irreducible row omits an owner. The missing meet-irreducibles
of each color have a common upper bound still missing that row. -/
def Admissible (c : MeetIrred L → Role) : Prop :=
  ∀ j : JoinIrred L,
    (∃ r, ∀ m, c m = r → j.val ≤ m.val) ∧
    (∀ r, ∃ x : L, ¬j.val ≤ x ∧ ∀ m, c m = r → ¬j.val ≤ m.val → m.val ≤ x)

private theorem Presentation.exists_point [Fintype Row] (p : Presentation L Role Row Var)
    (j : JoinIrred L) : ∃ z, p.point z = j.val := by
  classical
  let s := Finset.univ.filter fun z => p.point z ≤ j.val
  have hj : s.sup p.point = j.val := by
    apply le_antisymm
    · exact Finset.sup_le fun _ hz => (Finset.mem_filter.mp hz).2
    · apply p.separates
      intro z hz
      exact Finset.le_sup (s := s) (f := p.point) (by simpa [s] using hz)
  obtain ⟨z, _, heq⟩ := j.property.finset_sup_eq hj
  exact ⟨z, heq⟩

/-- Choosing one generating offer for every meet-irreducible gives an
admissible coloring of any finite system of proper rows. -/
theorem Presentation.exists_admissible [Fintype Row] (p : Presentation L Role Row Var) :
    ∃ c : MeetIrred L → Role, Admissible c := by
  classical
  have gen (m : MeetIrred L) : ∃ e, p.cut e = m.val := by
    obtain ⟨h, hh⟩ := p.generates m
    obtain ⟨e, _, hm⟩ := m.property.finset_inf_eq hh
    exact ⟨e, hm⟩
  choose e he using gen
  refine ⟨fun m => (e m).1, fun j => ?_⟩
  obtain ⟨z, hz⟩ := p.exists_point j
  obtain ⟨r₀, h₀⟩ := p.proper z
  have covered (m : MeetIrred L) (hm : ¬j.val ≤ m.val) :
      (e m).2.val ⊆ p.block z (e m).1 := by
    by_contra hn
    exact hm (by simpa only [hz, he] using (p.mem_cut z (e m)).2 hn)
  constructor
  · refine ⟨r₀, fun m hr => ?_⟩
    by_contra hm
    have hh := (e m).2.property.mono (covered m hm)
    change (e m).1 = r₀ at hr
    rw [hr, h₀] at hh
    exact Set.not_nonempty_empty hh
  · intro r
    by_cases h : (p.block z r).Nonempty
    · let f : Offer Role Var := (r, ⟨p.block z r, h⟩)
      refine ⟨p.cut f, ?_, fun m hr hm => ?_⟩
      · rw [← hz, p.mem_cut]
        exact fun hn => hn (fun _ hx => hx)
      · rw [← he m]
        apply p.separates
        intro y hy
        apply (p.mem_cut y f).2
        intro hsub
        have hA := covered m hm
        change (e m).1 = r at hr
        rw [hr] at hA
        apply (p.mem_cut y (e m)).1 hy
        rw [hr]
        exact hA.trans hsub
    · refine ⟨⊥, fun hj => j.property.ne_bot (le_bot_iff.mp hj), fun m hr hm => ?_⟩
      have hA := (e m).2.property.mono (covered m hm)
      exact (h (hr ▸ hA)).elim

/-- The meet-irreducible indexed by an input is posted on exactly those
irreducible rows missing it, at its designated owner. -/
def canonicalBlock (c : MeetIrred L → Role) (j : JoinIrred L) (r : Role) : Set (MeetIrred L) :=
  {m | c m = r ∧ ¬j.val ≤ m.val}

/-- A monochromatic offer keeps the join of its inputs. Other offers keep the top. -/
noncomputable def canonicalCut [Fintype L] (c : MeetIrred L → Role)
    (e : Offer Role (MeetIrred L)) : L := by
  classical
  exact if ∀ m ∈ e.2.val, c m = e.1 then e.2.val.toFinite.toFinset.sup Subtype.val else ⊤

theorem canonicalCut_spec [Fintype L] {c : MeetIrred L → Role} (hc : Admissible c)
    (j : JoinIrred L) (e : Offer Role (MeetIrred L)) :
    j.val ≤ canonicalCut c e ↔ ¬e.2.val ⊆ canonicalBlock c j e.1 := by
  classical
  by_cases he : ∀ m ∈ e.2.val, c m = e.1
  · rw [canonicalCut, ite_eq_left he]
    constructor
    · intro hj hs
      obtain ⟨x, hx, hmx⟩ := (hc j).2 e.1
      apply hx (hj.trans (Finset.sup_le ?_))
      intro m hm
      have hm' : m ∈ e.2.val := by simpa using hm
      exact hmx m (he m hm') (hs hm').2
    · intro hn
      by_contra hj
      apply hn
      intro m hm
      exact ⟨he m hm, fun hjm => hj (Finset.le_sup_of_le (by simpa using hm) hjm)⟩
  · rw [canonicalCut, ite_eq_right he]
    exact ⟨fun _ hs => he (fun _ hm => (hs hm).1), fun _ => le_top⟩

/-- Conversely every admissible coloring has a presentation with one row
per join-irreducible and one posted input per meet-irreducible. -/
noncomputable def canonicalPresentation [Fintype L] {c : MeetIrred L → Role} (hc : Admissible c) :
    Presentation L Role (JoinIrred L) (MeetIrred L) := by
  classical
  refine { point := Subtype.val, block := canonicalBlock c, cut := canonicalCut c,
           separates := ?_, proper := ?_, mem_cut := canonicalCut_spec hc, generates := ?_ }
  · intro x y hxy
    obtain ⟨s, hs, hi⟩ := exists_supIrred_decomposition x
    rw [← hs]
    exact Finset.sup_le fun a ha => hxy ⟨a, hi ha⟩ (hs ▸ Finset.le_sup (f := id) ha)
  · intro j
    obtain ⟨r, hr⟩ := (hc j).1
    exact ⟨r, Set.eq_empty_iff_forall_notMem.mpr fun m hm => hm.2 (hr m hm.1)⟩
  · intro x
    obtain ⟨s, hs, hi⟩ := exists_infIrred_decomposition x
    let offer (a : s) : Offer Role (MeetIrred L) :=
      let m : MeetIrred L := ⟨a.val, hi a.property⟩
      (c m, ⟨{m}, Set.singleton_nonempty _⟩)
    have he (a : s) : canonicalCut c (offer a) = a.val := by
      simp [canonicalCut, offer, Finset.filter_eq']
    refine ⟨s.attach.image offer, ?_⟩
    rw [Finset.inf_image]
    calc
      s.attach.inf (canonicalCut c ∘ offer) = s.attach.inf (fun a => a.val) :=
        Finset.inf_congr rfl fun a _ => he a
      _ = x := (Finset.inf_attach s id).trans hs

universe u

/-- A finite lattice is the order of reachable survivor sets of finite,
proper partial colorings exactly when its irreducibles admit an owner coloring. -/
theorem survivor_lattice_iff {L : Type u} [Lattice L] [BoundedOrder L] [Fintype L]
    (Role : Type*) [Fintype Role] :
    (∃ (Row Var : Type u) (_ : Fintype Row) (_ : Fintype Var) (block : Row → Role → Set Var),
      (∀ z, ∃ r, block z r = ∅) ∧
      (∀ z r s, r ≠ s → Disjoint (block z r) (block z s)) ∧ Nonempty (L ≃o State block)) ↔
    ∃ c : MeetIrred L → Role, Admissible c := by
  classical
  constructor
  · rintro ⟨Row, Var, hR, hV, block, hp, _, ⟨f⟩⟩
    exact (ofOrderIso block hp f).exists_admissible
  · rintro ⟨c, hc⟩
    let p := canonicalPresentation hc
    refine ⟨JoinIrred L, MeetIrred L, inferInstance, inferInstance, canonicalBlock c,
      p.proper, ?_, ⟨p.orderIso⟩⟩
    intro z r s hrs
    exact Set.disjoint_left.mpr fun m hr hs => hrs (hr.1.symm.trans hs.1)

end KFOL.Core.OfferLattice
