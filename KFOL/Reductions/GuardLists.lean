module

public import KFOL.Definitions.RecognitionProblem
public import KFOL.Core.SourceLosses

/-! # Listing the prime guards of a system of losses

When every input has at most four losses, the prime guards are the minimal
choices of one posting from each loss. The list program below computes them
from the listed losses, and its output presents the prime guards of any
operation with that system of losses.
-/

@[expose] public section

namespace KFOL.Recognition.Lists

open Core.Sources Problems

/-! ### Choosing one posting from each of four losses -/

/-- The first loss. -/
def pick0 (zs : List (List (ℕ × ℕ))) : List (ℕ × ℕ) := zs.headD []

/-- The second loss, or the first when there is none. -/
def pick1 (zs : List (List (ℕ × ℕ))) : List (ℕ × ℕ) := (zs.tail ++ [zs.headD []]).headD []

/-- The third loss, or the first when there is none. -/
def pick2 (zs : List (List (ℕ × ℕ))) : List (ℕ × ℕ) :=
  (zs.tail.tail ++ [zs.headD []]).headD []

/-- The fourth loss, or the first when there is none. -/
def pick3 (zs : List (List (ℕ × ℕ))) : List (ℕ × ℕ) :=
  (zs.tail.tail.tail ++ [zs.headD []]).headD []

/-- One posting from each loss. -/
def selections (zs : List (List (ℕ × ℕ))) : List (List (ℕ × ℕ)) :=
  if zs.isEmpty then [[]] else
    (pick0 zs).flatMap fun a => (pick1 zs).flatMap fun b =>
      (pick2 zs).flatMap fun c => (pick3 zs).map fun d => [a, b, c, d]

/-- Inclusion of lists of postings. -/
def subsetB (g h : List (ℕ × ℕ)) : Bool :=
  g.all fun a => h.any fun b => a.1 == b.1 && a.2 == b.2

/-- The selections that contain no smaller selection. -/
def primesOf (zs : List (List (ℕ × ℕ))) : List (List (ℕ × ℕ)) :=
  (selections zs).filter fun g => (selections zs).all fun h => !subsetB h g || subsetB g h

/-- The guards of every observer at every source, from the losses of the
sources. -/
def entriesOf (K : ℕ) (src : List (ℕ × List (List (ℕ × ℕ)))) :
    List ((ℕ × ℕ) × List (ℕ × ℕ)) :=
  (List.range K).flatMap fun k => src.flatMap fun s =>
    (primesOf (s.2.filter fun z => z.all fun q => !(q.2 == k))).map fun g => ((k, s.1), g)

variable {zs : List (List (ℕ × ℕ))} {g : List (ℕ × ℕ)}

theorem mem_picks (h4 : zs.length ≤ 4) {z : List (ℕ × ℕ)} (hz : z ∈ zs) :
    z = pick0 zs ∨ z = pick1 zs ∨ z = pick2 zs ∨ z = pick3 zs := by
  rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩
  · cases hz
  · simp_all [pick0]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> simp [pick0, pick1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> simp [pick0, pick1, pick2]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp [pick0, pick1, pick2, pick3]
  · simp only [List.length_cons] at h4
    omega

theorem pick_mem (hne : zs ≠ []) :
    pick0 zs ∈ zs ∧ pick1 zs ∈ zs ∧ pick2 zs ∈ zs ∧ pick3 zs ∈ zs := by
  rcases zs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩
  · exact absurd rfl hne
  · simp [pick0, pick1, pick2, pick3]
  · simp [pick0, pick1, pick2, pick3]
  · simp [pick0, pick1, pick2, pick3]
  · simp [pick0, pick1, pick2, pick3]

theorem mem_selections (hne : zs ≠ []) :
    g ∈ selections zs ↔ ∃ a ∈ pick0 zs, ∃ b ∈ pick1 zs, ∃ c ∈ pick2 zs, ∃ d ∈ pick3 zs,
      g = [a, b, c, d] := by
  have he : zs.isEmpty = false := by simpa using hne
  simp only [selections, he, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    exact ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩
    exact ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩

/-- A selection contains a posting of every loss. -/
theorem selections_hit (h4 : zs.length ≤ 4) (hg : g ∈ selections zs) :
    ∀ z ∈ zs, ∃ a ∈ z, a ∈ g := by
  intro z hz
  have hne : zs ≠ [] := List.ne_nil_of_mem hz
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := (mem_selections hne).1 hg
  rcases mem_picks h4 hz with rfl | rfl | rfl | rfl
  · exact ⟨a, ha, by simp⟩
  · exact ⟨b, hb, by simp⟩
  · exact ⟨c, hc, by simp⟩
  · exact ⟨d, hd, by simp⟩

/-- A selection consists of postings of the losses. -/
theorem selections_sub (hg : g ∈ selections zs) : ∀ a ∈ g, ∃ z ∈ zs, a ∈ z := by
  intro x hx
  by_cases hne : zs = []
  · subst hne
    simp only [selections, List.isEmpty_nil, ↓reduceIte, List.mem_singleton] at hg
    subst hg
    cases hx
  · obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := (mem_selections hne).1 hg
    obtain ⟨h0, h1, h2, h3⟩ := pick_mem hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨_, h0, ha⟩
    · exact ⟨_, h1, hb⟩
    · exact ⟨_, h2, hc⟩
    · exact ⟨_, h3, hd⟩

/-- Every set meeting all losses contains a selection. -/
theorem exists_selection (H : ℕ × ℕ → Prop) (hH : ∀ z ∈ zs, ∃ a ∈ z, H a) :
    ∃ g ∈ selections zs, ∀ a ∈ g, H a := by
  by_cases hne : zs = []
  · subst hne
    exact ⟨[], by simp [selections], fun a ha => by cases ha⟩
  · obtain ⟨h0, h1, h2, h3⟩ := pick_mem hne
    obtain ⟨a, ha, Ha⟩ := hH _ h0
    obtain ⟨b, hb, Hb⟩ := hH _ h1
    obtain ⟨c, hc, Hc⟩ := hH _ h2
    obtain ⟨d, hd, Hd⟩ := hH _ h3
    refine ⟨[a, b, c, d], (mem_selections hne).2 ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption

theorem subsetB_iff (g h : List (ℕ × ℕ)) : subsetB g h = true ↔ ∀ a ∈ g, a ∈ h := by
  simp only [subsetB, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine forall₂_congr fun a _ => ⟨?_, fun ha => ⟨a, ha, rfl, rfl⟩⟩
  rintro ⟨b, hb, h1, h2⟩
  rwa [show a = b from Prod.ext h1 h2]

/-- A set of postings meets every loss and no proper subset does. -/
def MinHit (zs : List (List (ℕ × ℕ))) (H : Set (ℕ × ℕ)) : Prop :=
  (∀ z ∈ zs, ∃ a ∈ z, a ∈ H) ∧
    ∀ H' : Set (ℕ × ℕ), H' ⊆ H → (∀ z ∈ zs, ∃ a ∈ z, a ∈ H') → H ⊆ H'

theorem mem_primesOf :
    g ∈ primesOf zs ↔ g ∈ selections zs ∧
      ∀ h ∈ selections zs, (∀ a ∈ h, a ∈ g) → ∀ a ∈ g, a ∈ h := by
  simp only [primesOf, List.mem_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    ← Bool.not_eq_true, subsetB_iff]
  exact and_congr_right fun _ => forall₂_congr fun h _ => by tauto

theorem primesOf_minHit (h4 : zs.length ≤ 4) (hg : g ∈ primesOf zs) :
    MinHit zs {a | a ∈ g} := by
  obtain ⟨hsel, hmin⟩ := mem_primesOf.1 hg
  refine ⟨selections_hit h4 hsel, fun H' hsub hhit a ha => ?_⟩
  obtain ⟨h, hh, hH'⟩ := exists_selection (fun a => a ∈ H') hhit
  exact hH' a (hmin h hh (fun b hb => hsub (hH' b hb)) a ha)

theorem exists_primesOf (h4 : zs.length ≤ 4) {H : Set (ℕ × ℕ)} (hH : MinHit zs H) :
    ∃ g ∈ primesOf zs, ∀ a, a ∈ g ↔ a ∈ H := by
  obtain ⟨h, hh, hsub⟩ := exists_selection (fun a => a ∈ H) hH.1
  have hsup : H ⊆ {a | a ∈ h} := hH.2 {a | a ∈ h} hsub (selections_hit h4 hh)
  refine ⟨h, mem_primesOf.2 ⟨hh, fun h' hh' hsub' a ha => ?_⟩, fun a => ⟨hsub a, fun ha => hsup ha⟩⟩
  exact hH.2 {a | a ∈ h'} (fun b hb => hsub b (hsub' b hb)) (selections_hit h4 hh') (hsub a ha)

theorem mem_entriesOf {K : ℕ} {src : List (ℕ × List (List (ℕ × ℕ)))}
    {e : (ℕ × ℕ) × List (ℕ × ℕ)} :
    e ∈ entriesOf K src ↔ ∃ k < K, ∃ s ∈ src,
      ∃ g ∈ primesOf (s.2.filter fun z => z.all fun q => !(q.2 == k)), e = ((k, s.1), g) := by
  simp only [entriesOf, List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨k, hk, s, hs, g, hg, rfl⟩
    exact ⟨k, hk, s, hs, g, hg, rfl⟩
  · rintro ⟨k, hk, s, hs, g, hg, rfl⟩
    exact ⟨k, hk, s, hs, g, hg, rfl⟩

/-! ### The listed guards present the prime guards -/

section Presents

variable {K : ℕ} {Var : Type}

/-- A list of numbered postings lists a loss. -/
def PostsMatch (name : Var → ℕ) (z' : List (ℕ × ℕ)) (z : List (Var × Fin K)) : Prop :=
  ∀ a r, (a, r) ∈ z' ↔ ∃ q ∈ z, name q.1 = a ∧ q.2.val = r

/-- Lists of numbered postings list the losses of an input. -/
def LossesMatch (name : Var → ℕ) (zs' : List (List (ℕ × ℕ)))
    (zs : List (List (Var × Fin K))) : Prop :=
  (∀ z ∈ zs, ∃ z' ∈ zs', PostsMatch name z' z) ∧ ∀ z' ∈ zs', ∃ z ∈ zs, PostsMatch name z' z

/-- The numbered posting of a literal. -/
def litCode (name : Var → ℕ) {k : Fin K} {j : Var} (a : Literal k j) : ℕ × ℕ :=
  (name a.1.val, a.2.val.val)

theorem litCode_injective {name : Var → ℕ} (hname : Function.Injective name) (k : Fin K)
    (j : Var) : Function.Injective (litCode name : Literal k j → ℕ × ℕ) := by
  intro a b h
  have h1 : name a.1.val = name b.1.val := congrArg Prod.fst h
  have h2 : a.2.val.val = b.2.val.val := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext (hname h1)) (Subtype.ext (Fin.ext h2))

variable [Fintype Var] {f : (Var → WinnerSet (Fin K)) → WinnerSet (Fin K)}
  {zeros : Var → List (List (Var × Fin K))}

/-- The losses of an input that do not name the observer. -/
def lossesFor (k : ℕ) (zs' : List (List (ℕ × ℕ))) : List (List (ℕ × ℕ)) :=
  zs'.filter fun z => z.all fun q => !(q.2 == k)

theorem mem_lossesFor {k : ℕ} {zs' : List (List (ℕ × ℕ))} {z : List (ℕ × ℕ)} :
    z ∈ lossesFor k zs' ↔ z ∈ zs' ∧ ∀ q ∈ z, q.2 ≠ k := by
  simp [lossesFor]

omit [Fintype Var] in
theorem meetsAll_iff {name : Var → ℕ} (hname : Function.Injective name) {k : Fin K} {j : Var}
    {zs' : List (List (ℕ × ℕ))} (hm : LossesMatch name zs' (zeros j)) (g : Guard k j) :
    MeetsAll (zeros j) g ↔
      ∀ z' ∈ lossesFor k.val zs', ∃ a ∈ z', a ∈ litCode name '' (g : Set (Literal k j)) := by
  constructor
  · intro hall z' hz'
    obtain ⟨hz', hk⟩ := mem_lossesFor.1 hz'
    obtain ⟨z, hz, hmatch⟩ := hm.2 z' hz'
    have hk' : ∀ q ∈ z, q.2 ≠ k := fun q hq hqk =>
      hk (name q.1, q.2.val) ((hmatch _ _).2 ⟨q, hq, rfl, rfl⟩) (congrArg Fin.val hqk)
    obtain ⟨a, ha, haz⟩ := hall z hz hk'
    exact ⟨litCode name a, (hmatch _ _).2 ⟨_, haz, rfl, rfl⟩, a, ha, rfl⟩
  · intro hall z hz hk
    obtain ⟨z', hz', hmatch⟩ := hm.1 z hz
    have hk' : ∀ q ∈ z', q.2 ≠ k.val := by
      rintro ⟨a, r⟩ hq hqk
      obtain ⟨q, hq', -, rfl⟩ := (hmatch a r).1 hq
      exact hk q hq' (Fin.ext hqk)
    obtain ⟨_, haz, a, ha, rfl⟩ := hall z' (mem_lossesFor.2 ⟨hz', hk'⟩)
    obtain ⟨q, hq, h1, h2⟩ := (hmatch _ _).1 haz
    have e : q = (a.1.val, a.2.val) := Prod.ext (hname h1) (Fin.ext h2)
    exact ⟨a, ha, e ▸ hq⟩

omit [Fintype Var] in
theorem minimal_iff_minHit {name : Var → ℕ} (hname : Function.Injective name) {k : Fin K}
    {j : Var} {zs' : List (List (ℕ × ℕ))} (hm : LossesMatch name zs' (zeros j))
    (g : Guard k j) :
    Minimal (MeetsAll (zeros j)) g ↔
      MinHit (lossesFor k.val zs') (litCode name '' (g : Set (Literal k j))) := by
  classical
  constructor
  · intro hg
    refine ⟨(meetsAll_iff hname hm g).1 hg.prop, fun H' hsub hhit => ?_⟩
    let g' : Guard k j := g.filter fun a => litCode name a ∈ H'
    have himg : ∀ a, a ∈ H' → a ∈ litCode name '' (g' : Set (Literal k j)) := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := hsub ha
      exact ⟨b, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hb, ha⟩), rfl⟩
    have hall : MeetsAll (zeros j) g' := (meetsAll_iff hname hm g').2 fun z' hz' => by
      obtain ⟨a, haz, ha⟩ := hhit z' hz'
      exact ⟨a, haz, himg a ha⟩
    have hle : g ≤ g' := hg.2 hall (Finset.filter_subset _ _)
    rintro _ ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.1 (hle ha)).2
  · rintro ⟨hhit, hmin⟩
    refine ⟨(meetsAll_iff hname hm g).2 hhit, fun g' hg' hle a ha => ?_⟩
    have hsub : litCode name '' (g' : Set (Literal k j)) ⊆ litCode name '' (g : Set _) :=
      Set.image_mono fun b hb => hle hb
    obtain ⟨b, hb, hab⟩ := hmin _ hsub ((meetsAll_iff hname hm g').1 hg') ⟨a, ha, rfl⟩
    rwa [← litCode_injective hname k j hab]

theorem exists_guard_of_minHit (h : LossSystem f zeros) {name : Var → ℕ} {k : Fin K} {j : Var}
    {zs' : List (List (ℕ × ℕ))} (hm : LossesMatch name zs' (zeros j)) {H : Set (ℕ × ℕ)}
    (hH : MinHit (lossesFor k.val zs') H) :
    ∃ g : Guard k j, litCode name '' (g : Set (Literal k j)) = H := by
  classical
  have hcover : ∀ a ∈ H, ∃ z' ∈ lossesFor k.val zs', a ∈ z' := by
    have hsub := hH.2 {a | a ∈ H ∧ ∃ z' ∈ lossesFor k.val zs', a ∈ z'} (fun a ha => ha.1)
      (fun z' hz' => by
        obtain ⟨a, haz, ha⟩ := hH.1 z' hz'
        exact ⟨a, haz, ha, z', hz', haz⟩)
    exact fun a ha => (hsub ha).2
  refine ⟨Finset.univ.filter fun a => litCode name a ∈ H, ?_⟩
  ext ⟨a, r⟩
  constructor
  · rintro ⟨b, hb, hab⟩
    rw [← hab]
    exact (Finset.mem_filter.1 hb).2
  · intro ha
    obtain ⟨z', hz', haz⟩ := hcover _ ha
    obtain ⟨hz'', hk⟩ := mem_lossesFor.1 hz'
    obtain ⟨z, hz, hmatch⟩ := hm.2 z' hz''
    obtain ⟨q, hq, h1, h2⟩ := (hmatch a r).1 haz
    have hi : q.1 ≠ j := h.off_source j z hz q hq
    have hr : q.2 ≠ k := fun e => hk _ haz (by rw [← h2, e])
    refine ⟨(⟨q.1, hi⟩, ⟨q.2, hr⟩), ?_, Prod.ext h1 h2⟩
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    have e : litCode name ((⟨q.1, hi⟩, ⟨q.2, hr⟩) : Literal k j) = (a, r) := Prod.ext h1 h2
    rw [e]
    exact ha

omit [Fintype Var] in
theorem namesGuard_of_image {name : Var → ℕ} {k : Fin K} {j : Var} {l : List (ℕ × ℕ)}
    {g : Guard k j} (hl : ∀ a, a ∈ l ↔ a ∈ litCode name '' (g : Set (Literal k j))) :
    NamesGuard name l g := by
  intro a r
  rw [hl]
  constructor
  · rintro ⟨q, hq, e⟩
    exact ⟨q, hq, congrArg Prod.fst e, congrArg Prod.snd e⟩
  · rintro ⟨q, hq, h1, h2⟩
    exact ⟨q, hq, Prod.ext h1 h2⟩

/-- **The listed guards are the prime guards.** For an operation with a
system of losses, at most four at each input, the list program presents its
prime guards. -/
theorem presents_entriesOf (three : Fin 3 ↪ Fin K) (h : LossSystem f zeros) (name : Var → ℕ)
    (hname : Function.Injective name) (src : List (ℕ × List (List (ℕ × ℕ))))
    (h1 : ∀ j, ∃ s ∈ src, s.1 = name j)
    (h2 : ∀ s ∈ src, ∃ j, s.1 = name j ∧ s.2.length ≤ 4 ∧ LossesMatch name s.2 (zeros j)) :
    Presents name (entriesOf K src) (normalForm three f) := by
  have hlen : ∀ (k : ℕ) (zs' : List (List (ℕ × ℕ))), zs'.length ≤ 4 →
      (lossesFor k zs').length ≤ 4 := fun k zs' h4 => (List.length_filter_le _ _).trans h4
  constructor
  · intro k j g hg
    obtain ⟨s, hs, hsj⟩ := h1 j
    obtain ⟨j', hsj', h4, hm⟩ := h2 s hs
    obtain rfl : j' = j := hname (hsj'.symm.trans hsj)
    have hmin := (minimal_iff_minHit hname hm g).1 ((h.mem_normalForm_iff three k j' g).1 hg)
    obtain ⟨l, hl, hlH⟩ := exists_primesOf (hlen k.val s.2 h4) hmin
    exact ⟨((k.val, s.1), l), mem_entriesOf.2 ⟨k.val, k.isLt, s, hs, l, hl, rfl⟩,
      by rw [hsj], namesGuard_of_image hlH⟩
  · intro e he
    obtain ⟨k', hk', s, hs, l, hl, rfl⟩ := mem_entriesOf.1 he
    obtain ⟨j, hsj, h4, hm⟩ := h2 s hs
    have hmin : MinHit (lossesFor (⟨k', hk'⟩ : Fin K).val s.2) {a | a ∈ l} :=
      primesOf_minHit (hlen k' s.2 h4) hl
    obtain ⟨g, hg⟩ := exists_guard_of_minHit (k := ⟨k', hk'⟩) h hm hmin
    refine ⟨⟨k', hk'⟩, j, g, ?_, by rw [hsj], namesGuard_of_image fun a => by rw [hg]; rfl⟩
    rw [h.mem_normalForm_iff three, minimal_iff_minHit hname hm g, hg]
    exact hmin

/-- A guard of one presentation has a guard of the other with no new postings. -/
theorem exists_guard_of_presents {V₁ V₂ : Type} {name₁ : V₁ → ℕ} {name₂ : V₂ → ℕ}
    (h₂ : Function.Injective name₂) {entries : List ((ℕ × ℕ) × List (ℕ × ℕ))}
    {G₁ : ∀ (k : Fin K) (j : V₁), Finset (Guard k j)}
    {G₂ : ∀ (k : Fin K) (j : V₂), Finset (Guard k j)}
    (p₁ : Presents name₁ entries G₁) (p₂ : Presents name₂ entries G₂) {k : Fin K} {j₁ : V₁}
    {g₁ : Guard k j₁} (hg₁ : g₁ ∈ G₁ k j₁) {j₂ : V₂} (hj : name₂ j₂ = name₁ j₁) :
    ∃ g₂ ∈ G₂ k j₂, ∀ b ∈ g₂, ∃ a ∈ g₁, name₁ a.1.val = name₂ b.1.val ∧
      a.2.val = b.2.val := by
  obtain ⟨e, he, he1, hn₁⟩ := p₁.1 k j₁ g₁ hg₁
  obtain ⟨k', j', g', hg', he2, hn₂⟩ := p₂.2 e he
  have hkj : (k'.val, name₂ j') = (k.val, name₁ j₁) := he2.symm.trans he1
  obtain rfl : k' = k := Fin.ext (congrArg Prod.fst hkj)
  obtain rfl : j' = j₂ := h₂ ((congrArg Prod.snd hkj).trans hj.symm)
  refine ⟨g', hg', fun b hb => ?_⟩
  obtain ⟨a, ha, h1, h2⟩ := (hn₁ _ _).1 ((hn₂ _ _).2 ⟨b, hb, rfl, rfl⟩)
  exact ⟨a, ha, h1, Fin.ext h2⟩

/-- Two presentations of one list by guards on inputs with the same names
have the same meaning. -/
theorem meaning_eq_of_presents {V₁ V₂ : Type} {name₁ : V₁ → ℕ} {name₂ : V₂ → ℕ}
    (h₁ : Function.Injective name₁) (h₂ : Function.Injective name₂)
    {entries : List ((ℕ × ℕ) × List (ℕ × ℕ))}
    {G₁ : ∀ (k : Fin K) (j : V₁), Finset (Guard k j)}
    {G₂ : ∀ (k : Fin K) (j : V₂), Finset (Guard k j)}
    (p₁ : Presents name₁ entries G₁) (p₂ : Presents name₂ entries G₂) (σ : V₂ → V₁)
    (hσ : ∀ j, name₁ (σ j) = name₂ j) (hsurj : Function.Surjective σ)
    (v : V₁ → WinnerSet (Fin K)) : meaning G₂ (fun j => v (σ j)) = meaning G₁ v := by
  ext k
  constructor
  · rintro ⟨j₂, hk, g₂, hg₂, hen⟩
    obtain ⟨g₁, hg₁, hsub⟩ := exists_guard_of_presents h₁ p₂ p₁ hg₂ (hσ j₂)
    refine ⟨σ j₂, hk, g₁, hg₁, fun b hb hpb => ?_⟩
    obtain ⟨a, ha, h1, h2⟩ := hsub b hb
    have e : σ a.1.val = b.1.val := h₁ ((hσ _).trans h1)
    refine hen a ha ?_
    change passive k (v (σ a.1.val)) = .atom a.2
    rw [e, show a.2 = b.2 from Subtype.ext h2]
    exact hpb
  · rintro ⟨j₁, hk, g₁, hg₁, hen⟩
    obtain ⟨j₂, rfl⟩ := hsurj j₁
    obtain ⟨g₂, hg₂, hsub⟩ := exists_guard_of_presents h₂ p₁ p₂ hg₁ (hσ j₂).symm
    refine ⟨j₂, hk, g₂, hg₂, fun b hb hpb => ?_⟩
    obtain ⟨a, ha, h1, h2⟩ := hsub b hb
    have e : a.1.val = σ b.1.val := h₁ (h1.trans (hσ _).symm)
    refine hen a ha ?_
    change passive k (v a.1.val) = .atom a.2
    rw [e, show a.2 = b.2 from Subtype.ext h2]
    exact hpb

end Presents

end KFOL.Recognition.Lists
