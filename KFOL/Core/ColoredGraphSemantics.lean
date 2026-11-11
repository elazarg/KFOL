module

public import KFOL.Definitions.CoreGraph
public import KFOL.Algebra.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Preorder.Finite

/-! # Clique semantics across monochromatic cuts

Maximal owner cliques give the atomic blocking test and the possible winners.
A monochromatic cut turns these graph predicates into the owned-choice laws.
-/

@[expose] public section

namespace KFOL.Core.ColoredGraph

universe u v w
variable {Role : Type u} {Vertex : Type v} {Var : Type w}
variable {G : Graph Role Vertex} {A L R D : Set Vertex} {r q : Role}

private theorem maxClique_iff :
    G.MaxClique A r D ↔ D ⊆ A ∧ (G.component r).IsClique D ∧
      ∀ x ∈ A, (∀ y ∈ D, x ≠ y → G.color x y = r) → x ∈ D := by
  constructor
  · rintro ⟨⟨hDA, hD⟩, hmax⟩
    refine ⟨hDA, hD, ?_⟩
    intro x hx hadj
    have hcl : (G.component r).IsClique (insert x D) := hD.insert fun y hy hxy =>
      ⟨hxy, hadj y hy hxy⟩
    exact hmax ⟨Set.insert_subset hx hDA, hcl⟩ (Set.subset_insert x D) (by simp)
  · rintro ⟨hDA, hD, hmax⟩
    refine ⟨⟨hDA, hD⟩, ?_⟩
    intro C hC hDC x hx
    exact hmax x (hC.1 hx) fun y hy hxy => (hC.2 hx (hDC hy) hxy).2

/-- Every monochromatic clique extends to a maximal clique in a finite region. -/
theorem exists_maxClique [Finite Vertex] (hDA : D ⊆ A)
    (hD : (G.component r).IsClique D) :
    ∃ C, D ⊆ C ∧ G.MaxClique A r C := by
  obtain ⟨C, hDC, hC⟩ := Finite.exists_le_maximal
    (p := fun C : Set Vertex => C ⊆ A ∧ (G.component r).IsClique C) ⟨hDA, hD⟩
  exact ⟨C, hDC, hC⟩

/-- A maximal clique in a nonempty region contains a vertex. -/
theorem maxClique_nonempty (hA : A.Nonempty) (hD : G.MaxClique A r D) : D.Nonempty := by
  by_contra h
  have he : D = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  obtain ⟨x, hx⟩ := hA
  have hxD := (maxClique_iff.mp hD).2.2 x hx (by simp [he])
  simp [he] at hxD

private theorem cut_left (h : G.Cut A r L R) : L ⊆ A := by
  rw [← h.2.2.2.1]
  exact Set.subset_union_left

private theorem cut_right (h : G.Cut A r L R) : R ⊆ A := by
  rw [← h.2.2.2.1]
  exact Set.subset_union_right

private theorem cut_swap (h : G.Cut A r L R) : G.Cut A r R L := by
  refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_, ?_⟩
  · simpa [Set.union_comm] using h.2.2.2.1
  · intro x hx y hy
    exact (G.symm x y).trans (h.2.2.2.2 y hy x hx)

private theorem cut_ne (h : G.Cut A r L R) {x y : Vertex} (hx : x ∈ L) (hy : y ∈ R) :
    x ≠ y := by
  intro he
  exact Set.disjoint_left.mp h.2.2.1 hx (he ▸ hy)

/-- On its cut owner's color, a maximal clique is a union of maximal cliques
from the two regions. -/
theorem maxClique_cut_owner (h : G.Cut A r L R) :
    G.MaxClique A r D ↔ ∃ E F, G.MaxClique L r E ∧ G.MaxClique R r F ∧ D = E ∪ F := by
  constructor
  · intro hD
    have hd := maxClique_iff.mp hD
    have part : D = (D ∩ L) ∪ (D ∩ R) := by
      ext x
      constructor
      · intro hx
        have hm : x ∈ L ∪ R := h.2.2.2.1 ▸ hd.1 hx
        exact hm.elim (fun hl => Or.inl ⟨hx, hl⟩) (fun hr => Or.inr ⟨hx, hr⟩)
      · rintro (hx | hx) <;> exact hx.1
    have side (L R : Set Vertex) (hc : G.Cut A r L R) :
        G.MaxClique L r (D ∩ L) := by
      refine maxClique_iff.mpr ⟨Set.inter_subset_right, hd.2.1.inter_left L, ?_⟩
      intro x hx ha
      refine ⟨hd.2.2 x (cut_left hc hx) ?_, hx⟩
      intro y hy hxy
      have hm : y ∈ L ∪ R := hc.2.2.2.1 ▸ hd.1 hy
      rcases hm with hl | hr
      · exact ha y ⟨hy, hl⟩ hxy
      · exact hc.2.2.2.2 x hx y hr
    exact ⟨D ∩ L, D ∩ R, side L R h, side R L (cut_swap h), part⟩
  · rintro ⟨E, F, hE, hF, rfl⟩
    have he := maxClique_iff.mp hE
    have hf := maxClique_iff.mp hF
    refine maxClique_iff.mpr ⟨Set.union_subset (he.1.trans (cut_left h))
      (hf.1.trans (cut_right h)), ?_, ?_⟩
    · intro x hx y hy hxy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact he.2.1 hx hy hxy
      · exact ⟨hxy, h.2.2.2.2 x (he.1 hx) y (hf.1 hy)⟩
      · exact ⟨hxy, (G.symm x y).trans (h.2.2.2.2 y (he.1 hy) x (hf.1 hx))⟩
      · exact hf.2.1 hx hy hxy
    · intro x hx hadj
      have hm : x ∈ L ∪ R := h.2.2.2.1 ▸ hx
      rcases hm with hl | hr
      · exact Or.inl (he.2.2 x hl fun y hy hxy => hadj y (Or.inl hy) hxy)
      · exact Or.inr (hf.2.2 x hr fun y hy hxy => hadj y (Or.inr hy) hxy)

/-- On any other color, maximal cliques lie in exactly one side of the cut. -/
theorem maxClique_cut_other (h : G.Cut A r L R) (hqr : q ≠ r) :
    G.MaxClique A q D ↔ G.MaxClique L q D ∨ G.MaxClique R q D := by
  have restrict (S : Set Vertex) (hSA : S ⊆ A) (hD : G.MaxClique A q D)
      (hDS : D ⊆ S) : G.MaxClique S q D := by
    obtain ⟨hDA, hcl, hmax⟩ := maxClique_iff.mp hD
    exact maxClique_iff.mpr ⟨hDS, hcl, fun x hx ha => hmax x (hSA hx) ha⟩
  have lift (L R : Set Vertex) (hc : G.Cut A r L R) (hD : G.MaxClique L q D) :
      G.MaxClique A q D := by
    obtain ⟨hDL, hcl, hmax⟩ := maxClique_iff.mp hD
    obtain ⟨y, hy⟩ := maxClique_nonempty hc.1 hD
    refine maxClique_iff.mpr ⟨hDL.trans (cut_left hc), hcl, ?_⟩
    intro x hx ha
    have hm : x ∈ L ∪ R := hc.2.2.2.1 ▸ hx
    rcases hm with hl | hr
    · exact hmax x hl ha
    · have hxy : x ≠ y := (cut_ne hc (hDL hy) hr).symm
      exact (hqr ((ha y hy hxy).symm.trans
        ((G.symm x y).trans (hc.2.2.2.2 y (hDL hy) x hr)))).elim
  constructor
  · intro hD
    have ha : A.Nonempty := h.1.mono (cut_left h)
    obtain ⟨x, hx⟩ := maxClique_nonempty ha hD
    have hd := maxClique_iff.mp hD
    have hm : x ∈ L ∪ R := h.2.2.2.1 ▸ hd.1 hx
    have side (L R : Set Vertex) (hc : G.Cut A r L R) (hxl : x ∈ L) : D ⊆ L := by
      intro y hy
      have hm : y ∈ L ∪ R := hc.2.2.2.1 ▸ hd.1 hy
      rcases hm with hl | hr
      · exact hl
      · have he := (hd.2.1 hx hy (cut_ne hc hxl hr)).2
        exact (hqr (he.symm.trans (hc.2.2.2.2 x hxl y hr))).elim
    rcases hm with hl | hr
    · exact Or.inl (restrict L (cut_left h) hD (side L R h hl))
    · exact Or.inr (restrict R (cut_right h) hD (side R L (cut_swap h) hr))
  · exact fun hD => hD.elim (lift L R h) (lift R L (cut_swap h))

@[simp] theorem maxClique_singleton (x : Vertex) :
    G.MaxClique {x} r D ↔ D = {x} := by
  constructor
  · intro hD
    have hd := maxClique_iff.mp hD
    apply Set.Subset.antisymm hd.1
    apply Set.singleton_subset_iff.mpr
    exact hd.2.2 x (by simp) fun y hy hxy =>
      (hxy (Set.mem_singleton_iff.mp (hd.1 hy)).symm).elim
  · rintro rfl
    exact ⟨⟨Set.Subset.rfl, (G.component r).isClique_singleton x⟩,
      fun _ h _ => h.1⟩

@[simp] theorem blocks_singleton (x : Vertex) (label : Vertex → Var)
    (v : Var → WinnerSet Role) :
    G.Blocks {x} label v r ↔ v (label x) = WinnerSet.singleton r := by
  simp [Graph.Blocks]

@[simp] theorem wins_singleton (x : Vertex) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (k : Role) :
    G.Wins {x} label v k ↔ k ∈ (v (label x)).val := by
  simp [Graph.Wins]

/-- Failure of blocking supplies one maximal clique avoiding the owner's atom. -/
theorem not_blocks_iff (label : Vertex → Var) (v : Var → WinnerSet Role) :
    ¬G.Blocks A label v r ↔
      ∃ D, G.MaxClique A r D ∧ ∀ x ∈ D, v (label x) ≠ WinnerSet.singleton r := by
  classical
  simp [Graph.Blocks, not_forall, not_exists, not_and]

/-- The owner's own color gives disjunctive blocking across a cut. -/
theorem blocks_cut_owner (h : G.Cut A r L R)
    (label : Vertex → Var) (v : Var → WinnerSet Role) :
    G.Blocks A label v r ↔ G.Blocks L label v r ∨ G.Blocks R label v r := by
  classical
  constructor
  · intro hb
    by_contra hn
    obtain ⟨E, hE, he⟩ := (not_blocks_iff label v).mp (not_or.mp hn).1
    obtain ⟨F, hF, hf⟩ := (not_blocks_iff label v).mp (not_or.mp hn).2
    have hEF : G.MaxClique A r (E ∪ F) :=
      (maxClique_cut_owner h).mpr ⟨E, F, hE, hF, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hb _ hEF
    exact hx.elim (fun hx => he x hx hxa) (fun hx => hf x hx hxa)
  · intro hb D hD
    obtain ⟨E, F, hE, hF, rfl⟩ := (maxClique_cut_owner h).mp hD
    rcases hb with hl | hr
    · obtain ⟨x, hx, ha⟩ := hl E hE
      exact ⟨x, Or.inl hx, ha⟩
    · obtain ⟨x, hx, ha⟩ := hr F hF
      exact ⟨x, Or.inr hx, ha⟩

/-- Other colors give conjunctive blocking across a cut. -/
theorem blocks_cut_other (h : G.Cut A r L R) (hqr : q ≠ r)
    (label : Vertex → Var) (v : Var → WinnerSet Role) :
    G.Blocks A label v q ↔ G.Blocks L label v q ∧ G.Blocks R label v q := by
  constructor
  · intro hb
    exact ⟨fun D hd => hb D ((maxClique_cut_other h hqr).mpr (Or.inl hd)),
      fun D hd => hb D ((maxClique_cut_other h hqr).mpr (Or.inr hd))⟩
  · rintro ⟨hl, hr⟩ D hd
    exact ((maxClique_cut_other h hqr).mp hd).elim (hl D) (hr D)

private def SafeAt (G : Graph Role Vertex) (A : Set Vertex) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (q : Role) (x : Vertex) : Prop :=
  ∃ D, G.MaxClique A q D ∧ x ∈ D ∧
    ∀ y ∈ D, y ≠ x → v (label y) ≠ WinnerSet.singleton q

private theorem safeAt_cut_owner_left (h : G.Cut A r L R) (x : Vertex) (hx : x ∈ L)
    (label : Vertex → Var) (v : Var → WinnerSet Role) :
    SafeAt G A label v r x ↔ SafeAt G L label v r x ∧ ¬G.Blocks R label v r := by
  constructor
  · rintro ⟨D, hd, hxd, hs⟩
    obtain ⟨E, F, he, hf, rfl⟩ := (maxClique_cut_owner h).mp hd
    have hxe : x ∈ E := hxd.elim id (fun hxf =>
      (Set.disjoint_left.mp h.2.2.1 hx (hf.1.1 hxf)).elim)
    refine ⟨⟨E, he, hxe, fun y hy hne => hs y (Or.inl hy) hne⟩, ?_⟩
    apply (not_blocks_iff label v).mpr
    refine ⟨F, hf, ?_⟩
    intro y hy
    exact hs y (Or.inr hy) (cut_ne h hx (hf.1.1 hy)).symm
  · rintro ⟨⟨E, he, hxe, hs⟩, hn⟩
    obtain ⟨F, hf, hsF⟩ := (not_blocks_iff label v).mp hn
    refine ⟨E ∪ F, (maxClique_cut_owner h).mpr ⟨E, F, he, hf, rfl⟩,
      Or.inl hxe, ?_⟩
    intro y hy hne
    exact hy.elim (fun hy => hs y hy hne) (fun hy => hsF y hy)

private theorem safeAt_cut_other_left (h : G.Cut A r L R) (hqr : q ≠ r)
    (x : Vertex) (hx : x ∈ L) (label : Vertex → Var) (v : Var → WinnerSet Role) :
    SafeAt G A label v q x ↔ SafeAt G L label v q x := by
  constructor
  · rintro ⟨D, hd, hxd, hs⟩
    rcases (maxClique_cut_other h hqr).mp hd with hl | hr
    · exact ⟨D, hl, hxd, hs⟩
    · exact (Set.disjoint_left.mp h.2.2.1 hx (hr.1.1 hxd)).elim
  · rintro ⟨D, hd, hxd, hs⟩
    exact ⟨D, (maxClique_cut_other h hqr).mpr (Or.inl hd), hxd, hs⟩

private theorem safeAt_cut_left (h : G.Cut A r L R)
    (x : Vertex) (hx : x ∈ L) (label : Vertex → Var) (v : Var → WinnerSet Role) :
    SafeAt G A label v q x ↔
      SafeAt G L label v q x ∧ (q = r → ¬G.Blocks R label v r) := by
  classical
  by_cases he : q = r
  · subst q
    simpa using safeAt_cut_owner_left h x hx label v
  · simp [safeAt_cut_other_left h he x hx label v, he]

/-- A source survives a cut precisely when it survives in its own region and
its sibling does not force the cut owner's distinct singleton. -/
theorem wins_cut (h : G.Cut A r L R) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (k : Role) :
    G.Wins A label v k ↔
      (G.Wins L label v k ∧ (r = k ∨ ¬G.Blocks R label v r)) ∨
      (G.Wins R label v k ∧ (r = k ∨ ¬G.Blocks L label v r)) := by
  classical
  have left (L R : Set Vertex) (hc : G.Cut A r L R) (x : Vertex) (hx : x ∈ L) :
      (∀ q, q ≠ k → SafeAt G A label v q x) ↔
        (∀ q, q ≠ k → SafeAt G L label v q x) ∧
          (r = k ∨ ¬G.Blocks R label v r) := by
    constructor
    · intro hs
      refine ⟨fun q hq => ((safeAt_cut_left hc x hx label v).mp (hs q hq)).1, ?_⟩
      by_cases hrk : r = k
      · exact Or.inl hrk
      · exact Or.inr (((safeAt_cut_left hc x hx label v).mp (hs r hrk)).2 rfl)
    · rintro ⟨hs, hr⟩ q hq
      apply (safeAt_cut_left hc x hx label v).mpr
      refine ⟨hs q hq, ?_⟩
      intro hqr
      rcases hr with hrk | hb
      · exact (hq (hqr.trans hrk)).elim
      · exact hb
  constructor
  · rintro ⟨x, hx, hk, hs⟩
    have hm : x ∈ L ∪ R := h.2.2.2.1 ▸ hx
    rcases hm with hl | hr
    · obtain ⟨hsl, hb⟩ := (left L R h x hl).mp hs
      exact Or.inl ⟨⟨x, hl, hk, hsl⟩, hb⟩
    · obtain ⟨hsr, hb⟩ := (left R L (cut_swap h) x hr).mp hs
      exact Or.inr ⟨⟨x, hr, hk, hsr⟩, hb⟩
  · rintro (⟨⟨x, hx, hk, hs⟩, hb⟩ | ⟨⟨x, hx, hk, hs⟩, hb⟩)
    · exact ⟨x, cut_left h hx, hk, (left L R h x hx).mpr ⟨hs, hb⟩⟩
    · exact ⟨x, cut_right h hx, hk, (left R L (cut_swap h) x hx).mpr ⟨hs, hb⟩⟩

/-- Clique blocking obeys the singleton-output recursion of owned choice. -/
theorem blocks_cut [DecidableEq Role] (h : G.Cut A r L R) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (q : Role) :
    G.Blocks A label v q ↔
      if r = q then G.Blocks L label v q ∨ G.Blocks R label v q
      else G.Blocks L label v q ∧ G.Blocks R label v q := by
  classical
  by_cases he : r = q
  · subst q
    simpa using blocks_cut_owner h label v
  · simpa [he] using blocks_cut_other h (Ne.symm he) label v

/-- Substituting the child blocking and winner meanings into the graph cut
recurrence gives precisely the winner-set owned choice. -/
theorem wins_cut_choice (h : G.Cut A r L R) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (S T : WinnerSet Role)
    (hSL : ∀ k, G.Wins L label v k ↔ k ∈ S.val)
    (hTR : ∀ k, G.Wins R label v k ↔ k ∈ T.val)
    (hBL : G.Blocks L label v r ↔ S = WinnerSet.singleton r)
    (hBR : G.Blocks R label v r ↔ T = WinnerSet.singleton r) (k : Role) :
    G.Wins A label v k ↔ k ∈ (WinnerSet.choice r S T).val := by
  classical
  rw [wins_cut h, hSL k, hTR k, hBL, hBR]
  by_cases hs : S = WinnerSet.singleton r
  · subst S
    by_cases hk : r = k <;> simp [WinnerSet.choice, hk, eq_comm]
  · by_cases ht : T = WinnerSet.singleton r
    · subst T
      by_cases hk : r = k <;> simp [WinnerSet.choice, hk, eq_comm]
    · simp [WinnerSet.choice, hs, ht]

/-- Clique blocking agrees with the singleton output of owned choice once it
has that meaning on the child regions. -/
theorem blocks_cut_choice (h : G.Cut A r L R) (label : Vertex → Var)
    (v : Var → WinnerSet Role) (S T : WinnerSet Role)
    (hBL : ∀ q, G.Blocks L label v q ↔ S = WinnerSet.singleton q)
    (hBR : ∀ q, G.Blocks R label v q ↔ T = WinnerSet.singleton q) (q : Role) :
    G.Blocks A label v q ↔ WinnerSet.choice r S T = WinnerSet.singleton q := by
  classical
  by_cases he : r = q
  · subst q
    rw [blocks_cut_owner h, hBL r, hBR r, WinnerSet.choice_eq_owner_iff]
  · rw [blocks_cut_other h (Ne.symm he), hBL q, hBR q,
      WinnerSet.choice_eq_other_iff S T r he]

end KFOL.Core.ColoredGraph
