module

public import KFOL.Core.PruningSubstitution

/-! # Extracting a block of inputs and projecting pruning supports -/

@[expose] public section
namespace KFOL.Core.PruningModules

open ProfileBudgets CompulsoryPruning
variable {Role V U : Type*} [DecidableEq Role] [DecidableEq V]

omit [DecidableEq Role] in
private theorem vars_choice (q : Role) (x y : CoreTerm Role V) :
    (choiceTerm q x y).varFinset = x.varFinset ∪ y.varFinset := by
  simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2]

private theorem exists_support (r : Role) (t : CoreTerm Role V) :
    ∃ H ∈ Supports r t, H ⊆ t.varFinset := by
  induction t using induction_choice with
  | var x => exact ⟨{x}, rfl, Finset.Subset.rfl⟩
  | choice q x y hx hy =>
    obtain ⟨A, ha, sub⟩ := hx
    rw [vars_choice]
    by_cases qr : q = r
    · subst q
      obtain ⟨B, hb, sub'⟩ := hy
      exact ⟨A ∪ B, owned.mpr ⟨_, ha, _, hb, rfl⟩, Finset.union_subset_union sub sub'⟩
    · exact ⟨A, (foreign qr).mpr (Or.inl ha), sub.trans Finset.subset_union_left⟩

/-- Keep the leaves in the block and contract every gate with only one
remaining child. An empty result records that the subtree misses the block. -/
def extract (B : Finset V) : CoreTerm Role V → Option (CoreTerm Role V)
  | .var x => if x ∈ B then some (.var x) else none
  | .func (.choice q) f =>
    match extract B (f 0), extract B (f 1) with
    | some x, some y => some (choiceTerm q x y)
    | some x, none => some x
    | none, y => y

/-- Exact syntactic support and lifting of every pruning of the extracted word. -/
structure Restricts (B : Finset V) (t u : CoreTerm Role V) : Prop where
  vars : u.varFinset = t.varFinset ∩ B
  lifts : ∀ r H, H ∈ Supports r u → ∃ A ∈ Supports r t, A ∩ B = H

private theorem Restricts.choice {B : Finset V} {x y u v : CoreTerm Role V}
    (l : Restricts B x u) (h : Restricts B y v) (q : Role) :
    Restricts B (choiceTerm q x y) (choiceTerm q u v) where
  vars := by rw [vars_choice, vars_choice, l.vars, h.vars, Finset.union_inter_distrib_right]
  lifts := by
    intro r H hH
    by_cases qr : q = r
    · subst q
      obtain ⟨A, ha, D, hd, rfl⟩ := owned.mp hH
      obtain ⟨X, hx, rfl⟩ := l.lifts r A ha
      obtain ⟨Y, hy, rfl⟩ := h.lifts r D hd
      exact ⟨X ∪ Y, owned.mpr ⟨_, hx, _, hy, rfl⟩, Finset.union_inter_distrib_right _ _ _⟩
    · rcases (foreign qr).mp hH with hu | hv
      · obtain ⟨X, hx, e⟩ := l.lifts r H hu
        exact ⟨X, (foreign qr).mpr (Or.inl hx), e⟩
      · obtain ⟨Y, hy, e⟩ := h.lifts r H hv
        exact ⟨Y, (foreign qr).mpr (Or.inr hy), e⟩

private theorem Restricts.drop_right {B : Finset V} {x y u : CoreTerm Role V}
    (l : Restricts B x u) (empty : y.varFinset ∩ B = ∅) (q : Role) :
    Restricts B (choiceTerm q x y) u where
  vars := by rw [l.vars, vars_choice, Finset.union_inter_distrib_right, empty, Finset.union_empty]
  lifts := by
    intro r H hu
    obtain ⟨A, ha, rfl⟩ := l.lifts r H hu
    by_cases qr : q = r
    · subst q
      obtain ⟨D, hd, sub⟩ := exists_support r y
      have miss : D ∩ B = ∅ := Finset.subset_empty.mp
        (empty ▸ Finset.inter_subset_inter_right sub : D ∩ B ⊆ ∅)
      exact ⟨A ∪ D, owned.mpr ⟨A, ha, D, hd, rfl⟩,
        by rw [Finset.union_inter_distrib_right, miss, Finset.union_empty]⟩
    · exact ⟨A, (foreign qr).mpr (Or.inl ha), rfl⟩

private theorem Restricts.swap {B : Finset V} {x y u : CoreTerm Role V} {q : Role}
    (h : Restricts B (choiceTerm q x y) u) : Restricts B (choiceTerm q y x) u where
  vars := by rw [h.vars, vars_choice, vars_choice, Finset.union_comm]
  lifts := by
    intro r H hH
    obtain ⟨A, ha, eq⟩ := h.lifts r H hH
    refine ⟨A, ?_, eq⟩
    by_cases qr : q = r
    · subst q
      obtain ⟨X, hx, Y, hy, rfl⟩ := owned.mp ha
      exact owned.mpr ⟨Y, hy, X, hx, Finset.union_comm _ _⟩
    · exact (foreign qr).mpr ((foreign qr).mp ha).symm

/-- The extraction is simultaneous in the owners: one word lifts every
one of its pruning supports to an original support with that intersection. -/
theorem extract_spec (B : Finset V) (t : CoreTerm Role V) :
    match extract B t with
    | none => t.varFinset ∩ B = ∅
    | some u => Restricts B t u := by
  induction t using induction_choice with
  | var x =>
    by_cases hit : x ∈ B
    · simp only [extract, ite_eq_left hit]
      refine ⟨?_, ?_⟩
      · simp [FirstOrder.Language.Term.varFinset, hit]
      · intro r H hs
        obtain rfl := (supports_var r x H).mp hs
        exact ⟨_, rfl, by simp [hit]⟩
    · simp [extract, hit, FirstOrder.Language.Term.varFinset]
  | choice q x y hx hy =>
    simp only [choiceTerm, extract, ite_true, ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
    cases ex : extract B x with
    | none =>
      rw [ex] at hx
      cases ey : extract B y with
      | none =>
        rw [ey] at hy
        change (choiceTerm q x y).varFinset ∩ B = ∅
        rw [vars_choice, Finset.union_inter_distrib_right, hx, hy, Finset.empty_union]
      | some v =>
        rw [ey] at hy
        exact (Restricts.drop_right hy hx q).swap
    | some u =>
      rw [ex] at hx
      cases ey : extract B y with
      | none =>
        rw [ey] at hy
        exact Restricts.drop_right hx hy q
      | some v =>
        rw [ey] at hy
        exact Restricts.choice hx hy q

theorem exists_restriction (B : Finset V) (t : CoreTerm Role V) (uses : (t.varFinset ∩ B).Nonempty) :
    ∃ u, extract B t = some u ∧ Restricts B t u := by
  have spec := extract_spec B t
  cases eq : extract B t with
  | none => rw [eq] at spec; exact (uses.ne_empty spec).elim
  | some u => rw [eq] at spec; exact ⟨u, rfl, spec⟩

omit [DecidableEq Role] [DecidableEq V] in
private theorem relabel_choice (f : V → U) (q : Role) (x y : CoreTerm Role V) :
    (choiceTerm q x y).relabel f = choiceTerm q (x.relabel f) (y.relabel f) := by
  unfold choiceTerm
  rw [FirstOrder.Language.Term.relabel]
  congr 1
  funext i
  by_cases e : i = 0 <;> simp [e]

/-- All labels can be identified by an arbitrary map. At each owner the
pruning supports are exactly the images of the original supports. -/
theorem supports_relabel [DecidableEq U] (f : V → U) (r : Role)
    (t : CoreTerm Role V) (H : Finset U) :
    H ∈ Supports r (t.relabel f) ↔ ∃ A ∈ Supports r t, A.image f = H := by
  induction t using induction_choice generalizing H with
  | var x =>
    change H = {f x} ↔ ∃ A : Finset V, A = {x} ∧ A.image f = H
    simp [eq_comm]
  | choice q x y hx hy =>
    rw [relabel_choice]
    by_cases qr : q = r
    · subst q
      constructor
      · intro hh
        obtain ⟨X, ex, Y, ey, rfl⟩ := owned.mp hh
        obtain ⟨A, ha, rfl⟩ := (hx X).mp ex
        obtain ⟨B, hb, rfl⟩ := (hy Y).mp ey
        exact ⟨A ∪ B, owned.mpr ⟨_, ha, _, hb, rfl⟩, Finset.image_union _ _⟩
      · rintro ⟨A, ha, rfl⟩
        obtain ⟨X, ex, Y, ey, rfl⟩ := owned.mp ha
        exact owned.mpr ⟨_, (hx _).mpr ⟨_, ex, rfl⟩, _, (hy _).mpr ⟨_, ey, rfl⟩,
          (Finset.image_union _ _).symm⟩
    · rw [foreign qr, hx H, hy H]
      constructor
      · rintro (⟨A, ha, eq⟩ | ⟨A, ha, eq⟩)
        · exact ⟨A, (foreign qr).mpr (Or.inl ha), eq⟩
        · exact ⟨A, (foreign qr).mpr (Or.inr ha), eq⟩
      · rintro ⟨A, ha, eq⟩
        exact ((foreign qr).mp ha).imp (fun h => ⟨A, h, eq⟩) (fun h => ⟨A, h, eq⟩)

/-- A block actually used by a feasible word inherits feasibility of the
families of intersections with that block. -/
theorem feasibleOn_block (F : Role → Finset V → Prop) (B : Finset V) (t : CoreTerm Role V)
    (uses : (t.varFinset ∩ B).Nonempty) (safe : ∀ r H, H ∈ Supports r t → F r H) :
    FeasibleOn (B : Set V) (fun r H => ∃ A, F r A ∧ A ∩ B = H) := by
  obtain ⟨u, _, res⟩ := exists_restriction B t uses
  refine ⟨u, ?_, ?_⟩
  · rw [res.vars]
    exact Finset.inter_subset_right
  · intro r H hH
    obtain ⟨A, ha, eq⟩ := res.lifts r H hH
    exact ⟨A, safe r A ha, eq⟩

omit [DecidableEq Role] in
theorem vars_relabel [DecidableEq U] (f : V → U) (t : CoreTerm Role V) :
    (t.relabel f).varFinset = t.varFinset.image f := by
  induction t using induction_choice with
  | var i => simp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.varFinset]
  | choice q x y hx hy => rw [relabel_choice, vars_choice, vars_choice, Finset.image_union, hx, hy]

theorem feasibleOn_image [DecidableEq U] (f : V → U) (W : Set V)
    (F : Role → Finset V → Prop) (feasible : FeasibleOn W F) :
    FeasibleOn (f '' W) (fun r H => ∃ A, F r A ∧ A.image f = H) := by
  obtain ⟨t, vars, safe⟩ := feasible
  refine ⟨t.relabel f, ?_, ?_⟩
  · rw [vars_relabel, Finset.coe_image]
    exact Set.image_mono vars
  · intro r H hs
    obtain ⟨A, ha, eq⟩ := (supports_relabel f r t H).mp hs
    exact ⟨A, safe r A ha, eq⟩

/-- When legality factors into the active blocks and the individual slices,
pruning feasibility factors through precisely the realizable blocks. -/
theorem feasibleOn_fibers_iff [DecidableEq U] (π : V → U) (W : Set V)
    (outer : Role → Finset U → Prop) (inner : U → Role → Finset V → Prop)
    (closed : ∀ b r A C, A.Nonempty → C.Nonempty →
      inner b r A → inner b r C → inner b r (A ∪ C)) :
    FeasibleOn W (fun r H =>
      outer r (H.image π) ∧ ∀ b ∈ H.image π, inner b r (H.filter (fun x => π x = b))) ↔
    FeasibleOn {b | FeasibleOn {x | x ∈ W ∧ π x = b} (inner b)} outer := by
  refine ⟨?_, feasibleOn_substitution π W outer inner closed⟩
  rintro ⟨t, available, safe⟩
  refine ⟨t.relabel π, ?_, ?_⟩
  · rw [vars_relabel]
    intro b hb
    obtain ⟨x, hx, xb⟩ := Finset.mem_image.mp hb
    let block := t.varFinset.filter (fun x => π x = b)
    have uses : (t.varFinset ∩ block).Nonempty :=
      ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_filter.mpr ⟨hx, xb⟩⟩⟩
    obtain ⟨child, _, res⟩ := exists_restriction block t uses
    refine ⟨child, ?_, ?_⟩
    · rw [res.vars]
      intro i hi
      obtain ⟨iv, ib⟩ := Finset.mem_inter.mp hi
      exact ⟨available iv, (Finset.mem_filter.mp ib).2⟩
    · intro r H hs
      obtain ⟨A, ha, eq⟩ := res.lifts r H hs
      have filter_eq : A.filter (fun i => π i = b) = H := by
        rw [← eq]
        ext i
        simp only [Finset.mem_filter, Finset.mem_inter, block]
        exact ⟨fun h => ⟨h.1, support_subset_variables r t ha h.1, h.2⟩,
          fun h => ⟨h.1, h.2.2⟩⟩
      obtain ⟨i, hi⟩ := support_nonempty r child hs
      rw [← filter_eq] at hi
      obtain ⟨ia, ib⟩ := Finset.mem_filter.mp hi
      exact filter_eq ▸ (safe r A ha).2 b (Finset.mem_image.mpr ⟨i, ia, ib⟩)
  · intro r H hs
    obtain ⟨A, ha, eq⟩ := (supports_relabel π r t H).mp hs
    exact eq ▸ (safe r A ha).1

end KFOL.Core.PruningModules
