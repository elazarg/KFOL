module

public import KFOL.Reset.Basis.NormalForm

/-! # Suffix coverage of path constituents -/

@[expose] public section

namespace KFOL.Reset

universe u v

/-- A word selects a position if all variables after an occurrence are ambiguous. -/
def WordSelected {Var : Type v} : List Var → Set Var → Var → Prop
  | [], _, _ => False
  | x :: xs, B, j => (j = x ∧ ∀ i ∈ xs, i ∈ B) ∨ WordSelected xs B j

theorem wordSelected_iff {Var : Type v} (xs : List Var) (B : Set Var) (j : Var) :
    WordSelected xs B j ↔
      ∃ before after, xs = before ++ j :: after ∧ ∀ i ∈ after, i ∈ B := by
  induction xs with
  | nil => simp [WordSelected]
  | cons x xs ih =>
    constructor
    · rintro (⟨rfl, ha⟩ | ha)
      · exact ⟨[], xs, rfl, ha⟩
      · obtain ⟨before, after, he, ha⟩ := ih.mp ha
        exact ⟨x :: before, after, congrArg (List.cons x) he, ha⟩
    · rintro ⟨before, after, he, ha⟩
      cases before with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact Or.inl ⟨rfl, ha⟩
      | cons y before =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, he⟩ := he
        exact Or.inr (ih.mpr ⟨before, after, he, ha⟩)

theorem wordSelected_append {Var : Type v} (xs : List Var) (r : Var) (B : Set Var) (j : Var) :
    WordSelected (xs ++ [r]) B j ↔ j = r ∨ (r ∈ B ∧ WordSelected xs B j) := by
  induction xs with
  | nil => simp [WordSelected]
  | cons x xs ih =>
    simp only [List.cons_append, WordSelected, List.forall_mem_append,
      List.forall_mem_singleton, ih]
    tauto

namespace Term

theorem selected_iff_paths {Var : Type v} (t : Term Var) (B : Set Var) (j : Var) :
    t.Selected B j ↔ ∃ p ∈ t.paths, WordSelected (p ++ [t.root]) B j := by
  induction t using induction_reset with
  | var i => simp [Selected, paths, WordSelected]
  | step s t hs ht =>
    rw [selected_step, paths_step, root_step]
    constructor
    · rintro (hj | ⟨hr, hj⟩)
      · obtain ⟨p, hp, hj⟩ := ht.mp hj
        exact ⟨p, List.mem_append_right _ hp, hj⟩
      · obtain ⟨p, hp, hj⟩ := hs.mp hj
        refine ⟨p ++ [s.root], List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩), ?_⟩
        exact (wordSelected_append _ _ _ _).mpr (Or.inr ⟨hr, hj⟩)
    · rintro ⟨p, hp, hj⟩
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        rcases (wordSelected_append _ _ _ _).mp hj with he | ⟨hr, hj⟩
        · subst j
          exact Or.inl (t.selected_root B)
        · exact Or.inr ⟨hr, hs.mpr ⟨q, hq, hj⟩⟩
      · exact Or.inl (ht.mpr ⟨p, hp, hj⟩)

end Term

namespace Laws

variable {M : Type u} {op : M → M → M} (h : Laws op)
local infixl:70 " ⋄ " => op
local infix:50 " ≼ " => Below (op := op)
include h

/-- Selector coverage absorbs a target path in every six-law algebra. -/
theorem path_absorption {Var : Type v} (v : Var → M) (r : Var) (P : List (List Var))
    (target : List Var)
    (cover : ∀ (B : Set Var) j, WordSelected (target ++ [r]) B j →
      ∃ p ∈ P, WordSelected (p ++ [r]) B j) :
    (P.map (fun p => path op (v r) (p.map v))).foldr op (v r) ≼
      path op (v r) (target.map v) := by
  let a := (P.map (fun p => path op (v r) (p.map v))).foldr op (v r)
  have hfixed : a ⋄ v r = a := h.foldr_fixed _ _ (by
    rintro b hb
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hb
    exact h.path_fixed _ _)
  induction target with
  | nil => exact hfixed
  | cons x xs ih =>
    have htail : a ≼ path op (v r) (xs.map v) := ih (fun B j hj => cover B j (Or.inr hj))
    by_cases hxr : x = r
    · subst x
      simpa only [List.map_cons, h.path_initial_root] using htail
    · let B : Set Var := {j | j ∈ xs ++ [r]}
      obtain ⟨p, hp, hj⟩ := cover B x (Or.inl ⟨rfl, fun _ hi => hi⟩)
      obtain ⟨_, hj⟩ := (wordSelected_append p r B x).mp hj |>.resolve_left hxr
      obtain ⟨before, after, he, ha⟩ := (wordSelected_iff p B x).mp hj
      have hpa : a ≼ path op (v r) (p.map v) := h.foldr_below_mem _ _ (by
        rintro b hb
        obtain ⟨q, _, rfl⟩ := List.mem_map.mp hb
        exact h.path_fixed _ _) (List.mem_map.mpr ⟨p, hp, rfl⟩)
      have hsuffix : a ≼ path op (v r) (v x :: after.map v) := by
        apply h.below_trans hpa
        rw [he, List.map_append, List.map_cons]
        exact h.path_below_suffix _ _ _ _
      have hf := h.path_fusion (v r) (v x) (xs.map v) (after.map v) (by
        intro b hb
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hb
        have hh : v z ∈ (xs ++ [r]).map v := List.mem_map.mpr ⟨z, ha z hz, rfl⟩
        simpa only [List.map_append, List.map_cons, List.map_nil] using hh)
      exact h.below_trans (h.below_op htail hsuffix) hf

/-- Two common-root normal forms compare by their selector coverage. -/
theorem normal_below_of_coverage {Var : Type v} (v : Var → M) (r : Var)
    (P Q : List (List Var))
    (cover : ∀ (B : Set Var) j, (∃ p ∈ Q, WordSelected (p ++ [r]) B j) →
      ∃ p ∈ P, WordSelected (p ++ [r]) B j) :
    (P.map (fun p => path op (v r) (p.map v))).foldr op (v r) ≼
      (Q.map (fun p => path op (v r) (p.map v))).foldr op (v r) := by
  apply h.below_foldr (h.foldr_fixed _ _ (by
    rintro b hb
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hb
    exact h.path_fixed _ _))
  rintro b hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  exact h.path_absorption v r P q (fun B j hj => cover B j ⟨q, hq, hj⟩)

/-- Exact selector equality implies equality in every algebra satisfying the
six laws, not just the concrete winner-set model. -/
theorem interpret_eq_of_selected {Var : Type v} (s t : Term Var) (v : Var → M)
    (he : ∀ B j, s.Selected B j ↔ t.Selected B j) : interpret op v s = interpret op v t := by
  have hr : s.root = t.root := by
    have hh := (he ∅ s.root).mp (s.selected_root ∅)
    exact (t.selected_empty s.root).mp hh
  rw [h.interpret_normal v s, h.interpret_normal v t, ← hr]
  apply h.below_antisymm
  · apply h.normal_below_of_coverage
    intro B j hj
    apply (s.selected_iff_paths B j).mp
    apply (he B j).mpr
    apply (t.selected_iff_paths B j).mpr
    simpa only [hr] using hj
  · apply h.normal_below_of_coverage
    intro B j hj
    have hh := (he B j).mp ((s.selected_iff_paths B j).mpr hj)
    simpa only [hr] using (t.selected_iff_paths B j).mp hh

end Laws
end KFOL.Reset
