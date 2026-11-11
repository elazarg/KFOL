module

public import KFOL.Core.RelationalInterpolation
public import KFOL.Core.Interpolation
public import Mathlib.Tactic.FinCases

/-! # A four-valuation persistence law

Six atomic implications couple the rows. They are stable under owned choice,
and together they preserve a membership implication involving all four rows.
No finite role enumeration or relation certificate is used.
-/

@[expose] public section

namespace KFOL.Core.FourValuation
open WinnerSet
variable {Role : Type*}

private theorem good_owner (a c : Role) (A B : WinnerSet Role)
    (hA : A = singleton a ∨ c ∈ A.val) :
    choice a A B = singleton a ∨ c ∈ (choice a A B).val := by
  classical
  by_cases h : A = singleton a ∨ B = singleton a
  · exact Or.inl ((choice_eq_owner_iff _ _ _).mpr h)
  · rw [choice, ite_eq_right h]
    exact hA.elim (fun ha => (h (Or.inl ha)).elim) (fun ha => Or.inr (Or.inl ha))

private theorem good_choice (a c r : Role) (A B : WinnerSet Role)
    (hA : A = singleton a ∨ c ∈ A.val) (hB : B = singleton a ∨ c ∈ B.val) :
    choice r A B = singleton a ∨ c ∈ (choice r A B).val := by
  classical
  by_cases hr : r = a
  · subst r; exact good_owner a c A B hA
  by_cases h : A = singleton r ∨ B = singleton r
  · have hc : c = r := by
      rcases h with h | h
      · rcases hA with ha | hc
        · exact (hr ((singleton_inj.mp (h.symm.trans ha)))).elim
        · simpa [h] using hc
      · rcases hB with hb | hc
        · exact (hr ((singleton_inj.mp (h.symm.trans hb)))).elim
        · simpa [h] using hc
    exact Or.inr (by rw [(choice_eq_owner_iff _ _ _).mpr h]; exact hc)
  · rw [choice, ite_eq_right h]
    rcases hA with rfl | hc
    · rcases hB with rfl | hc
      · exact Or.inl (by apply Subtype.ext; exact Set.union_self _)
      · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hc)

private theorem implication_good (a c r : Role) (A B A' B' : WinnerSet Role)
    (h : A = singleton a → B = singleton a ∨ c ∈ B.val)
    (h' : A' = singleton a → B' = singleton a ∨ c ∈ B'.val) :
    choice r A A' = singleton a →
      choice r B B' = singleton a ∨ c ∈ (choice r B B').val := by
  classical
  by_cases hr : r = a
  · subst r
    intro ha
    rcases (choice_eq_owner_iff _ _ _).mp ha with ha | ha
    · exact good_owner a c B B' (h ha)
    · rw [choice_comm]; exact good_owner a c B' B (h' ha)
  · intro ha
    obtain ⟨ha, ha'⟩ := (choice_eq_other_iff _ _ _ hr).mp ha
    exact good_choice a c r B B' (h ha) (h' ha')

private theorem implication_atom (a r : Role) (A B A' B' : WinnerSet Role)
    (h : A = singleton a → B = singleton a)
    (h' : A' = singleton a → B' = singleton a) :
    choice r A A' = singleton a → choice r B B' = singleton a := by
  classical
  by_cases hr : r = a
  · subst r
    intro ha
    exact (choice_eq_owner_iff _ _ _).mpr
      (((choice_eq_owner_iff _ _ _).mp ha).imp h h')
  · intro ha
    obtain ⟨ha, ha'⟩ := (choice_eq_other_iff _ _ _ hr).mp ha
    rw [h ha, h' ha', choice_idempotent]

private theorem implication_mem (a r : Role) (A B A' B' : WinnerSet Role)
    (h : A = singleton a → a ∈ B.val) (h' : A' = singleton a → a ∈ B'.val) :
    choice r A A' = singleton a → a ∈ (choice r B B').val := by
  intro ha
  have hh := implication_good a a r A B A' B'
    (fun ha => Or.inr (h ha)) (fun ha => Or.inr (h' ha)) ha
  exact hh.elim (fun he => by simp [he]) id

private theorem negative_inputs (r k : Role) (A B : WinnerSet Role)
    (ha : A ≠ singleton r) (hb : B ≠ singleton r)
    (h : k ∉ (choice r A B).val) : k ∉ A.val ∧ k ∉ B.val := by
  simpa [choice, ha, hb] using h

private structure Quad (a b c : Role) (v : Fin 4 → WinnerSet Role) : Prop where
  bounded : ∀ i, (v i).val ⊆ {a, b, c}
  da : v 3 = singleton a → v 0 = singleton a
  ba : v 1 = singleton a → v 3 = singleton a ∨ c ∈ (v 3).val
  cb : v 2 = singleton b → v 0 = singleton b
  db : v 3 = singleton b → v 0 = singleton b ∨ c ∈ (v 0).val
  cc : v 2 = singleton c → c ∈ (v 1).val
  nb : v 1 ≠ singleton b
  persistent : c ∈ (v 0).val → c ∈ (v 1).val ∨ a ∈ (v 2).val ∨ c ∈ (v 3).val

private theorem persistent_choice (a b c : Role) (hac : a ≠ c) (hbc : b ≠ c)
    (r : Role) (v w : Fin 4 → WinnerSet Role) (hv : Quad a b c v) (hw : Quad a b c w)
    (ha : c ∈ (choice r (v 0) (w 0)).val)
    (hb : c ∉ (choice r (v 1) (w 1)).val)
    (hc : a ∉ (choice r (v 2) (w 2)).val)
    (hd : c ∉ (choice r (v 3) (w 3)).val) : False := by
  classical
  have contradiction (hv1 : c ∉ (v 1).val) (hv2 : a ∉ (v 2).val)
      (hv3 : c ∉ (v 3).val) (hw1 : c ∉ (w 1).val) (hw2 : a ∉ (w 2).val)
      (hw3 : c ∉ (w 3).val) (h : c ∈ (v 0).val ∨ c ∈ (w 0).val) : False := by
    rcases h with h | h
    · exact (hv.persistent h).elim hv1 (fun h => h.elim hv2 hv3)
    · exact (hw.persistent h).elim hw1 (fun h => h.elim hw2 hw3)
  by_cases hra : r = a
  · subst r
    obtain ⟨ha, hv0, hw0⟩ := (mem_choice_other a c hac _ _).mp ha
    have hv3 := fun he => hv0 (hv.da he)
    have hw3 := fun he => hw0 (hw.da he)
    obtain ⟨hdv, hdw⟩ := negative_inputs a c _ _ hv3 hw3 hd
    have hv1 : v 1 ≠ singleton a := fun he => (hv.ba he).elim hv3 hdv
    have hw1 : w 1 ≠ singleton a := fun he => (hw.ba he).elim hw3 hdw
    obtain ⟨hbv, hbw⟩ := negative_inputs a c _ _ hv1 hw1 hb
    have hh : a ∉ (v 2).val ∧ a ∉ (w 2).val := by
      simpa only [mem_choice_owner, not_or] using hc
    exact contradiction hbv hh.1 hdv hbw hh.2 hdw ha
  by_cases hrb : r = b
  · subst r
    obtain ⟨ha, hv0, hw0⟩ := (mem_choice_other b c hbc _ _).mp ha
    have hv2 := fun he => hv0 (hv.cb he)
    have hw2 := fun he => hw0 (hw.cb he)
    obtain ⟨hcv, hcw⟩ := negative_inputs b a _ _ hv2 hw2 hc
    obtain ⟨hbv, hbw⟩ := negative_inputs b c _ _ hv.nb hw.nb hb
    have hv3 : v 3 ≠ singleton b := by
      intro he
      rcases hv.db he with he | hm
      · exact hv0 he
      · exact (hv.persistent hm).elim hbv (fun hh => hh.elim hcv (by simp [he, hbc.symm]))
    have hw3 : w 3 ≠ singleton b := by
      intro he
      rcases hw.db he with he | hm
      · exact hw0 he
      · exact (hw.persistent hm).elim hbw (fun hh => hh.elim hcw (by simp [he, hbc.symm]))
    obtain ⟨hdv, hdw⟩ := negative_inputs b c _ _ hv3 hw3 hd
    exact contradiction hbv hcv hdv hbw hcw hdw ha
  by_cases hrc : r = c
  · subst r
    have hb' : c ∉ (v 1).val ∧ c ∉ (w 1).val := by
      simpa only [mem_choice_owner, not_or] using hb
    have hd' : c ∉ (v 3).val ∧ c ∉ (w 3).val := by
      simpa only [mem_choice_owner, not_or] using hd
    have hv2 := fun he => hb'.1 (hv.cc he)
    have hw2 := fun he => hb'.2 (hw.cc he)
    obtain ⟨hcv, hcw⟩ := negative_inputs c a _ _ hv2 hw2 hc
    exact contradiction hb'.1 hcv hd'.1 hb'.2 hcw hd'.2 ((mem_choice_owner _ _ _).mp ha)
  · have no_atom (q : Fin 4 → WinnerSet Role) (hq : Quad a b c q) (i : Fin 4) :
        q i ≠ singleton r := by
      intro he
      have hm := hq.bounded i (show r ∈ (q i).val by simp [he])
      simp [hra, hrb, hrc] at hm
    obtain ⟨hbv, hbw⟩ := negative_inputs r c _ _ (no_atom v hv 1) (no_atom w hw 1) hb
    obtain ⟨hcv, hcw⟩ := negative_inputs r a _ _ (no_atom v hv 2) (no_atom w hw 2) hc
    obtain ⟨hdv, hdw⟩ := negative_inputs r c _ _ (no_atom v hv 3) (no_atom w hw 3) hd
    exact contradiction hbv hcv hdv hbw hcw hdw ((mem_choice_other r c hrc _ _).mp ha).1

private theorem quad_choice (a b c : Role) (hac : a ≠ c) (hbc : b ≠ c)
    (r : Role) (v w : Fin 4 → WinnerSet Role) (hv : Quad a b c v) (hw : Quad a b c w) :
    Quad a b c (fun i => choice r (v i) (w i)) where
  bounded i := (choice_subset_union _ _ _).trans (Set.union_subset (hv.bounded i) (hw.bounded i))
  da := implication_atom a r _ _ _ _ hv.da hw.da
  ba := implication_good a c r _ _ _ _ hv.ba hw.ba
  cb := implication_atom b r _ _ _ _ hv.cb hw.cb
  db := implication_good b c r _ _ _ _ hv.db hw.db
  cc := implication_mem c r _ _ _ _ hv.cc hw.cc
  nb := by
    by_cases hr : r = b
    · subst r; simpa only [ne_eq, choice_eq_owner_iff, not_or] using And.intro hv.nb hw.nb
    · intro he; exact hv.nb ((choice_eq_other_iff _ _ _ hr).mp he).1
  persistent := by
    intro hm
    by_contra h
    push Not at h
    exact persistent_choice a b c hac hbc r v w hv hw hm h.1 h.2.1 h.2.2


private noncomputable def rows {Role : Type*} (three : Fin 3 ↪ Role) :
    Fin 4 → Fin 3 → WinnerSet Role :=
  let a := singleton (three 0)
  let b := singleton (three 1)
  let c := singleton (three 2)
  ![![a.union c, b, a], ![a.union b, a, b.union c], ![a,b,c], ![b,c,a]]

private theorem seed_quad {Role Var : Type*} (three : Fin 3 ↪ Role) (tag : Var → Fin 3) (x : Var) :
    Quad (three 0) (three 1) (three 2) (fun i => rows three i (tag x)) := by
  have hab := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have hx : tag x = 0 ∨ tag x = 1 ∨ tag x = 2 := by omega
  rcases hx with hx | hx | hx <;> constructor
  all_goals first
    | (intro i; fin_cases i <;> simp [rows, hx, Set.insert_subset_iff, Set.singleton_subset_iff])
    | simp_all [rows, union_eq_singleton_iff, singleton_inj, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

private theorem term_quad {Role Var : Type*} (three : Fin 3 ↪ Role) (tag : Var → Fin 3)
    (t : Term Role Var) (ht : t.IsCore) :
    Quad (three 0) (three 1) (three 2) (fun i => t.eval (fun x => rows three i (tag x))) := by
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x => exact seed_quad three tag x
  | choice r s t ihs iht =>
    exact quad_choice _ _ _ (three.injective.ne (by decide)) (three.injective.ne (by decide)) r _ _
      (ihs ht.1) (iht ht.2)

private theorem persistence_rows {Role Var : Type*} (three : Fin 3 ↪ Role) (tag : Var → Fin 3)
    (t : Term Role Var) (ht : t.IsCore)
    (hB : three 2 ∉ (t.eval (fun x => rows three 1 (tag x))).val)
    (hC : three 0 ∉ (t.eval (fun x => rows three 2 (tag x))).val)
    (hD : three 2 ∉ (t.eval (fun x => rows three 3 (tag x))).val) :
    three 2 ∉ (t.eval (fun x => rows three 0 (tag x))).val := by
  intro hA
  exact ((term_quad three tag t ht).persistent hA).elim hB (fun h => h.elim hC hD)
end KFOL.Core.FourValuation

namespace KFOL.Core

/-- Three simultaneous exclusions force a fourth, for every core term and
arbitrary partitions of its variables into the three input positions. -/
theorem four_valuation_persistence {Role Var : Type*} (three : Fin 3 ↪ Role)
    (tag : Var → Fin 3) (t : Term Role Var) (ht : t.IsCore)
    (hB : three 2 ∉ (t.eval (fun x =>
      ![(WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1)),
        WinnerSet.singleton (three 0),
        (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2))] (tag x))).val)
    (hC : three 0 ∉ (t.eval (fun x =>
      ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 1),
        WinnerSet.singleton (three 2)] (tag x))).val)
    (hD : three 2 ∉ (t.eval (fun x =>
      ![WinnerSet.singleton (three 1), WinnerSet.singleton (three 2),
        WinnerSet.singleton (three 0)] (tag x))).val) :
    three 2 ∉ (t.eval (fun x =>
      ![(WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 2)),
        WinnerSet.singleton (three 1), WinnerSet.singleton (three 0)] (tag x))).val :=
  FourValuation.persistence_rows three tag t ht hB hC hD

end KFOL.Core
