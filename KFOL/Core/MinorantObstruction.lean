module

public import KFOL.Core.Interpolation
public import Mathlib.Tactic.FinCases

/-! # A four-valuation cover for all core terms

Atomic tests couple two pairs of rows. A three-row atomic bridge and the
persistence of a membership implication prevent different branches from
hiding the four forbidden winners under absorbing singletons.
-/

@[expose] public section

namespace KFOL.Core.MinorantObstruction

open WinnerSet
variable {Role Var : Type*}

private def rows (a b c : Role) : Fin 4 → Fin 4 → WinnerSet Role :=
  ![![WinnerSet.singleton a, WinnerSet.singleton c, WinnerSet.singleton c, WinnerSet.singleton b],
    ![WinnerSet.singleton b, WinnerSet.singleton c, WinnerSet.singleton b, WinnerSet.singleton b],
    ![(WinnerSet.singleton a).union (WinnerSet.singleton c), WinnerSet.singleton c, WinnerSet.singleton b, WinnerSet.singleton a],
    ![WinnerSet.singleton a, WinnerSet.singleton a, (WinnerSet.singleton a).union (WinnerSet.singleton c), WinnerSet.singleton b]]

private noncomputable def out (a b c : Role) (tag : Var → Fin 4) (t : Term Role Var) (i : Fin 4) :
    WinnerSet Role := t.eval (fun x => rows a b c i (tag x))

private theorem out_choice (a b c r : Role) (tag : Var → Fin 4)
    (s t : Term Role Var) (i : Fin 4) :
    out a b c tag (.choice r s t) i = choice r (out a b c tag s i) (out a b c tag t i) := rfl

private theorem ad_atom (a b c : Role) (hab : a ≠ b) (hbc : b ≠ c)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 0 = WinnerSet.singleton b ↔ out a b c tag t 3 = WinnerSet.singleton b := by
  apply ht.isPublic.eval_singleton_iff_of_tests
  intro x
  generalize h : tag x = j
  fin_cases j <;>
    simp [rows, singleton_inj, union_eq_singleton_iff, hab, hbc.symm]

private theorem bc_atom (a b c : Role) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = WinnerSet.singleton c ↔ out a b c tag t 2 = WinnerSet.singleton c := by
  apply ht.isPublic.eval_singleton_iff_of_tests
  intro x
  generalize h : tag x = j
  fin_cases j <;>
    simp [rows, singleton_inj, union_eq_singleton_iff, hac, hbc]

private theorem bounded (a b c : Role) (tag : Var → Fin 4)
    (t : Term Role Var) (ht : t.IsCore) (i : Fin 4) :
    (out a b c tag t i).val ⊆ {a, b, c} := by
  classical
  apply ht.eval_subset_of_support
  intro x _
  generalize h : tag x = j
  fin_cases i <;> fin_cases j <;>
    simp [rows, val_union, Set.insert_subset_iff, Set.singleton_subset_iff]

private theorem bounded_second (a b c : Role) (tag : Var → Fin 4)
    (t : Term Role Var) (ht : t.IsCore) :
    (out a b c tag t 1).val ⊆ {b, c} := by
  classical
  apply ht.eval_subset_of_support
  intro x _
  generalize h : tag x = j
  fin_cases j <;>
    simp [rows, Set.singleton_subset_iff]

private theorem fourth_implication (a b c : Role) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    c ∈ (out a b c tag t 3).val → a ∈ (out a b c tag t 3).val := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x =>
    simp only [out, Term.eval]
    generalize h : tag x = j
    fin_cases j <;> simp [rows, hac.symm, hbc.symm]
  | choice r s t ihs iht =>
    rw [out_choice]
    intro hc
    by_cases hr : out a b c tag s 3 = WinnerSet.singleton r ∨ out a b c tag t 3 = WinnerSet.singleton r
    · have hcr : c = r := by simpa [choice, hr] using hc
      subst r
      rcases hr with hs | ht'
      · have ha := ihs ht.1 (by simp [hs])
        exact (hac (by simpa [hs] using ha)).elim
      · have ha := iht ht.2 (by simp [ht'])
        exact (hac (by simpa [ht'] using ha)).elim
    · simp only [choice, hr, ite_false, val_union, Set.mem_union] at hc ⊢
      exact hc.elim (fun h => Or.inl (ihs ht.1 h)) (fun h => Or.inr (iht ht.2 h))

private theorem fourth_not_c (a b c : Role) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 3 ≠ WinnerSet.singleton c := by
  intro he
  have ha := fourth_implication a b c hac hbc tag t ht (by simp [he])
  exact hac (by simpa [he] using ha)

private theorem negative_inputs (r k : Role) (A B : WinnerSet Role)
    (ha : A ≠ WinnerSet.singleton r) (hb : B ≠ WinnerSet.singleton r)
    (h : k ∉ (choice r A B).val) : k ∉ A.val ∧ k ∉ B.val := by
  simpa [choice, ha, hb] using h

private theorem bridge (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = WinnerSet.singleton b →
      out a b c tag t 3 = WinnerSet.singleton a → a ∈ (out a b c tag t 0).val := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x =>
    simp only [out, Term.eval]
    generalize h : tag x = j
    fin_cases j <;> simp [rows, union_eq_singleton_iff, singleton_inj, hab, hab.symm, hac, hac.symm, hbc.symm]
  | choice r s t ihs iht =>
    rw [out_choice, out_choice, out_choice]
    intro hB hD
    by_cases hra : r = a
    · subst r
      obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ a hab).mp hB
      rcases (choice_eq_owner_iff _ _ a).mp hD with hDs | hDt
      · exact (mem_choice_owner _ _ _).mpr (Or.inl (ihs ht.1 hBs hDs))
      · exact (mem_choice_owner _ _ _).mpr (Or.inr (iht ht.2 hBt hDt))
    by_cases hrb : r = b
    · subst r
      obtain ⟨hDs, hDt⟩ := (choice_eq_other_iff _ _ b hab.symm).mp hD
      have hs0 : out a b c tag s 0 ≠ WinnerSet.singleton b := by
        intro hs
        have hd := (ad_atom a b c hab hbc tag s ht.1).mp hs
        exact hab (singleton_inj.mp (hDs.symm.trans hd))
      have ht0 : out a b c tag t 0 ≠ WinnerSet.singleton b := by
        intro hs
        have hd := (ad_atom a b c hab hbc tag t ht.2).mp hs
        exact hab (singleton_inj.mp (hDt.symm.trans hd))
      rw [choice, ite_eq_right (not_or.mpr ⟨hs0, ht0⟩), val_union, Set.mem_union]
      exact ((choice_eq_owner_iff _ _ b).mp hB).elim
        (fun hs => Or.inl (ihs ht.1 hs hDs)) (fun ht' => Or.inr (iht ht.2 ht' hDt))
    · obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ r hrb).mp hB
      obtain ⟨hDs, hDt⟩ := (choice_eq_other_iff _ _ r hra).mp hD
      have hAs := ihs ht.1 hBs hDs
      have hAt := iht ht.2 hBt hDt
      have hs0 : out a b c tag s 0 ≠ WinnerSet.singleton r := by
        intro he
        have har : a = r := by simpa [he] using hAs
        exact hra har.symm
      have ht0 : out a b c tag t 0 ≠ WinnerSet.singleton r := by
        intro he
        have har : a = r := by simpa [he] using hAt
        exact hra har.symm
      rw [choice, ite_eq_right (not_or.mpr ⟨hs0, ht0⟩), val_union, Set.mem_union]
      exact Or.inl hAs

private theorem persistence (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = WinnerSet.singleton b →
      a ∉ (out a b c tag t 0).val → b ∉ (out a b c tag t 2).val →
        b ∈ (out a b c tag t 3).val := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x =>
    simp only [out, Term.eval]
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, hab, hbc.symm]
  | choice r s t ihs iht =>
    rw [out_choice, out_choice, out_choice, out_choice]
    intro hB hA hC
    by_contra hD
    by_cases hra : r = a
    · subst r
      obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ a hab).mp hB
      have hAs : a ∉ (out a b c tag s 0).val ∧ a ∉ (out a b c tag t 0).val := by
        simpa only [mem_choice_owner, not_or] using hA
      have hsD : out a b c tag s 3 ≠ WinnerSet.singleton a :=
        fun he => hAs.1 (bridge a b c hab hac hbc tag s ht.1 hBs he)
      have htD : out a b c tag t 3 ≠ WinnerSet.singleton a :=
        fun he => hAs.2 (bridge a b c hab hac hbc tag t ht.2 hBt he)
      obtain ⟨hDs, hDt⟩ := negative_inputs a b _ _ hsD htD hD
      have hCs : b ∈ (out a b c tag s 2).val := by
        by_contra hn
        exact hDs (ihs ht.1 hBs hAs.1 hn)
      have hCt : b ∈ (out a b c tag t 2).val := by
        by_contra hn
        exact hDt (iht ht.2 hBt hAs.2 hn)
      have htC : out a b c tag t 2 ≠ WinnerSet.singleton a := by
        intro he
        have hba : b = a := by simpa [he] using hCt
        exact hab hba.symm
      exact hC (subset_choice_of_right_ne _ _ _ htC hCs)
    by_cases hrb : r = b
    · subst r
      have hCs : b ∉ (out a b c tag s 2).val ∧ b ∉ (out a b c tag t 2).val := by
        simpa only [mem_choice_owner, not_or] using hC
      have hDs : b ∉ (out a b c tag s 3).val ∧ b ∉ (out a b c tag t 3).val := by
        simpa only [mem_choice_owner, not_or] using hD
      have hsA : out a b c tag s 0 ≠ WinnerSet.singleton b := by
        intro he
        exact hDs.1 (by rw [(ad_atom a b c hab hbc tag s ht.1).mp he]; simp)
      have htA : out a b c tag t 0 ≠ WinnerSet.singleton b := by
        intro he
        exact hDs.2 (by rw [(ad_atom a b c hab hbc tag t ht.2).mp he]; simp)
      obtain ⟨hAs, hAt⟩ := negative_inputs b a _ _ hsA htA hA
      rcases (choice_eq_owner_iff _ _ b).mp hB with hBs | hBt
      · exact hDs.1 (ihs ht.1 hBs hAs hCs.1)
      · exact hDs.2 (iht ht.2 hBt hAt hCs.2)
    by_cases hrc : r = c
    · subst r
      obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ c hbc.symm).mp hB
      have hsC : out a b c tag s 2 ≠ WinnerSet.singleton c := by
        intro he
        have hb := (bc_atom a b c hac hbc tag s ht.1).mpr he
        exact hbc (singleton_inj.mp (hBs.symm.trans hb))
      have htC : out a b c tag t 2 ≠ WinnerSet.singleton c := by
        intro he
        have hb := (bc_atom a b c hac hbc tag t ht.2).mpr he
        exact hbc (singleton_inj.mp (hBt.symm.trans hb))
      obtain ⟨hCs, hCt⟩ := negative_inputs c b _ _ hsC htC hC
      obtain ⟨hDs, hDt⟩ := negative_inputs c b _ _
        (fourth_not_c a b c hac hbc tag s ht.1)
        (fourth_not_c a b c hac hbc tag t ht.2) hD
      have hAs : a ∈ (out a b c tag s 0).val := by
        by_contra hn
        exact hDs (ihs ht.1 hBs hn hCs)
      have hAt : a ∈ (out a b c tag t 0).val := by
        by_contra hn
        exact hDt (iht ht.2 hBt hn hCt)
      have htA : out a b c tag t 0 ≠ WinnerSet.singleton c := by
        intro he
        exact hac (by simpa [he] using hAt)
      exact hA (subset_choice_of_right_ne _ _ _ htA hAs)
    · have no_atom (u : Term Role Var) (hu : u.IsCore) (i : Fin 4) :
          out a b c tag u i ≠ WinnerSet.singleton r := by
        intro he
        have hm := bounded a b c tag u hu i (show r ∈ (out a b c tag u i).val by simp [he])
        simp [hra, hrb, hrc] at hm
      obtain ⟨hBs, _⟩ := (choice_eq_other_iff _ _ r hrb).mp hB
      obtain ⟨hAs, _⟩ := negative_inputs r a _ _ (no_atom s ht.1 0) (no_atom t ht.2 0) hA
      obtain ⟨hCs, _⟩ := negative_inputs r b _ _ (no_atom s ht.1 2) (no_atom t ht.2 2) hC
      obtain ⟨hDs, _⟩ := negative_inputs r b _ _ (no_atom s ht.1 3) (no_atom t ht.2 3) hD
      exact hDs (ihs ht.1 hBs hAs hCs)

private theorem cover (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    a ∈ (out a b c tag t 0).val ∨ c ∈ (out a b c tag t 1).val ∨
      b ∈ (out a b c tag t 2).val ∨ b ∈ (out a b c tag t 3).val := by
  classical
  by_contra hn
  have hA : a ∉ (out a b c tag t 0).val := fun h => hn (Or.inl h)
  have hB : c ∉ (out a b c tag t 1).val := fun h => hn (Or.inr (Or.inl h))
  have hC : b ∉ (out a b c tag t 2).val := fun h => hn (Or.inr (Or.inr (Or.inl h)))
  have hD : b ∉ (out a b c tag t 3).val := fun h => hn (Or.inr (Or.inr (Or.inr h)))
  have hBb : out a b c tag t 1 = WinnerSet.singleton b := by
    apply eq_singleton_of_subset _ b
    intro k hk
    have hm := bounded_second a b c tag t ht hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hB hk).elim
  exact hD (persistence a b c hab hac hbc tag t ht hBb hA hC)

end KFOL.Core.MinorantObstruction

namespace KFOL.Core

/-- Two atomic observations force membership at a third valuation, allowing
arbitrary variable types and arbitrary repeated occurrences of each position. -/
theorem three_valuation_minorant_bridge {Role Var : Type*} (three : Fin 3 ↪ Role)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore)
    (hB : t.eval (fun x => ![WinnerSet.singleton (three 1), WinnerSet.singleton (three 2),
      WinnerSet.singleton (three 1), WinnerSet.singleton (three 1)] (tag x)) =
        WinnerSet.singleton (three 1))
    (hD : t.eval (fun x => ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 0),
      (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 2)),
      WinnerSet.singleton (three 1)] (tag x)) = WinnerSet.singleton (three 0)) :
    three 0 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 2),
      WinnerSet.singleton (three 2), WinnerSet.singleton (three 1)] (tag x))).val :=
  MinorantObstruction.bridge _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) tag t ht hB hD

/-- Every core term retains at least one of four designated winners. In
particular, no core operation can lie below a function excluding all four. -/
theorem four_valuation_minorant_cover {Role Var : Type*} (three : Fin 3 ↪ Role)
    (tag : Var → Fin 4) (t : Term Role Var) (ht : t.IsCore) :
    three 0 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 2),
      WinnerSet.singleton (three 2), WinnerSet.singleton (three 1)] (tag x))).val ∨
    three 2 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 1), WinnerSet.singleton (three 2),
      WinnerSet.singleton (three 1), WinnerSet.singleton (three 1)] (tag x))).val ∨
    three 1 ∈ (t.eval (fun x => ![(WinnerSet.singleton (three 0)).union
      (WinnerSet.singleton (three 2)), WinnerSet.singleton (three 2),
      WinnerSet.singleton (three 1), WinnerSet.singleton (three 0)] (tag x))).val ∨
    three 1 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 0),
      (WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 2)),
      WinnerSet.singleton (three 1)] (tag x))).val :=
  MinorantObstruction.cover _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) tag t ht

end KFOL.Core
