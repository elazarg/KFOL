module

public import KFOL.Core.Interpolation
public import Mathlib.Tactic.FinCases

/-! # A five-valuation obstruction to core minorants

Two atomic tests and four symbolic bridge laws couple the five rows. Root
induction then rules out simultaneous exclusion of all five designated winners.
No role enumeration or finite relation certificate enters the proof.
-/

@[expose] public section
set_option linter.unusedSimpArgs false
namespace KFOL.Core.MinorantFive
open WinnerSet
variable {Role Var : Type*}

private def rows (a b c : Role) : Fin 5 → Fin 5 → WinnerSet Role :=
  ![![singleton a, singleton b, singleton b, (singleton b).union (singleton c), singleton c],
    ![singleton a, singleton b, singleton a, singleton a, singleton a],
    ![singleton c, singleton c, singleton b, singleton c, singleton a],
    ![singleton c, (singleton b).union (singleton c), singleton b, singleton a, singleton b],
    ![singleton b, singleton c, (singleton b).union (singleton c),
      (singleton b).union (singleton c), singleton a]]
private noncomputable def out (a b c : Role) (tag : Var → Fin 5) (t : Term Role Var) (i : Fin 5) :
    WinnerSet Role := t.eval (fun x => rows a b c i (tag x))
private theorem out_choice (a b c r : Role) (tag : Var → Fin 5)
    (s t : Term Role Var) (i : Fin 5) :
    out a b c tag (.choice r s t) i = choice r (out a b c tag s i) (out a b c tag t i) := rfl

private theorem no_pair (r s : Role) (hrs : r ≠ s) (v w : Var → WinnerSet Role)
    (hv : ∀ x, ¬(v x = singleton r ∧ w x = singleton s))
    (t : Term Role Var) (ht : t.IsCore) :
    ¬(t.eval v = singleton r ∧ t.eval w = singleton s) := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x => exact hv x
  | choice q t u iht ihu =>
    rintro ⟨hr, hs⟩
    by_cases hqr : q = r
    · subst q
      obtain ⟨hts, hus⟩ := (choice_eq_other_iff _ _ r hrs).mp hs
      exact ((choice_eq_owner_iff _ _ r).mp hr).elim
        (fun htr => iht ht.1 ⟨htr, hts⟩) (fun hur => ihu ht.2 ⟨hur, hus⟩)
    · obtain ⟨htr, hur⟩ := (choice_eq_other_iff _ _ q hqr).mp hr
      by_cases hqs : q = s
      · subst q
        exact ((choice_eq_owner_iff _ _ s).mp hs).elim
          (fun hts => iht ht.1 ⟨htr, hts⟩) (fun hus => ihu ht.2 ⟨hur, hus⟩)
      · obtain ⟨hts, _⟩ := (choice_eq_other_iff _ _ q hqs).mp hs
        exact iht ht.1 ⟨htr, hts⟩

private theorem atomic_bridge (r s : Role) (hrs : r ≠ s)
    (v w z : Var → WinnerSet Role)
    (hbase : ∀ x, v x = singleton r → w x = singleton s → s ∈ (z x).val)
    (hblock : ∀ x, ¬(w x = singleton s ∧ z x = singleton r))
    (t : Term Role Var) (ht : t.IsCore) :
    t.eval v = singleton r → t.eval w = singleton s → s ∈ (t.eval z).val := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x => exact hbase x
  | choice q t u iht ihu =>
    intro hr hs
    by_cases hqs : q = s
    · subst q
      obtain ⟨htr, hur⟩ := (choice_eq_other_iff _ _ s hrs.symm).mp hr
      exact (mem_choice_owner _ _ _).mpr (((choice_eq_owner_iff _ _ s).mp hs).elim
        (fun hts => Or.inl (iht ht.1 htr hts))
        (fun hus => Or.inr (ihu ht.2 hur hus)))
    by_cases hqr : q = r
    · subst q
      obtain ⟨hts, hus⟩ := (choice_eq_other_iff _ _ r hrs).mp hs
      have ht0 : t.eval z ≠ singleton r := fun he => no_pair s r hrs.symm w z hblock t ht.1 ⟨hts, he⟩
      have hu0 : u.eval z ≠ singleton r := fun he => no_pair s r hrs.symm w z hblock u ht.2 ⟨hus, he⟩
      rw [Term.eval, choice, ite_eq_right (not_or.mpr ⟨ht0, hu0⟩), val_union, Set.mem_union]
      exact ((choice_eq_owner_iff _ _ r).mp hr).elim
        (fun htr => Or.inl (iht ht.1 htr hts)) (fun hur => Or.inr (ihu ht.2 hur hus))
    · obtain ⟨htr, hur⟩ := (choice_eq_other_iff _ _ q hqr).mp hr
      obtain ⟨hts, hus⟩ := (choice_eq_other_iff _ _ q hqs).mp hs
      have hm := iht ht.1 htr hts
      have hn := ihu ht.2 hur hus
      have hu0 : u.eval z ≠ singleton q := by
        intro he
        exact hqs (show s = q from by simpa [he] using hn).symm
      exact subset_choice_of_right_ne _ _ _ hu0 hm

private theorem ce_atom (a b c : Role) (hab : a ≠ b) (hac : a ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 2 = singleton a ↔ out a b c tag t 4 = singleton a := by
  apply ht.isPublic.eval_singleton_iff_of_tests
  intro x
  generalize h : tag x = j
  fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff, hab.symm, hac.symm]

private theorem ba_ec (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore)
    (hB : out a b c tag t 1 = singleton a) : out a b c tag t 4 ≠ singleton c := by
  intro hE
  apply no_pair a c hac (fun x => rows a b c 1 (tag x))
    (fun x => rows a b c 4 (tag x)) ?_ t ht ⟨hB, hE⟩
  intro x
  generalize h : tag x = j
  fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff, hab.symm, hac, hac.symm, hbc, hbc.symm]

private theorem dc_ab (a b c : Role) (hab : a ≠ b) (_hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore)
    (hD : out a b c tag t 3 = singleton c) : out a b c tag t 0 ≠ singleton b := by
  intro hA
  apply no_pair c b hbc.symm (fun x => rows a b c 3 (tag x))
    (fun x => rows a b c 0 (tag x)) ?_ t ht ⟨hD, hA⟩
  intro x
  generalize h : tag x = j
  fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff, hab, hbc, hbc.symm]

private theorem bridgeI (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = singleton a → out a b c tag t 0 = singleton b →
      b ∈ (out a b c tag t 2).val := by
  apply atomic_bridge a b hab _ _ _ ?_ ?_ t ht
  · intro x
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
  · intro x
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]

private theorem bridgeII (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = singleton a → out a b c tag t 0 = singleton c →
      a ∈ (out a b c tag t 4).val := by
  intro hB hA
  apply atomic_bridge c a hac.symm _ _ _ ?_ ?_ t ht hA hB
  · intro x
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
  · intro x
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff, hab, hab.symm, hac, hac.symm, hbc, hbc.symm]

private theorem bounded (a b c : Role) (tag : Var → Fin 5)
    (t : Term Role Var) (ht : t.IsCore) (i : Fin 5) :
    (out a b c tag t i).val ⊆ {a,b,c} := by
  classical
  apply ht.eval_subset_of_support
  intro x _
  generalize h : tag x = j
  fin_cases i <;> fin_cases j <;>
    simp [rows, val_union, Set.insert_subset_iff, Set.singleton_subset_iff]

private theorem no_other_atom (a b c r : Role) (hra : r ≠ a) (hrb : r ≠ b) (hrc : r ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) (i : Fin 5) :
    out a b c tag t i ≠ singleton r := by
  intro he
  have hm := bounded a b c tag t ht i (show r ∈ (out a b c tag t i).val by simp [he])
  simp [hra, hrb, hrc] at hm

private theorem negative_inputs (r k : Role) (A B : WinnerSet Role)
    (ha : A ≠ singleton r) (hb : B ≠ singleton r)
    (h : k ∉ (choice r A B).val) : k ∉ A.val ∧ k ∉ B.val := by
  simpa [choice, ha, hb] using h

private theorem mem_both (r k : Role) (S T : WinnerSet Role)
    (hs : k ∈ S.val) (ht : k ∈ T.val) : k ∈ (choice r S T).val := by
  have hm := choice_mono r (A := singleton k) (B := singleton k) (C := S) (D := T)
    (Set.singleton_subset_iff.mpr hs) (Set.singleton_subset_iff.mpr ht)
  exact hm (by simp)

private theorem bridgeIII (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = singleton a → out a b c tag t 3 = singleton c →
      a ∉ (out a b c tag t 0).val → a ∈ (out a b c tag t 4).val := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x =>
    simp only [out, Term.eval]
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff,
      hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
  | choice r s t ihs iht =>
    rw [out_choice, out_choice, out_choice, out_choice]
    intro hB hD hA
    by_cases hra : r = a
    · subst r
      obtain ⟨hDs, hDt⟩ := (choice_eq_other_iff _ _ a hac).mp hD
      have hAs : a ∉ (out a b c tag s 0).val ∧ a ∉ (out a b c tag t 0).val := by
        simpa only [mem_choice_owner, not_or] using hA
      exact (mem_choice_owner _ _ _).mpr (((choice_eq_owner_iff _ _ a).mp hB).elim
        (fun hBs => Or.inl (ihs ht.1 hBs hDs hAs.1))
        (fun hBt => Or.inr (iht ht.2 hBt hDt hAs.2)))
    by_cases hrc : r = c
    · subst r
      obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ c hac.symm).mp hB
      by_contra hE
      obtain ⟨hEs, hEt⟩ := negative_inputs c a _ _
        (ba_ec a b c hab hac hbc tag s ht.1 hBs)
        (ba_ec a b c hab hac hbc tag t ht.2 hBt) hE
      have hsA : out a b c tag s 0 ≠ singleton c :=
        fun he => hEs (bridgeII a b c hab hac hbc tag s ht.1 hBs he)
      have htA : out a b c tag t 0 ≠ singleton c :=
        fun he => hEt (bridgeII a b c hab hac hbc tag t ht.2 hBt he)
      obtain ⟨hAs, hAt⟩ := negative_inputs c a _ _ hsA htA hA
      exact ((choice_eq_owner_iff _ _ c).mp hD).elim
        (fun hDs => hEs (ihs ht.1 hBs hDs hAs))
        (fun hDt => hEt (iht ht.2 hBt hDt hAt))
    · obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ r hra).mp hB
      obtain ⟨hDs, hDt⟩ := (choice_eq_other_iff _ _ r hrc).mp hD
      have noA (u : Term Role Var) (hu : u.IsCore)
          (hDu : out a b c tag u 3 = singleton c) : out a b c tag u 0 ≠ singleton r := by
        by_cases hrb : r = b
        · subst r
          exact dc_ab a b c hab hac hbc tag u hu hDu
        · exact no_other_atom a b c r hra hrb hrc tag u hu 0
      obtain ⟨hAs, hAt⟩ := negative_inputs r a _ _ (noA s ht.1 hDs) (noA t ht.2 hDt) hA
      exact mem_both r a _ _ (ihs ht.1 hBs hDs hAs) (iht ht.2 hBt hDt hAt)

private theorem bridgeIV (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = singleton a → out a b c tag t 4 = singleton b →
      a ∉ (out a b c tag t 0).val → b ∈ (out a b c tag t 2).val := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x =>
    simp only [out, Term.eval]
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff,
      hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
  | choice r s t ihs iht =>
    rw [out_choice, out_choice, out_choice, out_choice]
    intro hB hE hA
    by_cases hra : r = a
    · subst r
      obtain ⟨hEs, hEt⟩ := (choice_eq_other_iff _ _ a hab).mp hE
      have hAs : a ∉ (out a b c tag s 0).val ∧ a ∉ (out a b c tag t 0).val := by
        simpa only [mem_choice_owner, not_or] using hA
      have noC (u : Term Role Var) (hu : u.IsCore)
          (hEu : out a b c tag u 4 = singleton b) : out a b c tag u 2 ≠ singleton a := by
        intro he
        have hEa := (ce_atom a b c hab hac tag u hu).mp he
        exact hab (singleton_inj.mp (hEa.symm.trans hEu))
      rw [choice, ite_eq_right (not_or.mpr ⟨noC s ht.1 hEs, noC t ht.2 hEt⟩),
        val_union, Set.mem_union]
      exact ((choice_eq_owner_iff _ _ a).mp hB).elim
        (fun hBs => Or.inl (ihs ht.1 hBs hEs hAs.1))
        (fun hBt => Or.inr (iht ht.2 hBt hEt hAs.2))
    by_cases hrb : r = b
    · subst r
      obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ b hab.symm).mp hB
      by_contra hC
      have hCs : b ∉ (out a b c tag s 2).val ∧ b ∉ (out a b c tag t 2).val := by
        simpa only [mem_choice_owner, not_or] using hC
      have hsA : out a b c tag s 0 ≠ singleton b :=
        fun he => hCs.1 (bridgeI a b c hab hac hbc tag s ht.1 hBs he)
      have htA : out a b c tag t 0 ≠ singleton b :=
        fun he => hCs.2 (bridgeI a b c hab hac hbc tag t ht.2 hBt he)
      obtain ⟨hAs, hAt⟩ := negative_inputs b a _ _ hsA htA hA
      exact ((choice_eq_owner_iff _ _ b).mp hE).elim
        (fun hEs => hCs.1 (ihs ht.1 hBs hEs hAs))
        (fun hEt => hCs.2 (iht ht.2 hBt hEt hAt))
    · obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ r hra).mp hB
      obtain ⟨hEs, hEt⟩ := (choice_eq_other_iff _ _ r hrb).mp hE
      have noA (u : Term Role Var) (hu : u.IsCore)
          (hBu : out a b c tag u 1 = singleton a)
          (hEu : out a b c tag u 4 = singleton b) : out a b c tag u 0 ≠ singleton r := by
        by_cases hrc : r = c
        · subst r
          intro he
          have hm := bridgeII a b c hab hac hbc tag u hu hBu he
          exact hab (by simpa [hEu] using hm)
        · exact no_other_atom a b c r hra hrb hrc tag u hu 0
      obtain ⟨hAs, hAt⟩ := negative_inputs r a _ _
        (noA s ht.1 hBs hEs) (noA t ht.2 hBt hEt) hA
      exact mem_both r b _ _ (ihs ht.1 hBs hEs hAs) (iht ht.2 hBt hEt hAt)

private theorem persistence (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    out a b c tag t 1 = singleton a → a ∉ (out a b c tag t 0).val →
      b ∉ (out a b c tag t 2).val → a ∉ (out a b c tag t 3).val →
        a ∈ (out a b c tag t 4).val := by
  classical
  induction t with
  | winner => exact ht.elim
  | rename => exact ht.elim
  | var x =>
    simp only [out, Term.eval]
    generalize h : tag x = j
    fin_cases j <;> simp [rows, singleton_inj, union_eq_singleton_iff,
      hab, hab.symm, hac, hac.symm, hbc, hbc.symm]
  | choice r s t ihs iht =>
    rw [out_choice, out_choice, out_choice, out_choice, out_choice]
    intro hB hA hC hD
    by_contra hE
    by_cases hra : r = a
    · subst r
      have hAs : a ∉ (out a b c tag s 0).val ∧ a ∉ (out a b c tag t 0).val := by
        simpa only [mem_choice_owner, not_or] using hA
      have hDs : a ∉ (out a b c tag s 3).val ∧ a ∉ (out a b c tag t 3).val := by
        simpa only [mem_choice_owner, not_or] using hD
      have hEs : a ∉ (out a b c tag s 4).val ∧ a ∉ (out a b c tag t 4).val := by
        simpa only [mem_choice_owner, not_or] using hE
      have noC (u : Term Role Var) (hu : u.IsCore)
          (hEu : a ∉ (out a b c tag u 4).val) : out a b c tag u 2 ≠ singleton a := by
        intro he
        exact hEu (by rw [(ce_atom a b c hab hac tag u hu).mp he]; simp)
      obtain ⟨hCs, hCt⟩ := negative_inputs a b _ _ (noC s ht.1 hEs.1) (noC t ht.2 hEs.2) hC
      exact ((choice_eq_owner_iff _ _ a).mp hB).elim
        (fun hBs => hEs.1 (ihs ht.1 hBs hAs.1 hCs hDs.1))
        (fun hBt => hEs.2 (iht ht.2 hBt hAs.2 hCt hDs.2))
    by_cases hrb : r = b
    · subst r
      obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ b hab.symm).mp hB
      have hCs : b ∉ (out a b c tag s 2).val ∧ b ∉ (out a b c tag t 2).val := by
        simpa only [mem_choice_owner, not_or] using hC
      have hsA : out a b c tag s 0 ≠ singleton b :=
        fun he => hCs.1 (bridgeI a b c hab hac hbc tag s ht.1 hBs he)
      have htA : out a b c tag t 0 ≠ singleton b :=
        fun he => hCs.2 (bridgeI a b c hab hac hbc tag t ht.2 hBt he)
      obtain ⟨hAs, hAt⟩ := negative_inputs b a _ _ hsA htA hA
      have hsE : out a b c tag s 4 ≠ singleton b :=
        fun he => hCs.1 (bridgeIV a b c hab hac hbc tag s ht.1 hBs he hAs)
      have htE : out a b c tag t 4 ≠ singleton b :=
        fun he => hCs.2 (bridgeIV a b c hab hac hbc tag t ht.2 hBt he hAt)
      obtain ⟨hEs, hEt⟩ := negative_inputs b a _ _ hsE htE hE
      have hDs : a ∈ (out a b c tag s 3).val := by
        by_contra hn
        exact hEs (ihs ht.1 hBs hAs hCs.1 hn)
      have hDt : a ∈ (out a b c tag t 3).val := by
        by_contra hn
        exact hEt (iht ht.2 hBt hAt hCs.2 hn)
      exact hD (mem_both b a _ _ hDs hDt)
    by_cases hrc : r = c
    · subst r
      obtain ⟨hBs, hBt⟩ := (choice_eq_other_iff _ _ c hac.symm).mp hB
      obtain ⟨hEs, hEt⟩ := negative_inputs c a _ _
        (ba_ec a b c hab hac hbc tag s ht.1 hBs)
        (ba_ec a b c hab hac hbc tag t ht.2 hBt) hE
      have hsA : out a b c tag s 0 ≠ singleton c :=
        fun he => hEs (bridgeII a b c hab hac hbc tag s ht.1 hBs he)
      have htA : out a b c tag t 0 ≠ singleton c :=
        fun he => hEt (bridgeII a b c hab hac hbc tag t ht.2 hBt he)
      obtain ⟨hAs, hAt⟩ := negative_inputs c a _ _ hsA htA hA
      have hsD : out a b c tag s 3 ≠ singleton c :=
        fun he => hEs (bridgeIII a b c hab hac hbc tag s ht.1 hBs he hAs)
      have htD : out a b c tag t 3 ≠ singleton c :=
        fun he => hEt (bridgeIII a b c hab hac hbc tag t ht.2 hBt he hAt)
      obtain ⟨hDs, hDt⟩ := negative_inputs c a _ _ hsD htD hD
      have hCs : b ∈ (out a b c tag s 2).val := by
        by_contra hn
        exact hEs (ihs ht.1 hBs hAs hn hDs)
      have hCt : b ∈ (out a b c tag t 2).val := by
        by_contra hn
        exact hEt (iht ht.2 hBt hAt hn hDt)
      exact hC (mem_both c b _ _ hCs hCt)
    · have no_atom (u : Term Role Var) (hu : u.IsCore) (i : Fin 5) :
          out a b c tag u i ≠ singleton r := no_other_atom a b c r hra hrb hrc tag u hu i
      obtain ⟨hBs, _⟩ := (choice_eq_other_iff _ _ r hra).mp hB
      obtain ⟨hAs, _⟩ := negative_inputs r a _ _ (no_atom s ht.1 0) (no_atom t ht.2 0) hA
      obtain ⟨hCs, _⟩ := negative_inputs r b _ _ (no_atom s ht.1 2) (no_atom t ht.2 2) hC
      obtain ⟨hDs, _⟩ := negative_inputs r a _ _ (no_atom s ht.1 3) (no_atom t ht.2 3) hD
      obtain ⟨hEs, _⟩ := negative_inputs r a _ _ (no_atom s ht.1 4) (no_atom t ht.2 4) hE
      exact hEs (ihs ht.1 hBs hAs hCs hDs)

private theorem cover (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    a ∈ (out a b c tag t 0).val ∨ b ∈ (out a b c tag t 1).val ∨
      b ∈ (out a b c tag t 2).val ∨ a ∈ (out a b c tag t 3).val ∨
        a ∈ (out a b c tag t 4).val := by
  classical
  by_contra hn
  have hA : a ∉ (out a b c tag t 0).val := fun h => hn (Or.inl h)
  have hB : b ∉ (out a b c tag t 1).val := fun h => hn (Or.inr (Or.inl h))
  have hC : b ∉ (out a b c tag t 2).val := fun h => hn (Or.inr (Or.inr (Or.inl h)))
  have hD : a ∉ (out a b c tag t 3).val := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have hE : a ∉ (out a b c tag t 4).val := fun h => hn (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hBa : out a b c tag t 1 = singleton a := by
    apply eq_singleton_of_subset _ a
    intro k hk
    have hbound : (out a b c tag t 1).val ⊆ {a,b} := by
      apply ht.eval_subset_of_support
      intro x _
      generalize h : tag x = j
      fin_cases j <;> simp [rows, Set.singleton_subset_iff]
    have hm := hbound hk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hB hk).elim
  exact hE (persistence a b c hab hac hbc tag t ht hBa hA hC hD)

end KFOL.Core.MinorantFive

namespace KFOL.Core
/-- Every core term retains at least one of five designated winners. The
statement allows arbitrary role and variable types and repeated input groups. -/
theorem five_valuation_minorant_cover {Role Var : Type*} (three : Fin 3 ↪ Role)
    (tag : Var → Fin 5) (t : Term Role Var) (ht : t.IsCore) :
    three 0 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 1),
      WinnerSet.singleton (three 1), (WinnerSet.singleton (three 1)).union
        (WinnerSet.singleton (three 2)), WinnerSet.singleton (three 2)] (tag x))).val ∨
    three 1 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 1),
      WinnerSet.singleton (three 0), WinnerSet.singleton (three 0),
      WinnerSet.singleton (three 0)] (tag x))).val ∨
    three 1 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 2), WinnerSet.singleton (three 2),
      WinnerSet.singleton (three 1), WinnerSet.singleton (three 2),
      WinnerSet.singleton (three 0)] (tag x))).val ∨
    three 0 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 2),
      (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2)),
      WinnerSet.singleton (three 1), WinnerSet.singleton (three 0),
      WinnerSet.singleton (three 1)] (tag x))).val ∨
    three 0 ∈ (t.eval (fun x => ![WinnerSet.singleton (three 1), WinnerSet.singleton (three 2),
      (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2)),
      (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2)),
      WinnerSet.singleton (three 0)] (tag x))).val :=
  MinorantFive.cover _ _ _ (three.injective.ne (by decide))
    (three.injective.ne (by decide)) (three.injective.ne (by decide)) tag t ht
end KFOL.Core
