module

public import KFOL.Policies.Reductions

/-! Complete non-easy-family incidence certificate construction. -/

@[expose] public section

namespace KFOL.Policies

universe u v

variable {Role : Type u} {Label : Type v}

private theorem exists_third (three : Fin 3 ↪ Role) (a b : Role) :
    ∃ w, a ≠ w ∧ b ≠ w := by
  classical
  by_contra! h
  have h0 := h (three 0)
  have h1 := h (three 1)
  have h2 := h (three 2)
  have h01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have h02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have h12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  by_cases ha0 : a = three 0
  · have ha1 : a ≠ three 1 := fun he => h01 (ha0.symm.trans he)
    have ha2 : a ≠ three 2 := fun he => h02 (ha0.symm.trans he)
    exact h12 ((h1 ha1).symm.trans (h2 ha2))
  · have hb0 := h0 ha0
    by_cases ha1 : a = three 1
    · have ha2 : a ≠ three 2 := fun he => h12 (ha1.symm.trans he)
      exact h02 (hb0.symm.trans (h2 ha2))
    · exact h01 (hb0.symm.trans (h1 ha1))

/-- Finite labels provide actual finite passing patterns. Complements occur
only in the fixed-family preprocessing, never in the native term evaluator. -/
@[simp] theorem mem_finitePattern [Fintype Label] (D : Label → Set Role) (r : Role) (d : Label) :
    d ∈ finitePattern D r ↔ r ∉ D d := by
  classical
  simp [finitePattern]

@[simp] theorem coe_finitePattern [Fintype Label] (D : Label → Set Role) (r : Role) :
    (finitePattern D r : Set Label) = passingPattern D r := by
  ext d
  exact mem_finitePattern D r d

theorem missing_meet_of_not_familyEasy [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]
    (D : Label → Set Role) (hne : ¬FamilyEasy D) :
    ∃ (J : Finset Role) (s : Finset Label) (p q : Role),
      p ∈ J ∧ q ∈ J ∧ finitePattern D p ∩ finitePattern D q = s ∧
      (∀ r ∈ J, finitePattern D r ≠ s) ∧
      (J = Finset.univ ∨ ∃ k, J = Finset.univ.erase k ∧ Function.Injective (finitePattern D)) := by
  classical
  have hsub (r s : Role) : finitePattern D r ⊆ finitePattern D s ↔
      passingPattern D r ⊆ passingPattern D s := by
    change ((finitePattern D r : Set Label) ⊆ (finitePattern D s : Set Label)) ↔ _
    rw [coe_finitePattern, coe_finitePattern]
  have heq (r s : Role) : finitePattern D r = finitePattern D s ↔
      passingPattern D r = passingPattern D s := by
    rw [← Finset.coe_inj, coe_finitePattern, coe_finitePattern]
  have hinter (r s t : Role) : finitePattern D t = finitePattern D r ∩ finitePattern D s ↔
      passingPattern D t = passingPattern D r ∩ passingPattern D s := by
    rw [← Finset.coe_inj, Finset.coe_inter, coe_finitePattern, coe_finitePattern, coe_finitePattern]
  have hchain : ¬∀ r s, finitePattern D r ⊆ finitePattern D s ∨ finitePattern D s ⊆ finitePattern D r := by
    intro hc
    apply hne
    exact Or.inl (fun r s => (hc r s).imp (hsub r s).mp (hsub s r).mp)
  have heasy : ¬((∀ r s, ∃ t, finitePattern D t = finitePattern D r ∩ finitePattern D s) ∧
      ∃ r s, r ≠ s ∧ finitePattern D r = finitePattern D s) := by
    rintro ⟨hc, r, s, hrs, he⟩
    apply hne
    refine Or.inr ⟨?_, r, s, hrs, (heq r s).mp he⟩
    intro a b
    obtain ⟨t, ht⟩ := hc a b
    exact ⟨t, (hinter a b t).mp ht⟩
  exact missing_meet_of_not_easy (finitePattern D) hchain heasy

namespace Hardness.Plan

private theorem certificate_from_macros [Fintype Role] [Fintype Label] [DecidableEq Role]
    (D : Label → Set Role) (three : Fin 3 ↪ Role)
    (J : Finset Role) (s : Finset Label) (E F : PolicyExpr Label) (a b : Role)
    (haJ : a ∈ J) (hbJ : b ∈ J) (hab : a ≠ b)
    (haU : a ∉ (PolicyExpr.unionLabels s.toList).eval D)
    (hbU : b ∉ (PolicyExpr.unionLabels s.toList).eval D)
    (haE : a ∈ E.eval D) (haF : a ∉ F.eval D)
    (hbE : b ∉ E.eval D) (hbF : b ∈ F.eval D)
    (hcover : ∀ r ∈ J, r ∉ (PolicyExpr.unionLabels s.toList).eval D →
      r ∉ E.eval D ∨ r ∉ F.eval D)
    (hshape : J = Finset.univ ∨ ∃ k, J = Finset.univ.erase k ∧ Function.Injective (finitePattern D)) :
    ∃ plan : Hardness.Plan Role Label, Nonempty (Certificate D plan) := by
  classical
  have hclear : ∀ d ∈ s.toList, a ∉ D d ∧ b ∉ D d := by
    have ha := (PolicyExpr.not_mem_eval_unionLabels D a s.toList).mp haU
    have hb := (PolicyExpr.not_mem_eval_unionLabels D b s.toList).mp hbU
    exact fun d hd => ⟨ha d hd, hb d hd⟩
  rcases hshape with hJ | ⟨k, hJ, hinj⟩
  · obtain ⟨w, haw, hbw⟩ := exists_third three a b
    let plan : Hardness.Plan Role Label := ⟨E, F, s.toList, []⟩
    refine ⟨plan, ⟨{
      a := a
      b := b
      marker := w
      a_ne_b := hab
      a_ne_marker := haw
      b_ne_marker := hbw
      a_zero := haE
      a_not_one := haF
      b_not_zero := hbE
      b_one := hbF
      preliminary_clear := hclear
      calibration_positive := ?_
      calibration_negative := ?_
      calibration_marker := ?_
      calibration_injective := ?_
      intersection := ?_ }⟩⟩
    · intro item hi; simp [plan] at hi
    · intro item hi; simp [plan] at hi
    · intro item hi; simp [plan] at hi
    · intro item hi; simp [plan] at hi
    · intro observer _ r hrE hrF hrclear
      have hrJ : r ∈ J := hJ ▸ Finset.mem_univ r
      have hrU := (PolicyExpr.not_mem_eval_unionLabels D r s.toList).mpr hrclear
      exact False.elim ((hcover r hrJ hrU).elim (fun hn => hn hrE) (fun hn => hn hrF))
  · let entries := calibrationEntries (finitePattern D) J.toList
    let plan : Hardness.Plan Role Label := ⟨E, F, s.toList, entries⟩
    have hitem : ∀ item ∈ entries, item.1 ∈ J ∧
        item.2.1 = (finitePattern D item.1).toList ∧
        item.2.2 = (Finset.univ \ finitePattern D item.1).toList := by
      intro item hi
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hi
      exact ⟨Finset.mem_toList.mp hr, rfl, rfl⟩
    have hpassinj : Function.Injective (passingPattern D) := by
      intro r t he
      apply hinj
      apply Finset.coe_injective
      simpa only [coe_finitePattern] using he
    refine ⟨plan, ⟨{
      a := a
      b := b
      marker := k
      a_ne_b := hab
      a_ne_marker := ?_
      b_ne_marker := ?_
      a_zero := haE
      a_not_one := haF
      b_not_zero := hbE
      b_one := hbF
      preliminary_clear := hclear
      calibration_positive := ?_
      calibration_negative := ?_
      calibration_marker := ?_
      calibration_injective := ?_
      intersection := ?_ }⟩⟩
    · exact (Finset.mem_erase.mp (hJ ▸ haJ)).1
    · exact (Finset.mem_erase.mp (hJ ▸ hbJ)).1
    · intro item hi d
      rw [(hitem item hi).2.1, Finset.mem_toList, mem_finitePattern]
    · intro item hi d
      rw [(hitem item hi).2.2, Finset.mem_toList, Finset.mem_sdiff]
      simp only [Finset.mem_univ, true_and, mem_finitePattern, not_not]
    · intro item hi
      exact (Finset.mem_erase.mp (hJ ▸ (hitem item hi).1)).1
    · intro item hi
      exact hpassinj
    · intro observer hexcluded r hrE hrF hrclear
      have hrU := (PolicyExpr.not_mem_eval_unionLabels D r s.toList).mpr hrclear
      have hrJ : r ∉ J := by
        intro hr
        exact (hcover r hr hrU).elim (fun hn => hn hrE) (fun hn => hn hrF)
      have hrk : r = k := by
        simpa only [hJ, Finset.mem_erase, Finset.mem_univ, and_true, not_not] using hrJ
      have hok : observer = k := by
        by_contra hne
        have hoJ : observer ∈ J := by simp [hJ, hne]
        have hi : (observer, (finitePattern D observer).toList,
            (Finset.univ \ finitePattern D observer).toList) ∈ entries :=
          List.mem_map.mpr ⟨observer, Finset.mem_toList.mpr hoJ, rfl⟩
        exact hexcluded _ hi rfl
      exact hrk.trans hok.symm

end Hardness.Plan

/-- Every non-easy finite family has a concrete native CNF equation plan with
all incidence, calibration, and separating-role obligations discharged. -/
theorem exists_certified_hardness_plan [Fintype Role] [Fintype Label]
    (D : Label → Set Role) (three : Fin 3 ↪ Role) (hne : ¬FamilyEasy D) :
    ∃ plan : Hardness.Plan Role Label, Nonempty (Hardness.Plan.Certificate D plan) := by
  classical
  obtain ⟨J, s, p, q, hp, hq, hs, hmissing, hshape⟩ := missing_meet_of_not_familyEasy D hne
  obtain ⟨a, b, E, F, haJ, hbJ, hab, haU, hbU, haE, haF, hbE, hbF, hcover⟩ :=
    exists_hard_policy_macros D (finitePattern D) (mem_finitePattern D) J s p q hp hq hs hmissing
  exact Hardness.Plan.certificate_from_macros D three J s E F a b haJ hbJ hab haU hbU
    haE haF hbE hbF hcover hshape

/-- Main semantic hardness statement: an actual native equation is valid
exactly when the input CNF is unsatisfiable, for every non-easy finite family. -/
theorem non_easy_family_cnf_reduction [Fintype Role] [Fintype Label]
    (D : Label → Set Role) (three : Fin 3 ↪ Role) (hne : ¬FamilyEasy D) :
    ∃ plan : Hardness.Plan Role Label, ∀ formula : KFOL.Reductions.CNF,
      (∀ valuation : Hardness.Variable Role → WinnerSet Role,
        (plan.equation formula).1.eval D valuation = (plan.equation formula).2.eval D valuation) ↔
        ¬KFOL.Reductions.Satisfiable formula := by
  obtain ⟨plan, ⟨cert⟩⟩ := exists_certified_hardness_plan D three hne
  exact ⟨plan, plan.valid_iff_unsatisfiable D cert⟩

end KFOL.Policies

namespace KFOL.Policies

universe u v w x

variable {Role : Type u} {Label : Type v}

/-- Exact native-tree reduction on ordinary natural-number variable names.
The sparse naming injection preserves full, independent valuations. -/
theorem non_easy_family_nat_cnf_reduction [Fintype Role] [Fintype Label]
    (D : Label → Set Role) (three : Fin 3 ↪ Role) (code : Role ↪ ℕ) (hne : ¬FamilyEasy D) :
    ∃ plan : Hardness.Plan Role Label, ∀ formula : KFOL.Reductions.CNF,
      (∀ valuation : ℕ → WinnerSet Role,
        Term.eval D ((plan.equation formula).1.relabel (Hardness.Variable.toNat code)) valuation =
          Term.eval D ((plan.equation formula).2.relabel (Hardness.Variable.toNat code)) valuation) ↔
        ¬KFOL.Reductions.Satisfiable formula := by
  obtain ⟨plan, hplan⟩ := non_easy_family_cnf_reduction D three hne
  refine ⟨plan, fun formula => ?_⟩
  exact (Term.relabel_equation_valid_iff D (plan.equation formula).1 (plan.equation formula).2
    (Hardness.Variable.embeddingNat code)).trans (hplan formula)

end KFOL.Policies
