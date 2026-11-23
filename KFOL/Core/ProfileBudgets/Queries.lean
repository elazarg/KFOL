module

public import KFOL.Core.ProfileBudgets.Folds

/-! # Exact simultaneous pair and rainbow tests from one Horn closure -/

@[expose] public section
namespace KFOL.Core.ProfileBudgets
universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v} [Fintype Var] {Row : Type w}
attribute [local instance] Equational.coreStructure

omit [Fintype Var] in
private theorem support_safe {b : Row → Budget Role Var} {r : Role}
    {t : CoreTerm Role Var} (hf : OwnedFold r t) (ht : Satisfies b t) :
    ∃ S : Finset Var, S.Nonempty ∧ SafeSupport b r (S : Set Var) ∧
      ∀ q A, profile q A t = true ↔
        if q = r then ∃ j ∈ S, A j = true else ∀ j ∈ S, A j = true := by
  obtain ⟨S,hS,hp,hb⟩ := hf.support
  exact ⟨S,hS,fun i => (hb _ _).mp (ht i),hp⟩

/-- Under the common-absorber hypothesis, a single Horn closure decides
positive/negative same-owner separation under every row bound at once. -/
theorem pairCondition_iff (b : Row → Budget Role Var) (r : Role)
    (habs : SingleAbsorber b r) (q : Role) (A B : Var → Bool) :
    PairCondition b r q A B ↔
      ∃ t : CoreTerm Role Var, profile q A t = true ∧ profile q B t = false ∧ Satisfies b t := by
  classical
  constructor
  · intro h
    by_cases hqr : q = r
    · subst q
      obtain ⟨j,hj,hja⟩ := (by simpa only [PairCondition,ite_true] using h :
        ∃ j ∈ greatestSupport b r {k | B k = false}, A j = true)
      let S := (greatestSupport b r {k | B k = false}).toFinset
      have hjS : j ∈ S := by simpa only [S,Set.mem_toFinset] using hj
      have hS : S.Nonempty := ⟨j,hjS⟩
      obtain ⟨t,hp,hs⟩ := exists_fold_support (Row := Row) r S hS
      refine ⟨t,?_,?_,hs b ?_⟩
      · exact (hp r A).mpr (by simpa only [ite_true] using
          (show ∃ k ∈ S, A k = true from ⟨j,hjS,hja⟩))
      · have hb : ¬profile r B t = true := by
          intro hb
          obtain ⟨k,hk,hkb⟩ := by simpa only [ite_true] using (hp r B).mp hb
          have hh := greatestSupport_subset b r {k | B k = false}
            (by simpa only [S,Set.mem_toFinset] using hk)
          change B k = false at hh
          rw [hkb] at hh
          cases hh
        cases he : profile r B t <;> simp_all
      · simpa only [S,Set.coe_toFinset] using greatestSupport_safe b r {k | B k = false}
    · obtain ⟨j,hj,hjb⟩ := by simpa only [PairCondition,ite_eq_right hqr] using h
      let S := (greatestSupport b r {k | A k = true}).toFinset
      have hjS : j ∈ S := by simpa only [S,Set.mem_toFinset] using hj
      obtain ⟨t,hp,hs⟩ := exists_fold_support (Row := Row) r S ⟨j,hjS⟩
      refine ⟨t,?_,?_,hs b ?_⟩
      · apply (hp q A).mpr
        simp only [ite_eq_right hqr]
        intro k hk
        exact greatestSupport_subset b r {k | A k = true}
          (by simpa only [S,Set.mem_toFinset] using hk)
      · have hb : ¬profile q B t = true := by
          intro hb
          have hh := (by simpa only [ite_eq_right hqr] using (hp q B).mp hb : ∀ k ∈ S, B k = true)
          have htrue := hh j hjS
          rw [hjb] at htrue
          cases htrue
        cases he : profile q B t <;> simp_all
      · simpa only [S,Set.coe_toFinset] using greatestSupport_safe b r {k | A k = true}
  · rintro ⟨t,ha,hb,ht⟩
    obtain ⟨s,hps,hsp,hsn⟩ := exists_pruning_pair r q A B t
    obtain ⟨S,hS,hSafe,hp⟩ := support_safe hps.ownedFold (hps.satisfies habs ht)
    by_cases hqr : q = r
    · subst q
      have hSB (j : Var) (hj : j ∈ S) : B j = false := by
        cases he : B j with
        | false => rfl
        | true =>
          have hh := (hp r B).mpr (by simpa only [ite_true] using ⟨j,hj,he⟩)
          rw [hsn hb] at hh
          cases hh
      obtain ⟨j,hj,hja⟩ := by simpa only [ite_true] using (hp r A).mp (hsp ha)
      simpa only [PairCondition,ite_true] using
        (show ∃ k ∈ greatestSupport b r {k | B k = false}, A k = true from
          ⟨j,safeSupport_le_greatest b r (D := {k | B k = false}) hSafe
            (fun j hj => hSB j (Finset.mem_coe.1 hj)) hj,hja⟩)
    · have hSA : (S : Set Var) ⊆ {j | A j = true} := by
        simpa only [ite_eq_right hqr,Set.subset_def,Finset.mem_coe,Set.mem_ofPred_eq] using
          (hp q A).mp (hsp ha)
      have hex : ∃ j ∈ S, B j = false := by
        by_contra hn
        have hall (j : Var) (hj : j ∈ S) : B j = true := by
          cases he : B j with
          | true => rfl
          | false => exact (hn ⟨j,hj,he⟩).elim
        have hh := (hp q B).mpr (by simpa only [ite_eq_right hqr] using hall)
        rw [hsn hb] at hh
        cases hh
      obtain ⟨j,hj,hjb⟩ := hex
      simpa only [PairCondition,ite_eq_right hqr] using
        (show ∃ j ∈ greatestSupport b r {j | A j = true}, B j = false from
          ⟨j,safeSupport_le_greatest b r hSafe hSA hj,hjb⟩)

/-- A rainbow of singleton demands is simultaneously feasible precisely when
the greatest safe support meets the distinguished owner's demanded coalition. -/
theorem rainbowCondition_iff (b : Row → Budget Role Var) (r : Role)
    (habs : SingleAbsorber b r) (J : Finset Role) (A : Role → Var → Bool) :
    RainbowCondition b r J A ↔
      ∃ t : CoreTerm Role Var, (∀ q ∈ J, profile q (A q) t = true) ∧ Satisfies b t := by
  classical
  let D : Set Var := {j | ∀ q ∈ J, q ≠ r → A q j = true}
  constructor
  · rintro ⟨j,hj,hja⟩
    let S := (greatestSupport b r D).toFinset
    have hjS : j ∈ S := by simpa only [S,Set.mem_toFinset] using hj
    obtain ⟨t,hp,hs⟩ := exists_fold_support (Row := Row) r S ⟨j,hjS⟩
    refine ⟨t,?_,hs b ?_⟩
    · intro q hq
      apply (hp q (A q)).mpr
      by_cases hqr : q = r
      · subst q
        simpa only [ite_true] using (show ∃ k ∈ S, A r k = true from ⟨j,hjS,hja hq⟩)
      · simp only [ite_eq_right hqr]
        intro k hk
        exact greatestSupport_subset b r D (by simpa only [S,Set.mem_toFinset] using hk) q hq hqr
    · simpa only [S,Set.coe_toFinset] using greatestSupport_safe b r D
  · rintro ⟨t,hp,ht⟩
    obtain ⟨s,hps,hsp⟩ := exists_pruning_rainbow r J A t hp
    obtain ⟨S,hS,hSafe,hprofile⟩ := support_safe hps.ownedFold (hps.satisfies habs ht)
    have hSD : (S : Set Var) ⊆ D := by
      intro j hj q hq hqr
      have hh : ∀ k ∈ S, A q k = true := by
        simpa only [ite_eq_right hqr] using (hprofile q (A q)).mp (hsp q hq)
      exact hh j hj
    by_cases hrJ : r ∈ J
    · obtain ⟨j,hj,hja⟩ := by
        simpa only [ite_true] using (hprofile r (A r)).mp (hsp r hrJ)
      exact ⟨j,safeSupport_le_greatest b r hSafe hSD hj,fun _ => hja⟩
    · obtain ⟨j,hj⟩ := hS
      exact ⟨j,safeSupport_le_greatest b r hSafe hSD hj,fun hh => (hrJ hh).elim⟩

end KFOL.Core.ProfileBudgets
