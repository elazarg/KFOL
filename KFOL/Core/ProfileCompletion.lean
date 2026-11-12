module

public import KFOL.Core.ProfileQueries
public import KFOL.Reset.Public

/-! # Exact one-point completion of a full profile tuple

Reset preserves every singleton profile and can add any eligible whole input
to an ambiguous output. Thus whole-input coverage is the only additional
provenance condition once bounded profiles and atomic compatibility hold.
-/

@[expose] public section
namespace KFOL.Core.ProfileBounds
universe u v
variable {Role : Type u} [DecidableEq Role] {Var : Type v}
attribute [local instance] Equational.coreStructure

private theorem profiles_eq_of_singletons (three : Fin 3 ↪ Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var)
    (h : ∀ values : Var → WinnerSet Role, ∀ r,
      s.realize values = WinnerSet.singleton r ↔ t.realize values = WinnerSet.singleton r) :
    ∀ r A, profile r A s = profile r A t := by
  classical
  intro r A
  obtain ⟨q,hqr⟩ : ∃ q : Role, q ≠ r := by
    by_cases hr : three 0 = r
    · exact ⟨three 1,fun he => by have := three.injective (he.trans hr.symm); omega⟩
    · exact ⟨three 0,hr⟩
  let values : Var → WinnerSet Role := fun j => if A j then WinnerSet.singleton r else WinnerSet.singleton q
  have hbits : (fun j => decide (values j = WinnerSet.singleton r)) = A := by
    funext j
    cases ha : A j with
    | true => simp [values,ha]
    | false =>
      have hn : WinnerSet.singleton q ≠ WinnerSet.singleton r := by
        intro he
        have : q ∈ (WinnerSet.singleton r).val := he ▸ (show q ∈ (WinnerSet.singleton q).val from rfl)
        exact hqr this
      simp [values,ha,hn]
  apply Bool.eq_iff_iff.mpr
  have hh := h values r
  rw [winnerSet_eq_singleton_iff_profile,winnerSet_eq_singleton_iff_profile,hbits] at hh
  exact hh

/-- Reset against any core term preserves all profiles of the second operand. -/
theorem exists_profile_reset [Fintype Role] (three : Fin 3 ↪ Role)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) :
    ∃ e : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ r A, profile r A e = profile r A t) ∧
      ∀ values : Var → WinnerSet Role,
        e.realize values = (s.realize values).reset (t.realize values) := by
  classical
  let n := Reset.Term.resetTerm three Finset.univ.toList
    (Equational.Core.decode s) (Equational.Core.decode t)
  have hn : n.IsCore := Reset.Term.isCore_resetTerm three _ _ _
    (Equational.Core.isCore_decode s) (Equational.Core.isCore_decode t)
  let e := Equational.Core.encode n hn
  have he (values : Var → WinnerSet Role) :
      e.realize values = (s.realize values).reset (t.realize values) := by
    rw [← Equational.Core.eval_decode e values,Equational.Core.decode_encode]
    rw [Reset.Term.eval_resetTerm three _ (by simp)]
    rw [Equational.Core.eval_decode,Equational.Core.eval_decode]
  refine ⟨e,profiles_eq_of_singletons three e t ?_,he⟩
  intro values r
  rw [he,WinnerSet.reset_eq_singleton]

private theorem reset_add_source [Fintype Role] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role)
    (U : Set Role) (k : Role)
    (hatom : ∀ r, Φ r (atomicBits r values) = true → r = k)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (ht : ∀ r A, profile r A t = Φ r A) (htb : (t.realize values).val ⊆ U)
    (j : Var) (hjk : k ∈ (values j).val) (hjb : (values j).val ⊆ U) :
    ∃ e : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ r A, profile r A e = Φ r A) ∧ (e.realize values).val ⊆ U ∧
      (t.realize values).val ⊆ (e.realize values).val ∧ k ∈ (e.realize values).val := by
  classical
  obtain ⟨e,hep,hee⟩ := exists_profile_reset three (.var j) t
  have he : e.realize values = (values j).reset (t.realize values) := hee values
  have hcontain : (t.realize values).val ⊆ (e.realize values).val := by
    intro a ha
    rw [he]
    exact (WinnerSet.mem_reset _ _ _).mpr (Or.inl ha)
  refine ⟨e,fun r A => (hep r A).trans (ht r A),?_,hcontain,?_⟩
  · intro a ha
    rw [he] at ha
    rcases (WinnerSet.mem_reset _ _ _).mp ha with ha | ⟨_,ha⟩
    · exact htb ha
    · exact hjb ha
  · by_cases hamb : (t.realize values).Ambiguous
    · rw [he]
      exact (WinnerSet.mem_reset _ _ _).mpr (Or.inr ⟨hamb,hjk⟩)
    · obtain ⟨r,hr⟩ : ∃ r, t.realize values = WinnerSet.singleton r := by
        simpa only [WinnerSet.Ambiguous,not_forall,not_not] using hamb
      have hp : profile r (atomicBits r values) t = true :=
        (winnerSet_eq_singleton_iff_profile t r values).mp hr
      rw [ht] at hp
      exact hcontain (by simp [hr,hatom r hp])

/-- A full profile tuple can retain a given winner under one upper bound
exactly when an eligible whole input carries it and no prescribed atomic
output excludes it. -/
theorem profile_query_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role)
    (U : Set Role) (k : Role) :
    (ProfileCondition Φ values U ∧
      (∃ j, k ∈ (values j).val ∧ (values j).val ⊆ U) ∧
      (∀ r, Φ r (atomicBits r values) = true → r = k)) ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r A, profile r A t = Φ r A) ∧
        (t.realize values).val ⊆ U ∧ k ∈ (t.realize values).val := by
  classical
  constructor
  · rintro ⟨hbound,⟨j,hjk,hjb⟩,hatom⟩
    obtain ⟨t,ht,htb⟩ := (profileCondition_iff three Φ values U).mp hbound
    obtain ⟨e,hep,heb,_,hek⟩ := reset_add_source three Φ values U k hatom
      t ht htb j hjk hjb
    exact ⟨e,hep,heb,hek⟩
  · rintro ⟨t,ht,htb,htk⟩
    refine ⟨(profileCondition_iff three Φ values U).mpr ⟨t,ht,htb⟩,
      whole_input_provenance_bounded t values U htb k htk,?_⟩
    intro r hp
    have he : t.realize values = WinnerSet.singleton r :=
      (winnerSet_eq_singleton_iff_profile t r values).mpr (by rwa [ht])
    have : k = r := by simpa [he] using htk
    exact this.symm

/-- The direct one-point condition characterizes a complete profile tuple
with one exact prescribed winner value. -/
theorem onePointCondition_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role)
    (target : WinnerSet Role) :
    OnePointCondition Φ values target ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r A, profile r A t = Φ r A) ∧ t.realize values = target := by
  classical
  constructor
  · rintro ⟨hbound,hcompat,hcover⟩
    obtain ⟨t,ht,htb⟩ := (profileCondition_iff three Φ values target.val).mp hbound
    have build (K : Finset Role) :
        ∃ e : Equational.Term (Equational.CoreSymbol Role) Var,
          (∀ r A, profile r A e = Φ r A) ∧ (e.realize values).val ⊆ target.val ∧
          ∀ k ∈ K, k ∈ target.val → k ∈ (e.realize values).val := by
      induction K using Finset.induction_on with
      | empty => exact ⟨t,ht,htb,by simp⟩
      | @insert k K hk ih =>
        obtain ⟨e,hep,heb,heK⟩ := ih
        by_cases hkT : k ∈ target.val
        · obtain ⟨j,hjk,hjb⟩ := hcover k hkT
          have hatom (r : Role) (hr : Φ r (atomicBits r values) = true) : r = k := by
            have heq := (hcompat r).mp hr
            have : k = r := by simpa [heq] using hkT
            exact this.symm
          obtain ⟨f,hfp,hfb,hef,hfk⟩ := reset_add_source three Φ values target.val k hatom
            e hep heb j hjk hjb
          refine ⟨f,hfp,hfb,?_⟩
          intro a ha haT
          rcases Finset.mem_insert.mp ha with heq | haK
          · exact heq ▸ hfk
          · exact hef (heK a haK haT)
        · refine ⟨e,hep,heb,?_⟩
          intro a ha haT
          rcases Finset.mem_insert.mp ha with heq | haK
          · exact (hkT (heq ▸ haT)).elim
          · exact heK a haK haT
    obtain ⟨e,hep,heb,heall⟩ := build Finset.univ
    refine ⟨e,hep,Subtype.ext (Set.Subset.antisymm heb ?_)⟩
    intro k hk
    exact heall k (Finset.mem_univ k) hk
  · rintro ⟨t,ht,he⟩
    refine ⟨(profileCondition_iff three Φ values target.val).mpr
      ⟨t,ht,by rw [he]⟩,?_,?_⟩
    · intro r
      rw [← ht]
      exact (winnerSet_eq_singleton_iff_profile t r values).symm.trans (by rw [he])
    · intro k hk
      exact whole_input_provenance_bounded t values target.val (by rw [he]) k (by rwa [he])

end KFOL.Core.ProfileBounds
