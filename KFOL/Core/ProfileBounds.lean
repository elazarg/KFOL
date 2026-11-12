module

public import KFOL.Definitions.ProfileBounds
public import KFOL.Core.ProfileRelations
public import KFOL.Core.RainbowPersistence
public import KFOL.Core.Protected

/-! # A closed criterion for all prescribed profiles under one winner bound

Ownerwise positive/negative profile pairs have projection or two-leaf
witnesses. Together with rainbow feasibility, these direct input conditions
characterize complete profile tables, without auxiliary presentations.
-/

@[expose] public section
namespace KFOL.Core.ProfileBounds
universe u v
variable {Role : Type u} [DecidableEq Role] {Var : Type v}
attribute [local instance] Equational.coreStructure

private theorem profile_difference (r : Role) (A B : Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (ha : profile r A t = true) (hb : profile r B t = false) :
    ∃ j, A j = true ∧ B j = false := by
  classical
  by_contra hn
  have hAB (j : Var) (hj : A j = true) : B j = true := by
    cases he : B j with
    | false => exact (hn ⟨j,hj,he⟩).elim
    | true => rfl
  have hh := profile_mono r A B hAB t ha
  rw [hb] at hh
  cases hh

private theorem pair_child (r s : Role) (A B : Var → Bool)
    (x y : Equational.Term (Equational.CoreSymbol Role) Var)
    (ha : profile r A (choiceTerm s x y) = true)
    (hb : profile r B (choiceTerm s x y) = false) :
    (profile r A x = true ∧ profile r B x = false) ∨
      (profile r A y = true ∧ profile r B y = false) := by
  by_cases hsr : s = r
  · have ha' : profile r A x = true ∨ profile r A y = true := by
      simpa only [profile_choice,ite_eq_left hsr,Bool.or_eq_true] using ha
    have hb' : profile r B x = false ∧ profile r B y = false := by
      simpa only [profile_choice,ite_eq_left hsr,Bool.or_eq_false_iff] using hb
    exact ha'.elim (fun h => Or.inl ⟨h,hb'.1⟩) (fun h => Or.inr ⟨h,hb'.2⟩)
  · have ha' : profile r A x = true ∧ profile r A y = true := by
      simpa only [profile_choice,ite_eq_right hsr,Bool.and_eq_true] using ha
    have hb' : profile r B x = false ∨ profile r B y = false := by
      simpa only [profile_choice,ite_eq_right hsr,Bool.and_eq_false_iff] using hb
    exact hb'.elim (fun h => Or.inl ⟨ha'.1,h⟩) (fun h => Or.inr ⟨ha'.2,h⟩)

omit [DecidableEq Role] in
/-- With no winner restriction, an eligible projection separates exactly the
coalitions with a positive/negative distinguishing input. -/
theorem pairSafe_univ_iff (r : Role) (A B : Var → Bool)
    (values : Var → WinnerSet Role) :
    PairSafe r A B values Set.univ ↔ ∃ j, A j = true ∧ B j = false := by
  constructor
  · rintro (⟨j,ha,hb,_⟩ | ⟨_,hdiff,_⟩ | ⟨hdiff,_⟩)
    · exact ⟨j,ha,hb⟩
    · exact hdiff
    · exact hdiff
  · rintro ⟨j,ha,hb⟩
    exact Or.inl ⟨j,ha,hb,Set.subset_univ _⟩

omit [DecidableEq Role] in
/-- An unrestricted winner budget recovers precisely monotonicity, unanimity,
and the original common-source profile condition, even at infinite arity. -/
theorem profileCondition_univ_iff_admissibleProfiles [Fintype Role]
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role) :
    ProfileCondition Φ values Set.univ ↔ AdmissibleProfiles Φ := by
  classical
  constructor
  · intro h
    refine ⟨?_,h.1,?_⟩
    · intro r A B hAB hA
      cases hB : Φ r B with
      | true => rfl
      | false =>
        obtain ⟨j,hjA,hjB⟩ := (pairSafe_univ_iff r A B values).mp (h.2.1 r A B hA hB)
        have hh := hAB j hjA
        rw [hjB] at hh
        cases hh
    · intro A hA
      obtain ⟨j,hj⟩ := (h.2.2 A hA).1
      exact ⟨j,fun r => hj r (Finset.mem_univ _)⟩
  · intro h
    refine ⟨h.top,?_,?_⟩
    · intro r A B hA hB
      apply (pairSafe_univ_iff r A B values).mpr
      by_contra hn
      have hAB (j : Var) (hj : A j = true) : B j = true := by
        cases he : B j with
        | false => exact (hn ⟨j,hj,he⟩).elim
        | true => rfl
      have hh := h.mono r A B hAB hA
      rw [hB] at hh
      cases hh
    · intro A hA
      obtain ⟨j,hj⟩ := h.common_source A hA
      refine ⟨⟨j,fun r _ => hj r⟩,Or.inl ⟨j,fun r _ => hj r,Set.subset_univ _⟩⟩

/-- Exact one-budget feasibility of a positive and a negative bit of one owner. -/
theorem pairSafe_iff (r : Role) (A B : Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) :
    PairSafe r A B values U ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        profile r A t = true ∧ profile r B t = false ∧ (t.realize values).val ⊆ U := by
  classical
  constructor
  · rintro (⟨j,ha,hb,hbound⟩ | ⟨hrU,⟨l,hlA,hlB⟩,j,hj,hjB⟩ |
      ⟨⟨l,hlA,hlB⟩,s,hsU,hsr,j,hjA,hj⟩)
    · exact ⟨.var j,ha,hb,hbound⟩
    · refine ⟨choiceTerm r (.var j) (.var l),?_,?_,?_⟩
      · simp [hlA]
      · simp [hjB,hlB]
      · change (WinnerSet.choice r (values j) (values l)).val ⊆ U
        simp only [WinnerSet.choice,hj,true_or,ite_true]
        exact Set.singleton_subset_iff.mpr hrU
    · refine ⟨choiceTerm s (.var j) (.var l),?_,?_,?_⟩
      · simp [profile_choice,hsr,hjA,hlA]
      · simp [profile_choice,hsr,hlB]
      · change (WinnerSet.choice s (values j) (values l)).val ⊆ U
        simp only [WinnerSet.choice,hj,true_or,ite_true]
        exact Set.singleton_subset_iff.mpr hsU
  · rintro ⟨t,ha,hb,hbound⟩
    induction t using induction_choice with
    | var j => exact Or.inl ⟨j,ha,hb,hbound⟩
    | choice s x y hx hy =>
      have hdiff := profile_difference r A B (choiceTerm s x y) ha hb
      by_cases habs : x.realize values = WinnerSet.singleton s ∨
          y.realize values = WinnerSet.singleton s
      · have hparent : (choiceTerm s x y).realize values = WinnerSet.singleton s := by
          change WinnerSet.choice s (x.realize values) (y.realize values) = _
          simp [WinnerSet.choice,habs]
        have hsU : s ∈ U := hbound (by rw [hparent]; rfl)
        by_cases hsr : s = r
        · subst s
          have hb' : profile r B x = false ∧ profile r B y = false := by
            simpa only [profile_choice,ite_true,Bool.or_eq_false_iff] using hb
          have hex : ∃ j, values j = WinnerSet.singleton r ∧ B j = false := by
            rcases habs with hxe | hye
            · have hat := (winnerSet_eq_singleton_iff_profile x r values).mp hxe
              obtain ⟨j,hj,hjB⟩ := profile_difference r _ B x hat hb'.1
              exact ⟨j,of_decide_eq_true hj,hjB⟩
            · have hat := (winnerSet_eq_singleton_iff_profile y r values).mp hye
              obtain ⟨j,hj,hjB⟩ := profile_difference r _ B y hat hb'.2
              exact ⟨j,of_decide_eq_true hj,hjB⟩
          exact Or.inr (Or.inl ⟨hsU,hdiff,hex⟩)
        · have ha' : profile r A x = true ∧ profile r A y = true := by
            simpa only [profile_choice,ite_eq_right hsr,Bool.and_eq_true] using ha
          have hex : ∃ j, A j = true ∧ values j = WinnerSet.singleton s := by
            rcases habs with hxe | hye
            · have hat := (winnerSet_eq_singleton_iff_profile x s values).mp hxe
              obtain ⟨j,hjA,hj⟩ := profile_common_source_two r s (Ne.symm hsr) A _ x ha'.1 hat
              exact ⟨j,hjA,of_decide_eq_true hj⟩
            · have hat := (winnerSet_eq_singleton_iff_profile y s values).mp hye
              obtain ⟨j,hjA,hj⟩ := profile_common_source_two r s (Ne.symm hsr) A _ y ha'.2 hat
              exact ⟨j,hjA,of_decide_eq_true hj⟩
          exact Or.inr (Or.inr ⟨hdiff,s,hsU,hsr,hex⟩)
      · have hunion : (choiceTerm s x y).realize values =
            (x.realize values).union (y.realize values) := by
          change WinnerSet.choice s (x.realize values) (y.realize values) = _
          simp [WinnerSet.choice,habs]
        have hxbound : (x.realize values).val ⊆ U := by
          intro k hk
          apply hbound
          rw [hunion]
          exact Or.inl hk
        have hybound : (y.realize values).val ⊆ U := by
          intro k hk
          apply hbound
          rw [hunion]
          exact Or.inr hk
        rcases pair_child r s A B x y ha hb with ⟨hxa,hxb⟩ | ⟨hya,hyb⟩
        · exact hx hxa hxb hxbound
        · exact hy hya hyb hybound

/-- The direct rainbow input test is exactly bounded positive-profile feasibility. -/
theorem rainbowSafe_iff (J : Finset Role) (A : Role → Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) :
    RainbowSafe J A values U ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r ∈ J, profile r (A r) t = true) ∧ (t.realize values).val ⊆ U :=
  (rainbow_budget_iff J A values U).symm

/-- Reflexivity of the explicitly specified one-budget coalition preorder. -/
theorem coalitionLE_refl (values : Var → WinnerSet Role) (U : Set Role)
    (r : Role) (A : Var → Bool) : CoalitionLE values U r A A := by
  rintro h
  obtain ⟨t,ha,hb,_⟩ := (pairSafe_iff r A A values U).mp h
  rw [ha] at hb
  cases hb

/-- Transitivity of the explicitly specified one-budget coalition preorder. -/
theorem coalitionLE_trans (values : Var → WinnerSet Role) (U : Set Role)
    (r : Role) {A B C : Var → Bool}
    (hAB : CoalitionLE values U r A B) (hBC : CoalitionLE values U r B C) :
    CoalitionLE values U r A C := by
  rintro h
  obtain ⟨t,ha,hc,hbound⟩ := (pairSafe_iff r A C values U).mp h
  cases hb : profile r B t with
  | false => exact hAB ((pairSafe_iff r A B values U).mpr ⟨t,ha,hb,hbound⟩)
  | true => exact hBC ((pairSafe_iff r B C values U).mpr ⟨t,hb,hc,hbound⟩)

private def safeProfiles (values : Var → WinnerSet Role) (U : Set Role) :
    Set ((Role × (Var → Bool)) → Bool) :=
  {p | ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
    (∀ r A, profile r A t = p (r,A)) ∧ (t.realize values).val ⊆ U}

private theorem safeProfiles_closed (values : Var → WinnerSet Role) (U : Set Role) :
    ProfileRelations.ChoiceClosed Prod.fst (safeProfiles values U) := by
  rintro r x y ⟨s,hs,hsbound⟩ ⟨t,ht,htbound⟩
  refine ⟨choiceTerm r s t,?_,?_⟩
  · intro k A
    by_cases hrk : r = k
    · simp [profile_choice,ProfileRelations.mixedChoice,hrk,hs,ht]
    · simp [profile_choice,ProfileRelations.mixedChoice,hrk,Ne.symm hrk,hs,ht]
  · change (WinnerSet.choice r (s.realize values) (t.realize values)).val ⊆ U
    exact (WinnerSet.choice_subset_union r _ _).trans (Set.union_subset hsbound htbound)

/-- A prescribed full profile tuple fits one winner budget exactly when the
three direct input conditions hold. No auxiliary relation is part of the test. -/
theorem profileCondition_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role) (U : Set Role) :
    ProfileCondition Φ values U ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r A, profile r A t = Φ r A) ∧ (t.realize values).val ⊆ U := by
  classical
  constructor
  · intro h
    let p : (Role × (Var → Bool)) → Bool := fun i => Φ i.1 i.2
    have hp : p ∈ safeProfiles values U := by
      apply (ProfileRelations.ChoiceClosed.mem_iff_constraints Prod.fst
        (safeProfiles_closed values U) three p).mpr
      refine ⟨?_,?_,?_⟩
      · rintro ⟨r,B⟩ hforced
        change Φ r B = true
        by_contra hn
        have hb : Φ r B = false := by cases he : Φ r B <;> simp_all
        obtain ⟨t,_,hneg,hbound⟩ := (pairSafe_iff r (fun _ => true) B values U).mp
          (h.2.1 r _ B (h.1 r) hb)
        have ht : (fun i : Role × (Var → Bool) => profile i.1 i.2 t) ∈ safeProfiles values U :=
          ⟨t,fun _ _ => rfl,hbound⟩
        have hh := hforced _ ht
        change profile r B t = true at hh
        rw [hneg] at hh
        cases hh
      · rintro ⟨r,A⟩ ⟨s,B⟩ ho himp hpos
        change r = s at ho
        subst s
        change Φ r A = true at hpos
        change Φ r B = true
        by_contra hn
        have hb : Φ r B = false := by cases he : Φ r B <;> simp_all
        obtain ⟨t,hpa,hpb,hbound⟩ := (pairSafe_iff r A B values U).mp (h.2.1 r A B hpos hb)
        have ht : (fun i : Role × (Var → Bool) => profile i.1 i.2 t) ∈ safeProfiles values U :=
          ⟨t,fun _ _ => rfl,hbound⟩
        have hh := himp _ ht hpa
        change profile r B t = true at hh
        rw [hpb] at hh
        cases hh
      · intro S hr hforbidden hall
        have choose_coalition (r : Role) : ∃ A : Var → Bool,
            Φ r A = true ∧ ∀ B, (r,B) ∈ S → A = B := by
          by_cases hex : ∃ A : Var → Bool, (r,A) ∈ S
          · obtain ⟨A,hA⟩ := hex
            refine ⟨A,hall (r,A) hA,?_⟩
            intro B hB
            exact congrArg Prod.snd (hr (r,A) hA (r,B) hB rfl)
          · refine ⟨fun _ => true,h.1 r,?_⟩
            intro B hB
            exact (hex ⟨B,hB⟩).elim
        choose A hA hmatch using choose_coalition
        obtain ⟨t,ht,hbound⟩ := (rainbowSafe_iff Finset.univ A values U).mp (h.2.2 A hA)
        have htSafe : (fun i : Role × (Var → Bool) => profile i.1 i.2 t) ∈ safeProfiles values U :=
          ⟨t,fun _ _ => rfl,hbound⟩
        apply hforbidden _ htSafe
        rintro ⟨r,B⟩ hB
        change profile r B t = true
        rw [← hmatch r B hB]
        exact ht r (Finset.mem_univ _)
    exact hp
  · rintro ⟨t,hprof,hbound⟩
    refine ⟨?_,?_,?_⟩
    · intro r
      rw [← hprof]
      exact (admissibleProfiles_profile t).top r
    · intro r A B ha hb
      apply (pairSafe_iff r A B values U).mpr
      exact ⟨t,by rw [hprof]; exact ha,by rw [hprof]; exact hb,hbound⟩
    · intro A hA
      apply (rainbowSafe_iff Finset.univ A values U).mpr
      exact ⟨t,fun r _ => by rw [hprof]; exact hA r,hbound⟩

end KFOL.Core.ProfileBounds
