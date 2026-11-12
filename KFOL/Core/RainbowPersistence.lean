module

public import KFOL.Core.ProfileSynthesis
public import KFOL.Algebra.ChoiceSupport

/-! # Exact one-budget witnesses for rainbow positive profiles

A single upper winner bound needs only a common projection or a two-leaf
owned choice. The resulting closed conditions also characterize every
universal rainbow-profile-to-membership implication. No finite role or
variable assumption is needed.
-/

@[expose] public section
namespace KFOL.Core
universe u v
variable {Role : Type u} [DecidableEq Role] {Var : Type v}
attribute [local instance] Equational.coreStructure

private theorem rainbow_common_variable (J : Finset Role) (A : Role → Var → Bool)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (hp : ∀ r ∈ J, profile r (A r) t = true) :
    ∃ j, ∀ r ∈ J, A r j = true := by
  classical
  obtain ⟨j,hj⟩ := profile_common_source (fun r : J => r.val) Subtype.val_injective
    (fun r : J => A r.val) t (fun r => hp r.val r.property)
  exact ⟨j,fun r hr => hj ⟨r,hr⟩⟩

private theorem rainbow_singleton_source (J : Finset Role) (A : Role → Var → Bool)
    (values : Var → WinnerSet Role) (s : Role)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (he : t.realize values = WinnerSet.singleton s)
    (hp : ∀ r ∈ J, r ≠ s → profile r (A r) t = true) :
    ∃ j, values j = WinnerSet.singleton s ∧ ∀ r ∈ J, r ≠ s → A r j = true := by
  classical
  let I := insert s J
  let B : I → Var → Bool := fun r =>
    if r.val = s then fun j => decide (values j = WinnerSet.singleton s) else A r.val
  have hprofiles (r : I) : profile r.val (B r) t = true := by
    by_cases hrs : r.val = s
    · simpa only [B,hrs,ite_true] using (winnerSet_eq_singleton_iff_profile t s values).mp he
    · have hrJ : r.val ∈ J := (Finset.mem_insert.mp r.property).resolve_left hrs
      simpa only [B,hrs,ite_false] using hp r.val hrJ hrs
  obtain ⟨j,hj⟩ := profile_common_source (fun r : I => r.val) Subtype.val_injective B t hprofiles
  refine ⟨j,?_,?_⟩
  · have hh := hj ⟨s,Finset.mem_insert_self _ _⟩
    simpa only [B,ite_true,decide_eq_true_eq] using hh
  · intro r hr hrs
    have hh := hj ⟨r,Finset.mem_insert_of_mem hr⟩
    simpa only [B,hrs,ite_false] using hh

private theorem rainbow_choice_child (J : Finset Role) (A : Role → Var → Bool)
    (r : Role) (s t : Equational.Term (Equational.CoreSymbol Role) Var)
    (hp : ∀ k ∈ J, profile k (A k) (choiceTerm r s t) = true) :
    (∀ k ∈ J, profile k (A k) s = true) ∨
      (∀ k ∈ J, profile k (A k) t = true) := by
  by_cases hr : r ∈ J
  · have hh : profile r (A r) s = true ∨ profile r (A r) t = true := by
      simpa only [profile_choice,ite_true,Bool.or_eq_true] using hp r hr
    have other (k : Role) (hk : k ∈ J) (hkr : k ≠ r) :
        profile k (A k) s = true ∧ profile k (A k) t = true := by
      simpa only [profile_choice,ite_eq_right (Ne.symm hkr),Bool.and_eq_true] using hp k hk
    rcases hh with hs | ht
    · left
      intro k hk
      by_cases hkr : k = r
      · simpa only [hkr] using hs
      · exact (other k hk hkr).1
    · right
      intro k hk
      by_cases hkr : k = r
      · simpa only [hkr] using ht
      · exact (other k hk hkr).2
  · left
    intro k hk
    have hrk : r ≠ k := fun he => hr (he.symm ▸ hk)
    have hh : profile k (A k) s = true ∧ profile k (A k) t = true := by
      simpa only [profile_choice,ite_eq_right hrk,Bool.and_eq_true] using hp k hk
    exact hh.1

/-- A single winner upper bound with rainbow positive profiles has a
projection witness or a two-variable owned-choice witness. -/
theorem rainbow_budget_iff (J : Finset Role) (A : Role → Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role) :
    (∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ r ∈ J, profile r (A r) t = true) ∧ (t.realize values).val ⊆ U) ↔
      (∃ j, ∀ r ∈ J, A r j = true) ∧
      ((∃ j, (∀ r ∈ J, A r j = true) ∧ (values j).val ⊆ U) ∨
        ∃ s ∈ J, s ∈ U ∧ ∃ j, values j = WinnerSet.singleton s ∧
          ∀ r ∈ J, r ≠ s → A r j = true) := by
  classical
  constructor
  · rintro ⟨t,hp,hbound⟩
    refine ⟨rainbow_common_variable J A t hp,?_⟩
    induction t using induction_choice with
    | var j => exact Or.inl ⟨j,hp,hbound⟩
    | choice r s t hs ht =>
      have hother (k : Role) (hk : k ∈ J) (hkr : k ≠ r) :
          profile k (A k) s = true ∧ profile k (A k) t = true := by
        simpa only [profile_choice,ite_eq_right (Ne.symm hkr),Bool.and_eq_true] using hp k hk
      by_cases habs : s.realize values = WinnerSet.singleton r ∨
          t.realize values = WinnerSet.singleton r
      · have hparent : (choiceTerm r s t).realize values = WinnerSet.singleton r := by
          change WinnerSet.choice r (s.realize values) (t.realize values) = _
          simp [WinnerSet.choice,habs]
        have hrU : r ∈ U := hbound (by rw [hparent]; rfl)
        have hsource : ∃ j, values j = WinnerSet.singleton r ∧
            ∀ k ∈ J, k ≠ r → A k j = true := by
          rcases habs with hsatom | htatom
          · exact rainbow_singleton_source J A values r s hsatom
              (fun k hk hkr => (hother k hk hkr).1)
          · exact rainbow_singleton_source J A values r t htatom
              (fun k hk hkr => (hother k hk hkr).2)
        obtain ⟨j,hj,hcommon⟩ := hsource
        by_cases hrJ : r ∈ J
        · exact Or.inr ⟨r,hrJ,hrU,j,hj,hcommon⟩
        · left
          refine ⟨j,fun k hk => hcommon k hk (fun he => hrJ (he ▸ hk)),?_⟩
          intro k hk
          have hkr : k = r := by simpa only [hj,WinnerSet.val_singleton,Set.mem_singleton_iff] using hk
          exact hkr ▸ hrU
      · have hunion : (choiceTerm r s t).realize values =
            (s.realize values).union (t.realize values) := by
          change WinnerSet.choice r (s.realize values) (t.realize values) = _
          simp [WinnerSet.choice,habs]
        have hsbound : (s.realize values).val ⊆ U := by
          intro k hk
          apply hbound
          rw [hunion]
          exact Or.inl hk
        have htbound : (t.realize values).val ⊆ U := by
          intro k hk
          apply hbound
          rw [hunion]
          exact Or.inr hk
        rcases rainbow_choice_child J A r s t hp with hsp | htp
        · exact hs hsp hsbound
        · exact ht htp htbound
  · rintro ⟨⟨l,hl⟩,⟨j,hj,hbound⟩ | ⟨s,hsJ,hsU,j,hjs,hj⟩⟩
    · exact ⟨.var j,hj,hbound⟩
    · refine ⟨choiceTerm s (.var j) (.var l),?_,?_⟩
      · intro r hr
        by_cases hsr : s = r
        · simp [profile_choice,hsr,hl r hr]
        · simp [profile_choice,hsr,hj r hr (Ne.symm hsr),hl r hr]
      · change (WinnerSet.choice s (values j) (values l)).val ⊆ U
        simp only [WinnerSet.choice,hjs,true_or,ite_true]
        exact Set.singleton_subset_iff.mpr hsU

/-- Whenever a rainbow demand and one upper budget are realizable, a projection
or a single owned choice between two variable leaves already realizes them. -/
theorem rainbow_budget_small_witness (J : Finset Role) (A : Role → Var → Bool)
    (values : Var → WinnerSet Role) (U : Set Role)
    (h : ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ r ∈ J, profile r (A r) t = true) ∧ (t.realize values).val ⊆ U) :
    (∃ j, (∀ r ∈ J, A r j = true) ∧ (values j).val ⊆ U) ∨
      ∃ s j l, (∀ r ∈ J,
        profile r (A r) (choiceTerm s (.var j) (.var l)) = true) ∧
        ((choiceTerm s (.var j) (.var l)).realize values).val ⊆ U := by
  classical
  obtain ⟨⟨l,hl⟩,hp | ⟨s,hsJ,hsU,j,hjs,hj⟩⟩ :=
    (rainbow_budget_iff J A values U).mp h
  · exact Or.inl hp
  · right
    refine ⟨s,j,l,?_,?_⟩
    · intro r hr
      by_cases hsr : s = r
      · simp [profile_choice,hsr,hl r hr]
      · simp [profile_choice,hsr,hj r hr (Ne.symm hsr),hl r hr]
    · change (WinnerSet.choice s (values j) (values l)).val ⊆ U
      simp only [WinnerSet.choice,hjs,true_or,ite_true]
      exact Set.singleton_subset_iff.mpr hsU

omit [DecidableEq Role] in
private theorem subset_ne_iff (B : WinnerSet Role) (k : Role) :
    B.val ⊆ {r | r ≠ k} ↔ k ∉ B.val := by
  constructor
  · intro h hk
    exact h hk rfl
  · intro h r hr he
    exact h (he ▸ hr)

/-- Exact closed conditions for a universal rainbow-profile-to-membership law. -/
theorem rainbow_membership_iff (J : Finset Role) (A : Role → Var → Bool)
    (k : Role) (values : Var → WinnerSet Role) :
    (∀ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ r ∈ J, profile r (A r) t = true) → k ∈ (t.realize values).val) ↔
      (¬∃ j, ∀ r ∈ J, A r j = true) ∨
      ((∀ j, (∀ r ∈ J, A r j = true) → k ∈ (values j).val) ∧
        ∀ s ∈ J, s ≠ k → ¬∃ j, values j = WinnerSet.singleton s ∧
          ∀ r ∈ J, r ≠ s → A r j = true) := by
  classical
  have hbudget := rainbow_budget_iff J A values {r | r ≠ k}
  constructor
  · intro h
    have hbad : ¬∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r ∈ J, profile r (A r) t = true) ∧ (t.realize values).val ⊆ {r | r ≠ k} := by
      rintro ⟨t,hp,hb⟩
      exact hb (h t hp) rfl
    have hn := fun hh => hbad (hbudget.mpr hh)
    by_cases hc : ∃ j, ∀ r ∈ J, A r j = true
    · right
      refine ⟨?_,?_⟩
      · intro j hj
        by_contra hk
        exact hn ⟨hc,Or.inl ⟨j,hj,(subset_ne_iff _ _).mpr hk⟩⟩
      · intro s hs hsk hj
        exact hn ⟨hc,Or.inr ⟨s,hs,hsk,hj⟩⟩
    · exact Or.inl hc
  · intro h t hp
    by_contra hk
    obtain ⟨hc,hw⟩ := hbudget.mp ⟨t,hp,(subset_ne_iff _ _).mpr hk⟩
    rcases h with hn | ⟨hcommon,hblock⟩
    · exact hn hc
    · rcases hw with ⟨j,hj,hbound⟩ | ⟨s,hs,hsk,hj⟩
      · exact hbound (hcommon j hj) rfl
      · exact hblock s hs hsk hj

end KFOL.Core
