module

public import KFOL.Core.ProfileBudgets.Queries
public import KFOL.Core.ProfileRelations

/-! # Complete singleton profiles under simultaneous single-absorber budgets -/

@[expose] public section
namespace KFOL.Core.ProfileBudgets
universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v} {Row : Type w}
attribute [local instance] Equational.coreStructure

private def safeProfiles (b : Row → Budget Role Var) :
    Set ((Role × (Var → Bool)) → Bool) :=
  {p | ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
    (∀ r A, profile r A t = p (r,A)) ∧ Satisfies b t}

private theorem safeProfiles_closed (b : Row → Budget Role Var) :
    ProfileRelations.ChoiceClosed Prod.fst (safeProfiles b) := by
  rintro r x y ⟨s,hs,hsbound⟩ ⟨t,ht,htbound⟩
  refine ⟨choiceTerm r s t,?_,?_⟩
  · intro k A
    by_cases hrk : r = k
    · simp [profile_choice,ProfileRelations.mixedChoice,hrk,hs,ht]
    · simp [profile_choice,ProfileRelations.mixedChoice,hrk,Ne.symm hrk,hs,ht]
  · intro i
    change (WinnerSet.choice r (s.realize (b i).values) (t.realize (b i).values)).val ⊆ (b i).allowed
    exact (WinnerSet.choice_subset_union r _ _).trans (Set.union_subset (hsbound i) (htbound i))

/-- One Horn closure characterizes exact full-profile realizability under any
number of simultaneous bounds sharing one permitted atomic absorber. -/
theorem profileCondition_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (b : Row → Budget Role Var) (r₀ : Role) (habs : SingleAbsorber b r₀)
    (Φ : Role → (Var → Bool) → Bool) :
    ProfileCondition b r₀ Φ ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r A, profile r A t = Φ r A) ∧ Satisfies b t := by
  classical
  constructor
  · intro h
    let p : (Role × (Var → Bool)) → Bool := fun i => Φ i.1 i.2
    have hp : p ∈ safeProfiles b := by
      apply (ProfileRelations.ChoiceClosed.mem_iff_constraints Prod.fst
        (safeProfiles_closed b) three p).mpr
      refine ⟨?_,?_,?_⟩
      · rintro ⟨r,B⟩ hforced
        change Φ r B = true
        by_contra hn
        have hb : Φ r B = false := by cases he : Φ r B <;> simp_all
        obtain ⟨t,_,hneg,hbound⟩ := (pairCondition_iff b r₀ habs r (fun _ => true) B).mp
          (h.2.1 r _ B (h.1 r) hb)
        have ht : (fun i : Role × (Var → Bool) => profile i.1 i.2 t) ∈ safeProfiles b :=
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
        obtain ⟨t,hpa,hpb,hbound⟩ := (pairCondition_iff b r₀ habs r A B).mp (h.2.1 r A B hpos hb)
        have ht : (fun i : Role × (Var → Bool) => profile i.1 i.2 t) ∈ safeProfiles b :=
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
        obtain ⟨t,ht,hbound⟩ := (rainbowCondition_iff b r₀ habs Finset.univ A).mp (h.2.2 A hA)
        have htSafe : (fun i : Role × (Var → Bool) => profile i.1 i.2 t) ∈ safeProfiles b :=
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
      apply (pairCondition_iff b r₀ habs r A B).mpr
      exact ⟨t,by rw [hprof]; exact ha,by rw [hprof]; exact hb,hbound⟩
    · intro A hA
      apply (rainbowCondition_iff b r₀ habs Finset.univ A).mpr
      exact ⟨t,fun r _ => by rw [hprof]; exact hA r,hbound⟩

end KFOL.Core.ProfileBudgets
