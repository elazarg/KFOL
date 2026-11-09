module

public import KFOL.Complexity.OwnerLanguage

/-! # Certified tractable branches of owner-relative equation validity -/
@[expose] public section
namespace KFOL.Complexity.OwnerObservationFrontend
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Complexity.OwnerLanguage
variable {Role : Type} [Fintype Role] [DecidableEq Role]

def implicationB (observer : Role) (equation : Owner.Term Role ℕ × Owner.Term Role ℕ) : Bool :=
  Owner.coversB (equation.1.guards observer) (equation.2.guards observer)

theorem implicationB_polyTime (observer : Role) : ComputableInPolyTime
    (implicationB observer) equationEncoding encBool := by
  have ha := FiniteTermMachines.arguments_polyTime (σ := Owner.Symbol Role)
  have hl := (OwnerObservationCompiler.observation_guards_polyTime observer).comp ((fst _ _).comp ha)
  have hr := (OwnerObservationCompiler.observation_guards_polyTime observer).comp ((snd _ _).comp ha)
  exact OwnerTermFrontend.covers_polyTime.comp (hl.prod hr)

theorem equationB_polyTime (observer : Role) : ComputableInPolyTime
    (fun equation : Owner.Term Role ℕ × Owner.Term Role ℕ =>
      Owner.Term.equationB observer equation.1 equation.2) equationEncoding encBool := by
  have ha := FiniteTermMachines.arguments_polyTime (σ := Owner.Symbol Role)
  have hl := (OwnerObservationCompiler.observation_guards_polyTime observer).comp ((fst _ _).comp ha)
  have hr := (OwnerObservationCompiler.observation_guards_polyTime observer).comp ((snd _ _).comp ha)
  exact bool_and' (OwnerTermFrontend.covers_polyTime.comp (hl.prod hr))
    (OwnerTermFrontend.covers_polyTime.comp (hr.prod hl))

/-- Turn a complete checker on legal source trees into a checker of the
whole binary language; malformed syntax and unselected owners are rejected. -/
theorem language_mem_P_of_checker (owners : Finset Role)
    (relation : WinnerSet Role → WinnerSet Role → Prop)
    (test : Owner.Term Role ℕ × Owner.Term Role ℕ → Bool)
    (runtime : ComputableInPolyTime test equationEncoding encBool)
    (correct : ∀ equation, equation.1.OwnersIn (fun r => r ∈ owners) →
      equation.2.OwnersIn (fun r => r ∈ owners) →
      (test equation = true ↔ ∀ valuation : ℕ → WinnerSet Role,
        relation (equation.1.eval valuation) (equation.2.eval valuation))) :
    Owner.Language owners relation ∈ Cslib.Complexity.P encBits := by
  let check := fun equation => legalB owners equation && test equation
  have hruntime : ComputableInPolyTime check equationEncoding encBool :=
    bool_and' (legalB_polyTime owners) runtime
  have hcorrect : ∀ equation, check equation = true ↔ Owner.Valid owners relation equation := by
    intro equation
    simp only [check,Bool.and_eq_true,legalB,ownersB_iff,Owner.Valid]
    constructor
    · rintro ⟨⟨hl,hr⟩,ht⟩
      exact ⟨hl,hr,(correct equation hl hr).mp ht⟩
    · rintro ⟨hl,hr,ht⟩
      exact ⟨⟨hl,hr⟩,(correct equation hl hr).mpr ht⟩
  exact ⟨checkWordWith check,checkWordWith_polyTime check hruntime,
    fun word => (checkWordWith_iff _ _ hcorrect word).symm⟩

/-- At most one non-observer owner gives a native polynomial implication
checker on all encoded original equations. -/
theorem implication_language_mem_P (three : Fin 3 ↪ Role) (owners : Finset Role)
    (observer : Role) (small : (owners.erase observer).card ≤ 1) :
    Owner.Language owners (fun x y => observer ∈ x.val → observer ∈ y.val) ∈
      Cslib.Complexity.P encBits := by
  obtain ⟨other,hko,hallowed⟩ := Owner.exists_observation_owner three owners observer small
  obtain ⟨background,hbk,hbo⟩ := exists_role_outside_pair three observer other
  apply language_mem_P_of_checker owners _ (implicationB observer) (implicationB_polyTime observer)
  rintro ⟨left,right⟩ hl hr
  rw [implicationB,Owner.coversB_correct]
  exact left.observation_implication_iff right observer other background hko hbk.symm hbo.symm
    (hl.mono hallowed) (hr.mono hallowed)

/-- The same relative-owner bound decides observational equivalence. -/
theorem equivalence_language_mem_P (three : Fin 3 ↪ Role) (owners : Finset Role)
    (observer : Role) (small : (owners.erase observer).card ≤ 1) :
    Owner.Language owners (fun x y => observer ∈ x.val ↔ observer ∈ y.val) ∈
      Cslib.Complexity.P encBits := by
  obtain ⟨other,hko,hallowed⟩ := Owner.exists_observation_owner three owners observer small
  obtain ⟨background,hbk,hbo⟩ := exists_role_outside_pair three observer other
  apply language_mem_P_of_checker owners _
    (fun equation => Owner.Term.equationB observer equation.1 equation.2) (equationB_polyTime observer)
  rintro ⟨left,right⟩ hl hr
  exact left.observationB_correct right observer other background hko hbk.symm hbo.symm
    (hl.mono hallowed) (hr.mono hallowed)

/-- Full equality for zero or one selected owners uses one outsider table. -/
theorem equality_language_mem_P (three : Fin 3 ↪ Role) (owners : Finset Role)
    (small : owners.card ≤ 1) : Owner.Language owners Eq ∈ Cslib.Complexity.P encBits := by
  obtain ⟨owner,hallowed⟩ : ∃ owner : Role, ∀ r ∈ owners, r = owner := by
    by_cases empty : owners = ∅
    · exact ⟨three 0,by simp [empty]⟩
    · obtain ⟨owner,hm⟩ := Finset.nonempty_iff_ne_empty.mpr empty
      exact ⟨owner,fun r hr => Finset.card_le_one.mp small r hr owner hm⟩
  obtain ⟨observer,hne⟩ : ∃ observer : Role, observer ≠ owner := by
    by_cases he : owner = three 0
    · exact ⟨three 1,by simpa only [he] using three.injective.ne (show (1 : Fin 3) ≠ 0 by decide)⟩
    · exact ⟨three 0,Ne.symm he⟩
  apply language_mem_P_of_checker owners Eq
    (fun equation => Owner.Term.equationB observer equation.1 equation.2) (equationB_polyTime observer)
  rintro ⟨left,right⟩ hl hr
  exact Owner.Term.equationB_correct three owner observer hne left right
    (hl.mono hallowed) (hr.mono hallowed)

end KFOL.Complexity.OwnerObservationFrontend
