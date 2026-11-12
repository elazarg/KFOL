module

public import KFOL.Core.RainbowPersistence
public import Mathlib.Tactic.FinCases

/-! # Joint positive profiles force winner persistence

Two owners' positive coalitions can force a winner at an ambiguous valuation.
The resulting constraint need not follow from the separate owner profiles.
-/

@[expose] public section
namespace KFOL.Core

universe u v
variable {Role : Type u} [DecidableEq Role] {Var : Type v}
attribute [local instance] Equational.coreStructure

/-- Two positive profiles preserve the first owner's membership when their
common variables carry that owner, and the first coalition avoids all atomic
inputs of the second owner. -/
theorem winner_of_two_positive_profiles (r s : Role) (hrs : r ≠ s)
    (A B : Var → Bool) (values : Var → WinnerSet Role)
    (common : ∀ j, A j = true → B j = true → r ∈ (values j).val)
    (avoid : ∀ j, A j = true → values j ≠ WinnerSet.singleton s)
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (ha : profile r A t = true) (hb : profile s B t = true) :
    r ∈ (t.realize values).val := by
  classical
  let C : Role → Var → Bool := fun q => if q = r then A else B
  apply ((rainbow_membership_iff {r, s} C r values).mpr ?_) t ?_
  · right
    constructor
    · intro j hj
      apply common j
      · simpa only [C, ite_true] using hj r (by simp)
      · simpa only [C, hrs.symm, ite_false] using hj s (by simp)
    · intro q hq hqr
      rcases Finset.mem_insert.mp hq with he | hq
      · exact False.elim (hqr he)
      · have he : q = s := Finset.mem_singleton.mp hq
        subst q
        rintro ⟨j, hj, hprofiles⟩
        apply avoid j _ hj
        simpa only [C, ite_true] using hprofiles r (by simp) hrs
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simpa only [C, ite_true] using ha
    · have he : q = s := Finset.mem_singleton.mp hq
      subst q
      simpa only [C, hrs.symm, ite_false] using hb

private def fourPartner : Fin 3 → Fin 4 := ![1, 3, 2]

private def fourProfiles (r : Fin 3) (E : Fin 4 → Bool) : Bool :=
  E 0 && E (fourPartner r)

private def fourValues : Fin 4 → WinnerSet (Fin 3) :=
  ![⟨Set.univ, Set.univ_nonempty⟩, WinnerSet.singleton 2,
    WinnerSet.singleton 0, WinnerSet.singleton 0]

private theorem fourProfiles_admissible : AdmissibleProfiles fourProfiles where
  mono r E F h hE := by
    have hh : E 0 = true ∧ E (fourPartner r) = true := by
      simpa only [fourProfiles, Bool.and_eq_true] using hE
    simpa only [fourProfiles, Bool.and_eq_true] using And.intro (h 0 hh.1) (h _ hh.2)
  top r := rfl
  common_source E h := by
    refine ⟨0, fun r => ?_⟩
    have hh : E r 0 = true ∧ E r (fourPartner r) = true := by
      simpa only [fourProfiles, Bool.and_eq_true] using h r
    exact hh.1

private def fourWitness (r : Fin 3) :
    Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 4) :=
  choiceTerm (![2, 0, 0] r) (.var 0) (.var (fourPartner r))

private theorem fourWitness_profile (r : Fin 3) (E : Fin 4 → Bool) :
    profile r E (fourWitness r) = fourProfiles r E := by
  fin_cases r <;> simp [fourWitness, fourProfiles, fourPartner]

private theorem fourWitness_safe (r : Fin 3) :
    1 ∉ ((fourWitness r).realize fourValues).val := by
  fin_cases r <;>
    simp [fourWitness, fourValues, fourPartner, choiceTerm, WinnerSet.choice]

/-- One negative winner constraint can create a new joint profile conflict:
each coordinate of an admissible full profile tuple has a safe core witness,
but the whole tuple has none. -/
theorem safe_profiles_not_ownerwise :
    ∃ (values : Fin 4 → WinnerSet (Fin 3))
      (P : Fin 3 → (Fin 4 → Bool) → Bool),
      AdmissibleProfiles P ∧
      (∀ r, ∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 4),
        (∀ E, profile r E t = P r E) ∧ 1 ∉ (t.realize values).val) ∧
      ¬∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 4),
        (∀ r E, profile r E t = P r E) ∧ 1 ∉ (t.realize values).val := by
  refine ⟨fourValues, fourProfiles, fourProfiles_admissible,
    fun r => ⟨fourWitness r, fourWitness_profile r, fourWitness_safe r⟩, ?_⟩
  rintro ⟨t, hprof, hs⟩
  let A : Fin 4 → Bool := fun j => decide (j = 0 ∨ j = 3)
  let B : Fin 4 → Bool := fun j => decide (j = 0 ∨ j = 2)
  have ha : profile 1 A t = true := by rw [hprof]; rfl
  have hb : profile 2 B t = true := by rw [hprof]; rfl
  apply hs
  apply winner_of_two_positive_profiles 1 2 (by decide) A B fourValues _ _ t ha hb
  · intro j hj hk
    fin_cases j <;> simp_all [A, B, fourValues]
  · intro j hj
    fin_cases j <;> simp_all [A, fourValues, WinnerSet.singleton_inj]
    intro he
    have hh := congrArg (fun W : WinnerSet (Fin 3) => (0 : Fin 3) ∈ W.val) he
    simp at hh

end KFOL.Core
