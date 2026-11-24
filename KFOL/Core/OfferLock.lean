module

public import KFOL.Core.RainbowPersistence
public import KFOL.Core.SourceNormalForm
import KFOL.Equational.Native

/-! # Blocking a third offer with source losses -/

@[expose] public section

namespace KFOL.Core.OfferLock

variable {Role Var : Type*} [DecidableEq Role]
attribute [local instance] Equational.coreStructure

/-- Three positive profiles retain the middle owner's mark if every common input
carries it and the other two owners' atoms miss the indicated coalitions. -/
theorem mark_of_three_profiles (three : Fin 3 ↪ Role) (A B C : Var → Bool)
    (values : Var → WinnerSet Role)
    (common : ∀ j, A j = true → B j = true → C j = true → three 1 ∈ (values j).val)
    (first : ∀ j, C j = true → values j ≠ WinnerSet.singleton (three 0))
    (third : ∀ j, A j = true → B j = true → values j ≠ WinnerSet.singleton (three 2))
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (hA : profile (three 0) A t = true) (hB : profile (three 1) B t = true)
    (hC : profile (three 2) C t = true) : three 1 ∈ (t.realize values).val := by
  classical
  have n01 : three 0 ≠ three 1 := three.injective.ne (by decide)
  have n02 : three 0 ≠ three 2 := three.injective.ne (by decide)
  have n12 : three 1 ≠ three 2 := three.injective.ne (by decide)
  let J : Finset Role := {three 0, three 1, three 2}
  let flags (r : Role) := if r = three 0 then A else if r = three 1 then B else C
  have f0 : flags (three 0) = A := by simp [flags]
  have f1 : flags (three 1) = B := by simp [flags, Ne.symm n01]
  have f2 : flags (three 2) = C := by simp [flags, Ne.symm n02, Ne.symm n12]
  apply (rainbow_membership_iff J flags (three 1) values).mpr _ t
  · intro r hr
    simp only [J, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [f0] using hA
    · simpa only [f1] using hB
    · simpa only [f2] using hC
  · right
    constructor
    · intro j wins
      apply common j
      · simpa only [f0] using wins (three 0) (by simp [J])
      · simpa only [f1] using wins (three 1) (by simp [J])
      · simpa only [f2] using wins (three 2) (by simp [J])
    · rintro r hr ne ⟨j,atom,wins⟩
      simp only [J, Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl | rfl
      · exact first j (by simpa only [f2] using wins (three 2) (by simp [J]) n02.symm) atom
      · exact ne rfl
      · exact third j (by simpa only [f0] using wins (three 0) (by simp [J]) n02)
          (by simpa only [f1] using wins (three 1) (by simp [J]) n12) atom

/-- If every input carrying the middle mark has a surviving loss whose posted
atoms hold at this valuation, the other two profiles exclude the third offer. -/
theorem third_profile_false_of_source_losses (three : Fin 3 ↪ Role) (A B C : Var → Bool)
    (values : Var → WinnerSet Role)
    (common : ∀ j, A j = true → B j = true → C j = true → three 1 ∈ (values j).val)
    (first : ∀ j, C j = true → values j ≠ WinnerSet.singleton (three 0))
    (third : ∀ j, A j = true → B j = true → values j ≠ WinnerSet.singleton (three 2))
    (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (hA : profile (three 0) A t = true) (hB : profile (three 1) B t = true)
    (loss : ∀ j, three 1 ∈ (values j).val → ∃ p : Sources.Pattern (three 1) j,
      (∀ i r, p i = .atom r → values i.val = WinnerSet.singleton r.val) ∧
      three 1 ∉ (t.realize (Sources.probe three (three 1) j p)).val) :
    profile (three 2) C t = false := by
  classical
  apply Bool.eq_false_iff.mpr
  intro hC
  have mark := mark_of_three_profiles three A B C values common first third t hA hB hC
  let word := Equational.Core.decode t
  have observed : three 1 ∈ (word.eval values).val := by
    simpa only [word, Equational.Core.eval_decode] using mark
  obtain ⟨j,hj,hit⟩ := (Sources.membership_iff_source three word
    (Equational.Core.isCore_decode t) values (three 1)).mp observed
  obtain ⟨p,posts,miss⟩ := loss j hj
  have refinement : Sources.pattern (three 1) j values ≤ p := by
    intro i
    cases hi : p i with
    | neutral => exact Or.inl rfl
    | atom r =>
      exact Or.inr ((Sources.passive_eq_atom_iff (three 1) (values i.val) r).mpr (posts i r hi))
  apply miss
  simpa only [word, Equational.Core.eval_decode] using
    Sources.coefficient_mono three word (three 1) j refinement hit

end KFOL.Core.OfferLock
