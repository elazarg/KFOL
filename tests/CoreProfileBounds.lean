import KFOL.Core.ProfileBounds
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open KFOL KFOL.Core KFOL.Core.ProfileBounds

namespace CoreProfileBoundsTests
attribute [local instance] Equational.coreStructure

-- The unrestricted test is independent of any decidable equality or finiteness
-- assumption on the role and variable types.
example {Role Var : Type*} (r : Role) (A B : Var → Bool)
    (values : Var → WinnerSet Role) :
    PairSafe r A B values Set.univ ↔ ∃ j, A j = true ∧ B j = false :=
  pairSafe_univ_iff r A B values

-- The original common-source classification is recovered at infinite arity.
example (values : Nat → WinnerSet (Fin 3)) :
    ProfileCondition (fun _ E => E 0) values Set.univ := by
  apply (profileCondition_univ_iff_admissibleProfiles _ values).mpr
  exact ⟨fun _ _ _ h hp => h 0 hp,fun _ => rfl,fun _ h => ⟨0,h⟩⟩

-- Empty variables cannot acquire a fictitious constant-free realization.
example (Φ : Fin 3 → (Fin 0 → Bool) → Bool)
    (values : Fin 0 → WinnerSet (Fin 3)) (U : Set (Fin 3)) :
    ¬ProfileCondition Φ values U := by
  intro h
  obtain ⟨j,_⟩ := (h.2.2 (fun _ _ => true) h.1).1
  exact Fin.elim0 j

-- A raw empty budget is rejected, including when no variable is assumed inhabited.
example {Var : Type*} [Fintype Var] (Φ : Fin 3 → (Var → Bool) → Bool)
    (values : Var → WinnerSet (Fin 3)) : ¬ProfileCondition Φ values ∅ := by
  intro h
  obtain ⟨t,_,hb⟩ := (profileCondition_iff (Function.Embedding.refl _) Φ values ∅).mp h
  exact Set.not_nonempty_empty ((t.realize values).property.mono hb)

private def ownValues : Fin 2 → WinnerSet (Fin 3) :=
  ![WinnerSet.singleton 1,WinnerSet.singleton 0]

-- The positive/negative distinguishing projection is unsafe. The same-owner
-- absorber branch nevertheless supplies an actual bounded term.
example : ¬∃ j : Fin 2, (![true,false] j = true) ∧ (![false,false] j = false) ∧
    (ownValues j).val ⊆ ({0} : Set (Fin 3)) := by
  rintro ⟨j,hj,_,hb⟩
  fin_cases j
  · have hh := hb (by simp [ownValues] : (1 : Fin 3) ∈ (ownValues 0).val)
    simp at hh
  · simp at hj

example : ∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 2),
    profile 0 ![true,false] t = true ∧ profile 0 ![false,false] t = false ∧
      (t.realize ownValues).val ⊆ ({0} : Set (Fin 3)) := by
  apply (pairSafe_iff 0 ![true,false] ![false,false] ownValues {0}).mp
  exact Or.inr (Or.inl ⟨by simp,⟨0,rfl,rfl⟩,1,rfl,rfl⟩)

private def foreignValues : Fin 2 → WinnerSet (Fin 3) :=
  ![WinnerSet.singleton 1,WinnerSet.singleton 2]

-- A foreign absorber inside the negative coalition can satisfy the budget;
-- its other leaf supplies the positive/negative profile difference.
example : ∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 2),
    profile 0 ![true,true] t = true ∧ profile 0 ![true,false] t = false ∧
      (t.realize foreignValues).val ⊆ ({1} : Set (Fin 3)) := by
  apply (pairSafe_iff 0 ![true,true] ![true,false] foreignValues {1}).mp
  exact Or.inr (Or.inr ⟨⟨1,rfl,rfl⟩,1,by simp,by decide,0,rfl,rfl⟩)

end CoreProfileBoundsTests
