import KFOL.Core.ProfileCompletion
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open KFOL KFOL.Core KFOL.Core.ProfileBounds

namespace CoreProfileQueriesTests
attribute [local instance] Equational.coreStructure

private def ownValues : Fin 1 → WinnerSet (Fin 3) := fun _ => WinnerSet.singleton 0

-- The requested owner must be exempt from foreign-owner separation: every
-- input is its atom, so that separation test would be impossible.
example : QuerySafe {0} (fun _ _ : Fin 3 => true)
    (fun _ : Fin 3 => WinnerSet.singleton 0) {0} 0 := by
  refine ⟨⟨⟨0,by simp⟩,Or.inl ⟨0,by simp,by simp⟩⟩,
    ⟨0,by simp,by simp⟩,?_⟩
  intro r hr hne
  exact (hne (Finset.mem_singleton.mp hr)).elim

example : ¬PairSafe 0 (fun _ : Fin 1 => true) (atomicBits 0 ownValues) ownValues {0} := by
  simp [PairSafe,atomicBits,ownValues]

private def sourceValues : Fin 2 → WinnerSet (Fin 3) :=
  ![⟨{0,2},by simp⟩,WinnerSet.singleton 1]

-- Winner 0 occurs in the input union, and the bound is feasible via input 1.
-- Yet no whole eligible input carries 0, so no bounded term can produce it.
example : RainbowSafe (∅ : Finset (Fin 3)) (fun _ : Fin 3 => fun _ : Fin 2 => false)
    sourceValues {0,1} := by
  exact ⟨⟨1,by simp⟩,Or.inl ⟨1,by simp,by simp [sourceValues]⟩⟩

example : ¬∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 2),
    (t.realize sourceValues).val ⊆ ({0,1} : Set (Fin 3)) ∧
      0 ∈ (t.realize sourceValues).val := by
  rintro ⟨t,hb,hk⟩
  obtain ⟨j,hj,hsub⟩ := whole_input_provenance_bounded t sourceValues {0,1} hb 0 hk
  fin_cases j
  · have hh := hsub (by simp [sourceValues] : (2 : Fin 3) ∈ (sourceValues 0).val)
    simp at hh
  · simp [sourceValues] at hj

private def atomValues : Fin 2 → WinnerSet (Fin 3) :=
  ![WinnerSet.singleton 0,WinnerSet.singleton 1]
private def pairTarget : WinnerSet (Fin 3) := ⟨{0,1},by simp⟩
private def projectionProfiles (_ : Fin 3) (A : Fin 2 → Bool) : Bool := A 0

-- A bound and whole-input coverage do not allow overriding a prescribed atom.
example : ¬OnePointCondition projectionProfiles atomValues pairTarget := by
  intro h
  have hp : projectionProfiles 0 (atomicBits 0 atomValues) = true := by
    simp [projectionProfiles,atomicBits,atomValues]
  have he := (h.2.1 0).mp hp
  have hm : (1 : Fin 3) ∈ pairTarget.val := by simp [pairTarget]
  rw [he] at hm
  simp at hm

end CoreProfileQueriesTests
