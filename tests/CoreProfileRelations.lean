import KFOL.Core.ProfileRelations
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

open KFOL.Core.ProfileRelations

namespace CoreProfileRelationsTests

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _
private def owners : Fin 2 → Fin 3 := ![0,1]

-- Every relation on the unique empty tuple is closed, including the empty
-- relation. The classification covers both cases without a nonemptiness premise.
example (R : Set (Fin 0 → Bool)) :
    ∃ T : Theory (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Fin 3),
      ∀ x, x ∈ R ↔ T.Models x := by
  apply (choiceClosed_iff_theory (fun i : Fin 0 => Fin.elim0 i) three R).mp
  intro r x y hx _
  have he : mixedChoice (fun i : Fin 0 => Fin.elim0 i) r x y = x := by
    funext i
    exact Fin.elim0 i
  simpa only [he] using hx

-- Empty relations on genuine coordinates are also presented exactly.
example : ∃ T : Theory owners, ∀ x, ¬T.Models x := by
  obtain ⟨T,hT⟩ := (choiceClosed_iff_theory owners three
    (∅ : Set (Fin 2 → Bool))).mp (by intro r x y hx _; exact hx.elim)
  exact ⟨T,fun x hx => (hT x).mpr hx⟩

private def xorRelation : Set (Fin 2 → Bool) := {x | x 0 ≠ x 1}

-- Two owners preserve {10,01}, but their mixed gates do not generate global AND.
-- This is the boundary that makes the three-owner assumption necessary.
example : ChoiceClosed (fun i : Fin 2 => i) xorRelation := by
  intro r x y hx hy
  fin_cases r <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;>
    cases hy0 : y 0 <;> cases hy1 : y 1 <;>
    simp_all [xorRelation,mixedChoice]

example : ¬(∀ x y : Fin 2 → Bool, x ∈ xorRelation → y ∈ xorRelation →
    (fun i => x i && y i) ∈ xorRelation) := by
  intro h
  have hh := h ![true,false] ![false,true] (by simp [xorRelation]) (by simp [xorRelation])
  simp [xorRelation] at hh

-- A nontrivial implication across owners is not preserved: the first gate
-- takes OR at its premise and AND at its conclusion.
example : ¬ChoiceClosed owners {x : Fin 2 → Bool | x 0 = true → x 1 = true} := by
  intro h
  have hh := h 0 ![false,false] ![true,true] (by simp) (by simp)
  simp [mixedChoice,owners] at hh

-- A forbidden pair in one owner group is not invariant: OR combines its two
-- separately permitted singletons. The rainbow condition excludes this pair.
example : ¬ChoiceClosed (fun _ : Fin 2 => (0 : Fin 3))
    {x : Fin 2 → Bool | ¬AllTrue {0,1} x} := by
  intro h
  have hh := h 0 ![true,false] ![false,true]
    (by simp [AllTrue]) (by simp [AllTrue])
  apply hh
  intro i hi
  fin_cases i <;> simp [mixedChoice]

-- Moving the two coordinates to distinct owners makes that same conflict valid.
example : ChoiceClosed owners {x : Fin 2 → Bool | ¬AllTrue {0,1} x} := by
  intro r x y hx hy
  fin_cases r <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;>
    cases hy0 : y 0 <;> cases hy1 : y 1 <;>
    simp_all [AllTrue,mixedChoice,owners]

end CoreProfileRelationsTests
