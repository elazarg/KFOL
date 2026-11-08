module

public import KFOL.Algebra

/-! Reset boundary cases: repeated occurrences, alternative prerequisites,
root collisions under substitution, nullary syntax and a nonassociative chain. -/

@[expose] public section

namespace KFOLTest.Reset

open KFOL
open KFOL.Reset
open KFOL.Reset.Term

private def x (i : Fin 4) : Reset.Term (Fin 4) := .var i
private def alternatives : Reset.Term (Fin 4) :=
  step (step (step (x 3) (x 1)) (x 0)) (step (step (x 3) (x 2)) (x 0))

-- The two occurrences of input 3 have different prerequisite paths. Combining
-- their paths into one dependency order would lose these alternatives.
example : alternatives.table 3 = {{0, 1}, {0, 2}} := by decide
example : alternatives.table 0 = {∅} := by decide
example : alternatives.table 1 = {{0}} := by decide

private def inner (i : Fin 4) : Reset.Term (Fin 3) :=
  if i = 0 then .var 0 else if i = 1 then step (.var 2) (.var 1)
  else if i = 2 then .var 0 else step (.var 1) (.var 2)

-- An inner root is identified with the outer root. Normalization must delete
-- the resulting dominated guards, rather than retain the outer variable names.
example : table (alternatives.subst inner) 0 = {∅} := by decide
example : table (alternatives.subst inner) 1 = {{0}} := by decide
example : table (alternatives.subst inner) 2 = {{0}} := by decide

example : IsEmpty (Reset.Term (Fin 0)) := ⟨fun t => Fin.elim0 t.root⟩

-- Variables from an arbitrarily padded declaration remain unused.
private def padded : Reset.Term (Fin 100) := step (.var 0) (.var 99)
example : padded.table 55 = ∅ := by decide
example : padded.table 0 = {{99}} := by decide

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _

-- Three values are needed: the reset algebra is nonassociative.
example :
    ((chainValue three 2).reset (chainValue three 0)).reset (chainValue three 1) ≠
      (chainValue three 2).reset ((chainValue three 0).reset (chainValue three 1)) := by
  rw [reset_chainValue, reset_chainValue, reset_chainValue, reset_chainValue]
  change chainValue three 1 ≠ chainValue three 2
  intro h
  have hm : three 2 ∈ (chainValue three 1).val ↔ three 2 ∈ (chainValue three 2).val := by rw [h]
  simp only [marker_chainValue] at hm
  exact (by decide : (1 : Fin 3) ≠ 2) (hm.mpr trivial)

-- Selection semantics still works with two roles; only the three-value
-- completeness theorem asks for three distinct roles.
example (v : Fin 4 → Fin 2) :
    alternatives.eval (fun i => WinnerSet.singleton (v i)) = WinnerSet.singleton (v 0) :=
  alternatives.eval_singletons v

end KFOLTest.Reset
