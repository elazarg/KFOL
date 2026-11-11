import KFOL.Core.PairwiseInterpolation
import KFOL.Core.TernaryInterpolation

open KFOL Core

-- The obstruction survives adding a fourth role.
example : PairwiseInterpolable
    (pairwiseCounterexample (Fin.castLEEmb (by decide : 3 ≤ 4))) :=
  Pairwise.counterexample_pairwise _

example : ¬∃ t : Term (Fin 4) (Fin 3), t.IsCore ∧
    ∀ v, t.eval v = pairwiseCounterexample (Fin.castLEEmb (by decide : 3 ≤ 4)) v :=
  Pairwise.counterexample_not_term _

-- Empty invariant relations matter: a nullary function has no interpolant.
example (f : (Fin 0 → WinnerSet (Fin 3)) → WinnerSet (Fin 3)) :
    ¬ PreservesBinary f := by
  intro hf
  have h := hf ∅ (by intro _ _ _ hx; exact hx.elim)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  exact h

-- Three-point interpolation and its non-realizability survive extra owners.
example : LocallyInterpolable 3
    (threewiseCounterexample (Fin.castLEEmb (by decide : 3 ≤ 4))) :=
  Threewise.counterexample_interpolable _

example : PreservesInvariants 3
    (threewiseCounterexample (Fin.castLEEmb (by decide : 3 ≤ 4))) :=
  Threewise.counterexample_preserves _

example : ¬∃ t : Term (Fin 4) (Fin 3), t.IsCore ∧
    ∀ v, t.eval v = threewiseCounterexample (Fin.castLEEmb (by decide : 3 ≤ 4)) v :=
  Threewise.counterexample_not_term _

-- The general relational equivalence includes arity zero and no variables.
example (f : (Fin 0 → WinnerSet (Fin 3)) → WinnerSet (Fin 3)) :
    ¬ PreservesInvariants 0 f := by
  intro hf
  have h := hf ∅ (by intro _ _ _ hx; exact hx.elim)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  exact h

example (A : WinnerSet (Fin 3)) :
    LocallyInterpolable 0 (fun v : Fin 1 → WinnerSet (Fin 3) => (v 0).union A) :=
  fun _ => ⟨.var 0, trivial, fun i => Fin.elim0 i⟩
