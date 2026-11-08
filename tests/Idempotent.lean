module

public import KFOL.Algebra

/-!
Regression cases for accumulated action and core extraction. These exercise
noncommuting switches, cancellation through an owned node and the genuine
two-role failure of the no-winner characterization. No native computation is
used as proof evidence.
-/

@[expose] public section

namespace KFOLTest.Idempotent

open KFOL

private def nested : Term (Fin 3) Unit :=
  .rename (Equiv.swap 0 1) (.rename (Equiv.swap 1 2) (.var ()))

-- Reversing accumulated multiplication would send 0 to 2 instead of 1.
example : nested.inputOccurrences.map (fun (_, p) => p 0) = [1] := by decide

private def cancelled (p : Equiv.Perm (Fin 3)) : Term (Fin 3) Bool :=
  .rename p (.choice 0 (.rename p⁻¹ (.var false)) (.rename p⁻¹ (.var true)))

example (p : Equiv.Perm (Fin 3)) :
    ∀ A : WinnerSet (Fin 3), (cancelled p).eval (fun _ => A) = A := by
  apply ((cancelled p).idempotent_iff_clean (Function.Embedding.refl _)).mpr
  constructor
  · simp [cancelled, Term.HasWinner]
  · intro x q hq
    simp only [cancelled, Term.inputOccurrences, List.map_cons,
      List.map_nil, mul_one, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq
    · exact (Prod.mk.inj hq).2 ▸ mul_inv_cancel p
    · exact (Prod.mk.inj hq).2 ▸ mul_inv_cancel p

example (p : Equiv.Perm (Fin 3)) :
    (cancelled p).pushRenames 1 = .choice (p 0) (.var false) (.var true) := rfl

-- In two roles a winner leaf can be semantically redundant. This guards
-- against accidentally dropping the three-role hypothesis during migration.
example (A : WinnerSet (Fin 2)) :
    (Term.choice 0 (.var ()) (.winner 1)).eval (fun _ => A) = A := by
  classical
  change WinnerSet.choice 0 A (WinnerSet.singleton 1) = A
  by_cases h0 : A = WinnerSet.singleton 0
  · simp [h0, WinnerSet.choice]
  · have h1 : (1 : Fin 2) ∈ A.val := by
      apply Classical.byContradiction
      intro hn
      apply h0
      apply WinnerSet.eq_singleton_of_subset
      intro x hx
      have : x = 0 ∨ x = 1 := by omega
      exact this.elim id (fun he => False.elim (hn (he ▸ hx)))
    simp only [WinnerSet.choice, h0, WinnerSet.singleton_inj]
    rw [WinnerSet.union_comm]
    exact WinnerSet.singleton_union_of_mem A 1 h1

example : (Term.choice (0 : Fin 2) (.var ()) (.winner 1)).HasWinner := Or.inr trivial

-- These reduce the actual checked extractor, including its finite permutation
-- tests, rather than deciding a separate predicate or evaluating a model.
example : nested.extractCore? 1 = none := rfl

example : (cancelled (Equiv.swap 0 1)).extractCore? 1 =
    some (.choice 1 (.var false) (.var true)) := rfl

example : (Term.choice (0 : Fin 2) (.var ()) (.winner 1)).extractCore? 1 = none := rfl

end KFOLTest.Idempotent
