module

public import KFOL.Policies.PublicCompilation

@[expose] public section

namespace KFOLTest.PoliciesPublicCompilation

open KFOL
open KFOL.Policies

/-- Infinite label and variable types remain supported; only roles are finite. -/
example (D : ℕ → Finset (Fin 3)) :
    Term.toPublic (Function.Embedding.refl _) (List.finRange 3) D
      (.var 1000000000 : KFOL.Policies.Term ℕ ℕ) = KFOL.Term.var 1000000000 := rfl

example (D : ℕ → Finset (Fin 3)) (t : KFOL.Policies.Term ℕ ℕ)
    (v : ℕ → WinnerSet (Fin 3)) :
    (t.toPublic (Function.Embedding.refl _) (List.finRange 3) D).eval v =
      t.eval (fun d => (D d : Set (Fin 3))) v :=
  Term.eval_toPublic (Function.Embedding.refl _) (List.finRange 3) (by simp) D t v

example (D : ℕ → Finset (Fin 3)) (s t : KFOL.Policies.Term ℕ ℕ)
    (failure : ∃ v : ℕ → WinnerSet (Fin 3),
      s.eval (fun d => (D d : Set (Fin 3))) v ≠ t.eval (fun d => (D d : Set (Fin 3))) v) :
    ∃ v : ℕ → WinnerSet (Fin 3),
      (s.eval (fun d => (D d : Set (Fin 3))) v ≠ t.eval (fun d => (D d : Set (Fin 3))) v) ∧
      ∀ i, ∃ a b, v i = (WinnerSet.singleton a).union (WinnerSet.singleton b) :=
  Term.exists_pair_countervaluation D (Function.Embedding.refl _) s t failure

/-- info: 'KFOL.Policies.Term.eval_toPublic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Term.eval_toPublic

/-- info: 'KFOL.Policies.Term.exists_pair_countervaluation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Term.exists_pair_countervaluation

/-- info: 'KFOL.Policies.Term.isCore_toPublic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Policies.Term.isCore_toPublic

end KFOLTest.PoliciesPublicCompilation
