import KFOL.Core.Cuts
import KFOL.Core.Interpolation
import KFOL.Algebra.SemilatticeTrace
import Mathlib.Data.Fin.VecNotation

open KFOL

private def atom (r : Fin 3) : WinnerSet (Fin 3) := WinnerSet.singleton r
private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _

private def values (i : Fin 3) : Fin 3 → WinnerSet (Fin 3) :=
  ![![(atom 0).union (atom 1), atom 1, atom 1],
    ![atom 1, (atom 1).union (atom 2), (atom 0).union (atom 1)],
    ![atom 0, atom 1, atom 2]] i

private def target (i : Fin 3) : WinnerSet (Fin 3) :=
  ![atom 1, (atom 1).union (atom 2), (atom 0).union (atom 2)] i

-- Each row has a realizing term on its own.
example (i : Fin 3) : ∃ t : Term (Fin 3) (Fin 3), t.IsCore ∧ t.eval (values i) = target i := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl
  · exact ⟨.var 1, trivial, rfl⟩
  · exact ⟨.var 1, trivial, rfl⟩
  · refine ⟨Term.unionTerm three (.var 0) (.var 2), ⟨⟨trivial, trivial⟩, ⟨trivial, trivial⟩⟩, ?_⟩
    simp [Term.eval_unionTerm, values, target, Term.eval]

-- The cut test rejects these incompatible choices of witnesses: it requires
-- one term to realize every row simultaneously.
example : ¬Core.Cuts.Recognizes values target := by
  intro h
  obtain ⟨t, ht, he⟩ := (Core.Cuts.recognizes_iff three values target).mp h
  have hb := Core.three_valuation_persistence (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) id t ht (he 0) (he 1)
  change (1 : Fin 3) ∈ (t.eval (values 2)).val at hb
  rw [he 2] at hb
  simp [target, atom] at hb

-- Empty syntax has no seed; arity zero does not pass vacuously.
example (f : (Fin 0 → WinnerSet (Fin 3)) → WinnerSet (Fin 3)) :
    ¬Core.CutRecognizes f := by
  intro h
  obtain ⟨t, ht, _⟩ := (Core.Cuts.operation_iff three f).mp h
  obtain ⟨x, _⟩ := ht.vars_nonempty
  exact Fin.elim0 x

-- The round count is proved by the general finite-cardinality theorem.
example : Fintype.card (Core.Cuts.Fact (Fin 3) (Fin 3)) = 1125 := by
  simpa using (Core.Cuts.fact_card (Role := Fin 3) (Row := Fin 3))
