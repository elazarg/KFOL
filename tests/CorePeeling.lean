import KFOL.Core.Peeling
import KFOL.Algebra.SemilatticeTrace
import Mathlib.Tactic.FinCases

open KFOL Core Core.Interpolation WinnerSet

namespace CorePeelingTests

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _

-- With no rows, the test still asks for an actual core term. Arity zero
-- supplies none, whereas one input variable supplies a projection.
example : ¬ Recognizes (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Fin 0 → WinnerSet (Fin 3))
    (fun _ => ∅) := by
  intro h
  obtain ⟨t, ht, _⟩ := (recognizes_iff three _ _).mp h
  obtain ⟨j, _⟩ := ht.vars_nonempty
  exact Fin.elim0 j

example : Recognizes (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Fin 1 → WinnerSet (Fin 3))
    (fun _ => ∅) := by
  apply (recognizes_iff three _ _).mpr
  exact ⟨.var 0, trivial, fun i => Fin.elim0 i⟩

-- An empty allowed value at a genuine row is rejected by winner-set
-- nonemptiness, with no auxiliary nonemptiness premise in Recognizes.
example (values : Fin 1 → Fin 1 → WinnerSet (Fin 3)) :
    ¬ Recognizes values (fun _ => ∅) := by
  intro h
  obtain ⟨t, _, he⟩ := (recognizes_iff three values _).mp h
  have hn := (t.eval (values 0)).property
  rw [he 0] at hn
  exact Set.not_nonempty_empty hn

-- One row cannot be exactly a while also containing the distinct winner b.
example (values : Fin 1 → Fin 1 → WinnerSet (Fin 3)) :
    ¬ Peels values (fun _ => Set.univ) ∅ {(0, 0)} (some (0, 1)) := by
  intro h
  obtain ⟨t, _, _, ha, hp⟩ := (peels_iff three values _ _ _ _).mp h
  have he := ha (0, 0) (by simp)
  have hm : (1 : Fin 3) ∈ (t.eval (values 0)).val := hp
  simp [he] at hm

private def values : Fin 2 → Fin 2 → WinnerSet (Fin 3) :=
  ![![singleton 1, singleton 0], ![singleton 0, singleton 1]]

private def allowed : Fin 2 → Set (Fin 3) := fun _ => {0}
private def demands : Finset (Fin 2 × Fin 3) := {(0, 0), (1, 0)}
private def witness : Term (Fin 3) (Fin 2) := .choice 0 (.var 0) (.var 1)

private theorem witness_eval (i : Fin 2) : witness.eval (values i) = singleton 0 := by
  fin_cases i <;> simp [witness, Term.eval, values, choice]

-- Neither input column lies within both a-bounds.
example (j : Fin 2) : ¬ Bounded Finset.univ allowed (fun i => values i j) := by
  fin_cases j
  · intro h
    have hm := h 0 (by simp) (by simp [values] : (1 : Fin 3) ∈ (values 0 0).val)
    simp [allowed] at hm
  · intro h
    have hm := h 1 (by simp) (by simp [values] : (1 : Fin 3) ∈ (values 1 1).val)
    simp [allowed] at hm

-- Atomic boundary tuples must be available even when there is no bounded
-- projection. The actual owned-choice term realizes the entire table.
example : Recognizes values allowed := by
  apply (recognizes_iff three values allowed).mpr
  refine ⟨witness, by simp [witness, Term.IsCore], ?_⟩
  intro i
  rw [witness_eval]
  rfl

example : Peels values allowed Finset.univ ∅ none := by
  apply (peels_iff three values allowed _ _ _).mpr
  refine ⟨witness, by simp [witness, Term.IsCore], ?_, ?_, trivial⟩
  · intro i _
    change (witness.eval (values i)).val ⊆ allowed i
    rw [witness_eval]
    exact Set.Subset.rfl
  · simp [Atomic]

-- Same-owner demands are not a simultaneous projection demand. No input
-- column satisfies both, yet the core choice satisfies them together.
example (j : Fin 2) : ¬ Atomic demands (fun i => values i j) := by
  fin_cases j
  · intro h
    have he := h (0, 0) (by simp [demands])
    simp [values] at he
  · intro h
    have he := h (1, 0) (by simp [demands])
    simp [values] at he

example : Peels values allowed ∅ demands none := by
  apply (peels_iff three values allowed _ _ _).mpr
  refine ⟨witness, by simp [witness, Term.IsCore], ?_, ?_, trivial⟩
  · simp [Bounded]
  · intro d hd
    have hd0 : d.2 = 0 := by
      simp only [demands, Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl <;> rfl
    change witness.eval (values d.1) = singleton d.2
    rw [witness_eval, hd0]

end CorePeelingTests
