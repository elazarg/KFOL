module

public import KFOL.Algebra
public import Mathlib.Data.Fintype.Powerset

/-! Independently specified families, overlapping supports and empty ambients. -/

@[expose] public section

namespace KFOLTest.Antimatroid

open KFOL KFOL.Reset KFOL.Reset.Term

-- An independently specified rooted antimatroid: after its root, either of
-- the other two positions may be added in either order.
private def freeFamily : RootedAntimatroid (Fin 3) where
  ground := Finset.univ
  feasible := {A | A = ∅ ∨ 0 ∈ A}
  root := 0
  empty_mem := by decide
  ground_mem := by decide
  subset_ground := by decide
  union_mem := by decide
  accessible := by decide
  root_mem := by decide
  singleton_unique := by decide

-- Surjectivity consumes the axioms above, with no supplied term or table.
example : ∃ t : Reset.Term (Fin 3), t.varFinset = Finset.univ ∧ t.root = 0 ∧
    ∀ A : Finset (Fin 3), A ∈ t.feasible ↔ A = ∅ ∨ 0 ∈ A := by
  obtain ⟨t, ht⟩ := freeFamily.exists_term
  refine ⟨t, ?_, ?_, ?_⟩
  · rw [← t.antimatroid_ground, ht]
    rfl
  · rw [← t.antimatroid_root, ht]
    rfl
  · intro A
    rw [← t.feasible_antimatroid, ht]
    rfl

-- The two inputs share the root variable. Their family product still allows
-- both orders of the other positions, without treating the roots as fresh copies.
private def overlapping : Reset.Term (Fin 3) :=
  step (step (.var 1) (.var 0)) (step (.var 2) (.var 0))

example (A : Finset (Fin 3)) : A ∈ overlapping.feasible ↔ A = ∅ ∨ 0 ∈ A := by
  revert A
  dsimp [Term.feasible, overlapping, step, Selected, root]
  decide

-- Different path orders genuinely give different families.
private def path : Reset.Term (Fin 3) := step (step (.var 0) (.var 1)) (.var 2)
private def fork : Reset.Term (Fin 3) := step (.var 0) (step (.var 1) (.var 2))

private theorem fork_feasible : ({0, 2} : Finset (Fin 3)) ∈ fork.feasible := by
  dsimp [Term.feasible, fork, step, Selected, root]
  decide
private theorem path_not_feasible : ({0, 2} : Finset (Fin 3)) ∉ path.feasible := by
  dsimp [Term.feasible, path, step, Selected, root]
  decide
example : path.antimatroid ≠ fork.antimatroid := by
  intro he
  have hm : ({0, 2} : Finset (Fin 3)) ∈ fork.antimatroid.feasible := by
    rw [fork.feasible_antimatroid]
    exact fork_feasible
  rw [← he, path.feasible_antimatroid] at hm
  exact path_not_feasible hm

-- A large declaration contributes no unused position to the finite ground.
private def padded : Reset.Term (Fin 100) := .var 99
example : padded.antimatroid.ground = {99} := rfl
example (A : Finset (Fin 100)) : A ∈ padded.antimatroid.feasible ↔ A = ∅ ∨ A = {99} := Iff.rfl

-- Both sides of the representation have no objects on an empty ambient type.
example : IsEmpty (RootedAntimatroid (Fin 0)) := ⟨fun F => Fin.elim0 F.root⟩
example : IsEmpty (TermFunction (Fin 3) (Fin 0)) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨t, _⟩ := f.property
  exact Fin.elim0 t.root

end KFOLTest.Antimatroid
