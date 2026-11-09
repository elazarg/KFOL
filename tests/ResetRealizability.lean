module

public import KFOL.Algebra

/-! Independent candidate tables: alternatives, cycles, invalid minimality,
unused positions, and the bounded greedy progress theorem. -/

@[expose] public section

namespace KFOLTest.ResetRealizability

open KFOL KFOL.Reset

-- Position 3 has two genuinely alternative prerequisites. Position 4 is unused.
private def alternatives : GuardTable (Fin 5) where
  root := 0
  guards := fun j => if j = 0 then {∅} else if j = 1 ∨ j = 2 then {{0}}
    else if j = 3 then {{0, 1}, {0, 2}} else ∅

example : alternatives.check = true := by decide

-- Acceptance produces an actual syntax tree, with an occurrence bound.
example : ∃ t : Reset.Term (Fin 5), t.root = 0 ∧ t.table = alternatives.guards ∧
    t.size ≤ 51 := by
  obtain ⟨t, hr, ht, hs⟩ := alternatives.check_iff_bounded_realization.mp (by decide)
  refine ⟨t, hr, ht, ?_⟩
  have he : 1 + 2 * Fintype.card (Fin 5) * alternatives.entryCount = 51 := by decide
  simpa only [he] using hs

private def chain : GuardTable (Fin 3) where
  root := 0
  guards := fun j => if j = 0 then {∅} else if j = 1 then {{0}} else {{0, 1}}

-- Later additions must wait for earlier rounds. A batch does not use its own
-- additions as prerequisites until the next round.
example : chain.reached Finset.univ 1 = {0} ∧
    chain.reached Finset.univ 2 = {0, 1} ∧
    chain.reached Finset.univ 3 = Finset.univ := by decide

example : chain.Constructible Finset.univ :=
  (chain.constructibleCheck_eq_true _).mp (by decide)

-- Each cycle guard includes the root, and no guard contains its own output.
-- Root and self-independence checks alone cannot recognize this obstruction.
private def cyclic : GuardTable (Fin 3) where
  root := 0
  guards := fun j => if j = 0 then {∅} else if j = 1 then {{0, 2}} else {{0, 1}}

example : cyclic.check = false := by decide

example : ¬∃ t : Reset.Term (Fin 3), t.root = cyclic.root ∧ t.table = cyclic.guards := by
  intro ht
  have h := cyclic.check_eq_true.mpr (cyclic.wellFormed_iff_realizable.mpr ht)
  have hn : cyclic.check = false := by decide
  rw [hn] at h
  cases h

private def multipleRoots : GuardTable (Fin 2) where
  root := 0
  guards := fun _ => {∅}

private def selfDependent : GuardTable (Fin 2) where
  root := 0
  guards := fun j => if j = 0 then {∅} else {{0, 1}}

private def dominated : GuardTable (Fin 3) where
  root := 0
  guards := fun j => if j = 0 then {∅} else if j = 1 then {{0}, {0, 2}} else {{0}}

example : multipleRoots.check = false ∧ selfDependent.check = false ∧
    dominated.check = false := by decide

private def singletonRoot : GuardTable (Fin 1) := ⟨0, fun _ => {∅}⟩

example : singletonRoot.check = true ∧ singletonRoot.constructibleCheck ∅ = true := by decide

example : IsEmpty (GuardTable (Fin 0)) := ⟨fun G => Fin.elim0 G.root⟩

end KFOLTest.ResetRealizability
