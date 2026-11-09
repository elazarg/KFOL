module

public import KFOL.Algebra
import all Init.Data.List.Sort.Basic

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

-- Proved finite sorting rewrites let the kernel normalize the branching
-- example without unfolding merge sort's well-founded recursion.
private theorem alternatives_guardList (j : Fin 5) : alternatives.guardList j =
    if j = 0 then [∅] else if j = 1 ∨ j = 2 then [{0}]
    else if j = 3 then [{0, 1}, {0, 2}] else [] := by
  by_cases h0 : j = 0
  · simp [GuardTable.guardList, alternatives, h0]
  by_cases h12 : j = 1 ∨ j = 2
  · simp [GuardTable.guardList, alternatives, h0, h12]
  by_cases h3 : j = 3
  · subst j
    change List.map ofColex
      (({toColex ({0, 1} : Finset (Fin 5)), toColex {0, 2}} :
        Finset (Colex (Finset (Fin 5)))).sort) = [{0, 1}, {0, 2}]
    have hle : toColex ({0, 1} : Finset (Fin 5)) ≤ toColex {0, 2} := by
      rw [Finset.Colex.toColex_le_toColex]
      decide
    rw [Finset.sort_insert (s := {toColex ({0, 2} : Finset (Fin 5))})
      (a := toColex ({0, 1} : Finset (Fin 5))) (r := (· ≤ ·)) (by simpa using hle) (by
        simp only [Finset.mem_singleton]
        intro he
        exact (by decide : ({0, 1} : Finset (Fin 5)) ≠ {0, 2}) (toColex.injective he))]
    simp only [Finset.sort_singleton, List.map_cons, List.map_nil]
    rfl
  · simp [GuardTable.guardList, alternatives, h0, h12, h3]

example : alternatives.check = true := by decide

-- Run the synthesizer and inspect its actual output, rather than just an
-- existence certificate. Both alternatives survive, and position 4 is unused.
example : alternatives.synthesize.map (fun t => t.table 3) = some {{0, 1}, {0, 2}} := by
  simp only [GuardTable.synthesize, GuardTable.synthesisPaths, Fin.sort_univ,
    alternatives_guardList]
  decide +kernel
example : alternatives.synthesize.map (fun t => t.table 4) = some ∅ := by
  simp only [GuardTable.synthesize, GuardTable.synthesisPaths, Fin.sort_univ,
    alternatives_guardList]
  decide +kernel
example : alternatives.synthesize.map Reset.Term.size = some 23 := by
  simp only [GuardTable.synthesize, GuardTable.synthesisPaths, Fin.sort_univ,
    alternatives_guardList]
  decide +kernel

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

-- A path orders prerequisites before the output, then reverses them into
-- primitive reset syntax. Fuel beyond completion cannot add repeated positions.
example : chain.greedyOrder Finset.univ 1 = [1] ∧
    chain.greedyOrder Finset.univ 2 = [1, 2] ∧
    chain.greedyOrder Finset.univ 5 = [1, 2] := by decide

example : chain.synthesize.map (fun t => t.table 2) = some {{0, 1}} := by
  simp only [GuardTable.synthesize, GuardTable.synthesisPaths, Fin.sort_univ]
  decide +kernel

-- Each cycle guard includes the root, and no guard contains its own output.
-- Root and self-independence checks alone cannot recognize this obstruction.
private def cyclic : GuardTable (Fin 3) where
  root := 0
  guards := fun j => if j = 0 then {∅} else if j = 1 then {{0, 2}} else {{0, 1}}

example : cyclic.check = false := by decide
example : cyclic.synthesize.isNone = true := by decide

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
example : singletonRoot.synthesize.map Reset.Term.size = some 3 := by
  simp only [GuardTable.synthesize, GuardTable.synthesisPaths, Fin.sort_univ]
  decide +kernel

example : IsEmpty (GuardTable (Fin 0)) := ⟨fun G => Fin.elim0 G.root⟩

end KFOLTest.ResetRealizability
