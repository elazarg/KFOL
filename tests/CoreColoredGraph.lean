import KFOL.Core.ColoredGraphRealization
import KFOL.Core.ColoredGraphReconstruction
import KFOL.Core.ColoredGraphConstruction

open KFOL Core ColoredGraph

-- A nonempty graph of input occurrences cannot supply a nullary constant.
example (f : (Fin 0 → WinnerSet (Fin 3)) → WinnerSet (Fin 3)) : ¬Represents f := by
  rintro ⟨n, _, label, hn, _⟩
  exact Fin.elim0 (label ⟨0, hn⟩)

-- The representation includes the one-owner case and the singleton graph.
example : Represents (fun v : Fin 1 → WinnerSet Unit => v 0) := by
  let G : Graph Unit (Fin 1) := ⟨fun _ _ => (), fun _ _ => rfl⟩
  refine ⟨1, G, fun _ => 0, by decide, G.noRainbow_of_subsingleton,
    G.noAlternatingPath_of_subsingleton, ?_⟩
  intro v k
  have hA : (Set.univ : Set (Fin 1)) = {0} := by
    ext x
    simp [Subsingleton.elim x 0]
  rw [hA]
  exact (wins_singleton 0 (fun _ => 0) v k).symm

-- Independent occurrences of the same label preserve idempotence, even when
-- the graph has arbitrary colors. Each owner clique extends around the source.
example (G : Graph (Fin 3) (Fin 4)) (v : Fin 1 → WinnerSet (Fin 3)) (k : Fin 3) :
    G.Wins Set.univ (fun _ => 0) v k ↔ k ∈ (v 0).val := by
  constructor
  · rintro ⟨_, _, hk, _⟩
    exact hk
  · intro hk
    refine ⟨0, Set.mem_univ _, hk, ?_⟩
    intro r hr
    obtain ⟨D, hD0, hD⟩ := exists_maxClique (G := G) (A := Set.univ) (r := r)
      (D := {0}) (Set.subset_univ _) ((G.component r).isClique_singleton 0)
    refine ⟨D, hD, hD0 (by simp), ?_⟩
    intro _ _ _ he
    have hkr : k = r := by simpa [he] using hk
    exact hr hkr.symm

private def rainbow : Graph (Fin 3) (Fin 3) where
  color x y := x + y
  symm := add_comm

-- Three genuinely different colors on a triangle are forbidden.
example : ¬rainbow.NoRainbow := by
  intro h
  have hh := h 0 1 2 (by decide) (by decide) (by decide)
  exact (by decide : ¬(rainbow.color 0 1 = rainbow.color 1 2 ∨
    rainbow.color 0 1 = rainbow.color 0 2 ∨
    rainbow.color 1 2 = rainbow.color 0 2)) hh

private def alternatingPath : Graph (Fin 2) (Fin 4) where
  color x y := if x.val + 1 = y.val ∨ y.val + 1 = x.val then 0 else 1
  symm x y := by simp [or_comm]

-- Two colors suffice for a separate forbidden pattern: a path and its complement.
example : ¬alternatingPath.NoAlternatingPath := by
  intro h
  exact h (Function.Embedding.refl (Fin 4)) 0 1 (by decide) (by decide)


-- The characterization imposes no finiteness requirement on roles or variables.
example : Represents (fun v : ℕ → WinnerSet ℕ => WinnerSet.choice 7 (v 3) (v 11)) := by
  apply (represents_iff _).mpr
  exact ⟨Term.choice 7 (.var 3) (.var 11), ⟨trivial, trivial⟩, fun _ => rfl⟩
