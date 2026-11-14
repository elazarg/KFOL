module

public import KFOL.InfiniteGames.Profiles

/-! # The safety fixedpoint checks every subgame -/

@[expose] public section

namespace KFOL.InfiniteGames.PriorityGame

universe u v

variable {Role : Type u} {Move : Type v} {n : ℕ}
variable (G : PriorityGame Role Move n) (σ : Profile Move)

theorem equilibriumRegion_test {h : List Move} (hh : h ∈ G.equilibriumRegion σ) :
    ∀ i, h ∈ G.winRegion (G.deviationRel σ i) i →
      h ∈ G.winRegion (profileRel σ) i := by
  have unfolded : h ∈ (equilibriumHom G σ) ((equilibriumHom G σ).gfp) := by
    simpa only [equilibriumRegion, OrderHom.map_gfp] using hh
  exact unfolded.1

theorem equilibriumRegion_child {h k : List Move}
    (hh : h ∈ G.equilibriumRegion σ) (hk : legal h k) :
    k ∈ G.equilibriumRegion σ := by
  have unfolded : h ∈ (equilibriumHom G σ) ((equilibriumHom G σ).gfp) := by
    simpa only [equilibriumRegion, OrderHom.map_gfp] using hh
  exact unfolded.2 k hk

theorem equilibriumRegion_append {h : List Move}
    (hh : h ∈ G.equilibriumRegion σ) (suffix : List Move) :
    h ++ suffix ∈ G.equilibriumRegion σ := by
  induction suffix generalizing h with
  | nil => simpa only [List.append_nil] using hh
  | cons a tail ih =>
    have child := G.equilibriumRegion_child σ hh ⟨a, rfl⟩
    simpa only [List.append_assoc, List.singleton_append] using ih child

/-- The final greatest fixedpoint is exactly the full family of deviation
tests in all descendant subgames, including unreached histories. -/
theorem equilibriumRegion_iff_tests (h : List Move) :
    h ∈ G.equilibriumRegion σ ↔
      ∀ suffix i, h ++ suffix ∈ G.winRegion (G.deviationRel σ i) i →
        h ++ suffix ∈ G.winRegion (profileRel σ) i := by
  constructor
  · intro hh suffix
    exact G.equilibriumRegion_test σ (G.equilibriumRegion_append σ hh suffix)
  · intro tests
    let S : Set (List Move) := {k | ∀ suffix i,
      k ++ suffix ∈ G.winRegion (G.deviationRel σ i) i →
        k ++ suffix ∈ G.winRegion (profileRel σ) i}
    have postfixed : S ⊆ (equilibriumHom G σ) S := by
      intro k hk
      refine ⟨?_, ?_⟩
      · simpa only [List.append_nil, Set.mem_ofPred_eq] using hk []
      · rintro next ⟨a, rfl⟩ suffix
        simpa only [List.append_assoc, List.singleton_append] using hk (a :: suffix)
    exact (equilibriumHom G σ).le_gfp postfixed tests

end KFOL.InfiniteGames.PriorityGame
