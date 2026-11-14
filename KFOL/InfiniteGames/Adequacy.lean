module

public import KFOL.InfiniteGames.Buchi
public import KFOL.InfiniteGames.Priorities
public import KFOL.InfiniteGames.Equilibrium

/-! # Adequacy of the objective-sensitive multiplayer fixedpoint semantics

The proof eliminates path quantification for each fixed profile. Strategy
profiles remain existentially quantified: no determinacy or equilibrium
existence theorem is assumed.
-/

@[expose] public section

namespace KFOL.InfiniteGames.PriorityGame

universe u v

variable {Role : Type u} {Move : Type v} {n : ℕ}
variable (G : PriorityGame Role Move n)

theorem winRegion_iff_path {R : List Move → List Move → Prop} {i : Role}
    {h : List Move} : h ∈ G.winRegion R i ↔
    ∃ π : ℕ → List Move, π 0 = h ∧ (∀ k, R (π k) (π (k + 1))) ∧ G.Wins i π := by
  constructor
  · rintro ⟨p, hpi, hp⟩
    obtain ⟨π, initial, edges, recurrent, bounded⟩ := (mem_priorityRegion_iff G.priority p).mp hp
    exact ⟨π, initial, edges, p, hpi, recurrent, bounded⟩
  · rintro ⟨π, initial, edges, p, hpi, recurrent, bounded⟩
    exact ⟨p, hpi, (mem_priorityRegion_iff G.priority p).mpr
      ⟨π, initial, edges, recurrent, bounded⟩⟩

theorem profile_winRegion_iff {σ : Profile Move} {i : Role} {h : List Move} :
    h ∈ G.winRegion (profileRel σ) i ↔ G.Wins i (run σ h) := by
  rw [G.winRegion_iff_path]
  constructor
  · rintro ⟨π, initial, edges, wins⟩
    exact (eq_run_of_profilePath initial edges) ▸ wins
  · intro wins
    exact ⟨run σ h, rfl, run_profilePath σ h, wins⟩

/-- The existential path formula allows exactly full unilateral strategy
replacements, with the other owners' complete plans held fixed. -/
theorem deviation_winRegion_iff {σ : Profile Move} {i : Role} {h : List Move} :
    h ∈ G.winRegion (G.deviationRel σ i) i ↔
      ∃ τ, G.Deviation i σ τ ∧ G.Wins i (run τ h) := by
  rw [G.winRegion_iff_path]
  constructor
  · rintro ⟨π, initial, edges, wins⟩
    obtain ⟨τ, deviation, outcome⟩ := G.exists_deviation_of_path initial edges
    exact ⟨τ, deviation, outcome ▸ wins⟩
  · rintro ⟨τ, deviation, wins⟩
    exact ⟨run τ h, rfl, G.deviation_run_path deviation h, wins⟩

theorem isNash_iff_region_tests {σ : Profile Move} {h : List Move} :
    G.IsNash σ h ↔
      ∀ i, h ∈ G.winRegion (G.deviationRel σ i) i →
        h ∈ G.winRegion (profileRel σ) i := by
  constructor
  · intro nash i deviation
    obtain ⟨τ, hτ, wins⟩ := G.deviation_winRegion_iff.mp deviation
    exact G.profile_winRegion_iff.mpr (nash i τ hτ wins)
  · intro tests i τ deviation wins
    exact G.profile_winRegion_iff.mp (tests i
      (G.deviation_winRegion_iff.mpr ⟨τ, deviation, wins⟩))

/-- Full, history-dependent SPE is exactly the objective-sensitive ν/μ/ν
test at every subgame. There is no SPE-existence hypothesis. -/
theorem isSubgamePerfect_iff_equilibriumRegion (σ : Profile Move) (h : List Move) :
    G.IsSubgamePerfect σ h ↔ h ∈ G.equilibriumRegion σ := by
  rw [G.equilibriumRegion_iff_tests]
  exact forall_congr' fun _ => G.isNash_iff_region_tests

/-- Exact possible SPE winners of infinite finite-priority games. The right
side uses predecessor operators, genuine least/greatest fixedpoints, and an
existential complete-profile annotation. -/
theorem possibleWinners_eq_fixedpointPossibleWinners (h : List Move) :
    G.possibleWinners h = G.fixedpointPossibleWinners h := by
  ext i
  constructor
  · rintro ⟨σ, perfect, wins⟩
    exact ⟨σ, (G.isSubgamePerfect_iff_equilibriumRegion σ h).mp perfect,
      G.profile_winRegion_iff.mpr wins⟩
  · rintro ⟨σ, perfect, wins⟩
    exact ⟨σ, (G.isSubgamePerfect_iff_equilibriumRegion σ h).mpr perfect,
      G.profile_winRegion_iff.mp wins⟩

end KFOL.InfiniteGames.PriorityGame
