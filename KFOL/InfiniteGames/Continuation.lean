module

public import KFOL.InfiniteGames.Priorities
public import KFOL.InfiniteGames.Grafting

/-! # Priority games supply genuine public continuation interfaces -/

@[expose] public section

namespace KFOL.InfiniteGames.PriorityGame

universe u v

variable {Role : Type u} {Move : Type v} {n : ℕ}
variable (G : PriorityGame Role Move n)

/-- The generic public-grafting interface of a priority game. Its equilibrium
predicate is the independently specified full-deviation SPE at the root. -/
noncomputable def asContinuation : PublicGrafting.Continuation.{u, v} Role where
  Plan := Profile Move
  winner σ := (G.wins_exists_unique (run σ [])).choose
  deviation := G.Deviation
  deviation_refl _ _ _ _ := rfl
  perfect σ := G.IsSubgamePerfect σ []
  perfect_nash := by
    intro σ hσ i τ deviation wins
    have τ_wins : G.Wins i (run τ []) := by
      rw [← wins]
      exact (G.wins_exists_unique (run τ [])).choose_spec.1
    have σ_wins : G.Wins i (run σ []) := hσ [] i τ deviation τ_wins
    exact ((G.wins_exists_unique (run σ [])).choose_spec.2 i σ_wins).symm

theorem asContinuation_possibleWinners :
    G.asContinuation.possibleWinners = G.possibleWinners [] := by
  ext i
  constructor
  · rintro ⟨σ, hσ, winner⟩
    refine ⟨σ, hσ, ?_⟩
    rw [← winner]
    exact (G.wins_exists_unique (run σ [])).choose_spec.1
  · rintro ⟨σ, hσ, wins⟩
    exact ⟨σ, hσ, ((G.wins_exists_unique (run σ [])).choose_spec.2 i wins).symm⟩

/-- In particular, arbitrary infinite priority continuations compose by the
same owned choice, extended strictly at an empty SPE set. -/
theorem graft_possibleWinners_eq_strictChoice {Move' : Type v} {m : ℕ}
    (H : PriorityGame Role Move' m) (owner : Role) :
    PublicGrafting.possibleWinners owner G.asContinuation H.asContinuation =
      PublicGrafting.strictChoice owner (G.possibleWinners []) (H.possibleWinners []) := by
  rw [PublicGrafting.possibleWinners_eq_strictChoice,
    G.asContinuation_possibleWinners, H.asContinuation_possibleWinners]

end KFOL.InfiniteGames.PriorityGame
