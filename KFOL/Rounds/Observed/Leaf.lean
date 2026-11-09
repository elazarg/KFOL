module

public import KFOL.Rounds.Observed.Optimality

/-! # The canonical observed-SPE leaf value is its winner point mass -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol

universe u

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

/-- A terminal game has its actual unique local option, `none`. -/
def leafProfile (r : Role) : Profile (Game.leaf r).information.behavioralSignature :=
  fun _ p => match p with
  | .root => PMF.pure ⟨none,by intro h; exact h trivial⟩

omit [Fintype Role] [DecidableEq Role] in
/-- No transition is needed at a leaf, including in every deviation. -/
theorem leaf_bounded (r : Role) : (Game.leaf r).execution.BoundedHorizon 0 := by
  intro p _ _
  cases p
  trivial

theorem leaf_perfect (r : Role) :
    (Game.leaf r).information.IsBehavioralSubgamePerfect (leaf_bounded r) (leafProfile r)
      (fun h i => winnerPayoff (Game.leaf r).winner i h) := by
  apply (subgamePerfect_iff_winner_coordinates (.leaf r) (leaf_bounded r) _).mpr
  intro h who alternative
  exact le_rfl

/-- The leaf equation is proved for the actual independent canonical SPE
predicate and history runner, with a concrete profile witness. -/
theorem observedValues_leaf (r : Role) : (Game.leaf r).observedValues = {PMF.pure r} := by
  ext value
  constructor
  · rintro ⟨bound,_bounded,profile,_perfect,rfl⟩
    have he : (Game.leaf r).winner = Function.const (Game.leaf r).execution.History r :=
      funext (winner_leaf r)
    simp only [he,PMF.map_const,Set.mem_singleton_iff]
  · intro he
    have hv : value = PMF.pure r := Set.mem_singleton_iff.mp he
    refine ⟨0,leaf_bounded r,leafProfile r,leaf_perfect r,?_⟩
    rw [hv]
    change PMF.pure r = (PMF.pure (Game.leaf r).execution.initHistory).map (Game.leaf r).winner
    rw [PMF.pure_map]
    rfl

end KFOL.Rounds.Game.Observed
