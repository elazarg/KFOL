module

public import KFOL.Rounds.Observed.Sufficiency
public import KFOL.Rounds.Observed.Leaf

/-! # Complete canonical observed mixed-SPE round recursion -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe u

variable {Role : Type u} [Fintype Role] [DecidableEq Role]

/-- Every selected-continuation mixed-stage value is attained by a canonical
observed SPE. Arbitrary child certificates are normalized to the actual
parent's certified horizon before constructing its whole policies. -/
theorem roundOperator_subset_observedValues (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i+1)) → Game Role) :
    roundOperator sizes (fun a => (next a).observedValues) ⊆ (Game.round sizes next).observedValues := by
  intro value hvalue
  obtain ⟨p,hp,root,nash,hvalue⟩ := hvalue
  change ((i : Role) → PMF (Fin (sizes i+1))) at root
  choose childBounds certified children perfect values using hp
  obtain ⟨bound,_positive,bounded⟩ := (Game.round sizes next).exists_bounded_horizon
  have perfectAligned (a) : (next a).information.IsBehavioralSubgamePerfect
      (child_bounded_horizon sizes next bounded a) (children a)
      (fun h i => winnerPayoff (next a).winner i h) :=
    ((next a).information.isBehavioralSubgamePerfect_bound_iff (certified a)
      (child_bounded_horizon sizes next bounded a) _ _).mp (perfect a)
  have valuesAligned (a) : ((next a).information.runBehavioralFrom (children a) (bound-1)
      (next a).execution.initHistory).map (next a).winner = p a := by
    have hr := runBehavioral_bounds_eq (next a) (certified a)
      (child_bounded_horizon sizes next bounded a) (children a) (next a).execution.initHistory
    exact (congrArg (PMF.map (next a).winner) hr.symm).trans (values a).symm
  refine ⟨bound,bounded,assembleProfile sizes next root children,
    assemble_subgamePerfect sizes next bounded root children perfectAligned p valuesAligned nash,?_⟩
  have positive := round_bound_positive sizes next bounded
  have hb : bound = (bound-1)+1 := by omega
  rw [hvalue,hb,runBehavioral_round_winner]
  change (independentProduct root).bind p =
    (independentProduct (rootProfile sizes next (assembleProfile sizes next root children))).bind
      (fun a => ((next a).information.runBehavioralFrom
        (childProfile sizes next (assembleProfile sizes next root children) a) (bound-1)
        (next a).execution.initHistory).map (next a).winner)
  simp only [rootProfile_assemble,childProfile_assemble,valuesAligned]

/-- The complete round equation for the independently defined canonical
observed mixed-SPE winner distributions. All actual tuples, including
zero-probability ones and equal continuation syntax, are selected separately. -/
theorem observedValues_round (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i+1)) → Game Role) :
    (Game.round sizes next).observedValues = roundOperator sizes (fun a => (next a).observedValues) :=
  Set.Subset.antisymm (observedValues_round_subset sizes next) (roundOperator_subset_observedValues sizes next)

/-- Explicit complete selected-continuation proposition for a paper-facing
statement, with canonical mixed Nash and actual winner PMFs. -/
theorem observedValues_round_iff (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i+1)) → Game Role) (value : PMF Role) :
    value ∈ (Game.round sizes next).observedValues ↔
      ∃ p : ((i : Role) → Fin (sizes i+1)) → PMF Role,
        (∀ a, p a ∈ (next a).observedValues) ∧
        ∃ root : Profile (stageForm sizes p).sig.mixed,
          IsNash (stageForm sizes p).mixed
            (euPreference (fun winner i => winnerPayoff id i winner)) root ∧
          value = (stageForm sizes p).mixed.play root := by
  rw [observedValues_round]
  rfl

end KFOL.Rounds.Game.Observed
