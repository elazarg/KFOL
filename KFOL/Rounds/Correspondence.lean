module

public import KFOL.Rounds.SerialOptimality
public import KFOL.Rounds.Projection
public import KFOL.Rounds.SerialRun.Terminal
public import KFOL.Rounds.Observed

/-! # Canonical serial sequential equilibrium and observed mixed SPE -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- With canonical consistent beliefs, sequential rationality is exactly
whole-policy optimality in every observed public subgame, including off-path
subgames. No equilibrium predicate is defined through the round recursion. -/
theorem consistent_rationality_iff_subgamePerfect (game : Game Role) (order : ExplicitOrder Role)
    (assessment : (game.serialized order).information.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (game.serial_decision_recall order).decisionInformationAntichain)
    {bound : Nat} (bounded : game.execution.BoundedHorizon bound) :
    assessment.IsSequentiallyRational (game.serial_well_founded_histories order)
      (winnerPayoff (game.serialWinner order)) ↔
    game.information.IsBehavioralSubgamePerfect bounded
      (projectBehavioral game.toFOSG order assessment.strategy)
      (fun h i => winnerPayoff game.winner i h) := by
  rw [game.serial_rationality_iff_public_coordinates order assessment,
    game.subgamePerfect_iff_terminal_coordinates bounded]
  have baseline (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (who : Role) := by
    simpa only [Profile.update_eq_self] using
      SerialRun.productBelief_terminal_winner_deviation game order assessment.strategy who
        (assessment.strategy who) h ht
  constructor
  · intro optimal h who alternative
    by_cases ht : game.execution.terminal h.state
    · exact game.terminal_comparison _ h ht who alternative
    · obtain ⟨replacement,he⟩ := game.lift_source_deviation order assessment.strategy who alternative
      have hc := optimal h ht who replacement
      rw [game.consistent_belief_eq_product order assessment consistent h ht who,
        SerialRun.productBelief_terminal_winner_deviation,baseline,he] at hc
      exact hc
  · intro optimal h ht who alternative
    rw [game.consistent_belief_eq_product order assessment consistent h ht who,
      SerialRun.productBelief_terminal_winner_deviation,baseline,projectBehavioral_update]
    exact optimal h who _

/-- Exact equality of the paper's independently defined serial-SE values and
canonical observed mixed-SPE values. Consistency is constructed for every
lifted source profile and constrains beliefs even at zero-reach histories. -/
theorem sequentialValues_eq_observedValues (game : Game Role) (order : ExplicitOrder Role) :
    game.sequentialValues order = game.observedValues := by
  obtain ⟨bound,_positive,bounded⟩ := game.exists_bounded_horizon
  have rootLaw (profile : (i : Role) → (game.serialized order).information.BehavioralPolicy i) :
      ((game.serialized order).information.runBehavioralTerminalFrom
        (game.serial_well_founded_histories order) profile
        (game.serialized order).execution.initHistory).map (game.serialWinner order) =
      (game.information.runBehavioralFrom (projectBehavioral game.toFOSG order profile)
        bound game.execution.initHistory).map game.winner := by
    calc
      _ = (game.information.runBehavioralTerminalFrom game.well_founded_histories
          (projectBehavioral game.toFOSG order profile) game.execution.initHistory).map game.winner :=
        game.terminal_winner_law order profile game.execution.initHistory
      _ = _ := congrArg (PMF.map game.winner)
        (game.information.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
          game.well_founded_histories bounded _ _)
  ext value
  constructor
  · rintro ⟨certificate,antichain,assessment,hse,hvalue⟩
    have hr := hse.1
    have hc := hse.2
    refine ⟨bound,bounded,projectBehavioral game.toFOSG order assessment.strategy,
      (game.consistent_rationality_iff_subgamePerfect order assessment hc bounded).mp hr,?_⟩
    exact hvalue.trans (rootLaw assessment.strategy)
  · rintro ⟨sourceBound,sourceBounded,profile,perfect,hvalue⟩
    obtain ⟨assessment,he,consistent,_products⟩ := game.exists_consistent_product_assessment order
      (translateBehavioral game.toFOSG order profile)
    have hp : projectBehavioral game.toFOSG order assessment.strategy = profile := by
      rw [he,project_translate_profile]
    refine ⟨game.serial_well_founded_histories order,
      (game.serial_decision_recall order).decisionInformationAntichain,assessment,
      ⟨(game.consistent_rationality_iff_subgamePerfect order assessment consistent sourceBounded).mpr
        (by simpa only [hp] using perfect),consistent⟩,?_⟩
    rw [rootLaw,hp]
    exact hvalue.trans (congrArg (PMF.map game.winner)
      (Observed.runBehavioral_bounds_eq game sourceBounded bounded profile game.execution.initHistory))

/-- The complete serial-SE round recursion, selecting an equilibrium law at
every actual tuple and then a mixed Nash equilibrium of that finite stage. -/
theorem sequentialValues_round (sizes : Role → Nat)
    (next : ((i : Role) → Fin (sizes i+1)) → Game Role) (order : ExplicitOrder Role) :
    (Game.round sizes next).sequentialValues order =
      roundOperator sizes (fun a => (next a).sequentialValues order) := by
  simp only [sequentialValues_eq_observedValues,Observed.observedValues_round]

/-- The round equation with every existential and its Nash predicate explicit. -/
theorem sequentialValues_round_iff (sizes : Role → Nat)
    (next : ((i : Role) → Fin (sizes i+1)) → Game Role) (order : ExplicitOrder Role)
    (value : PMF Role) :
    value ∈ (Game.round sizes next).sequentialValues order ↔
      ∃ p : ((i : Role) → Fin (sizes i+1)) → PMF Role,
        (∀ a, p a ∈ (next a).sequentialValues order) ∧
        ∃ root : Profile (stageForm sizes p).sig.mixed,
          IsNash (stageForm sizes p).mixed
            (euPreference (fun winner i => winnerPayoff id i winner)) root ∧
          value = (stageForm sizes p).mixed.play root := by
  rw [sequentialValues_round]
  rfl

end KFOL.Rounds.Game
