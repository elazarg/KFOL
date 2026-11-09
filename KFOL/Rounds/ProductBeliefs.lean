module

public import KFOL.Rounds.DecisionSites
public import KFOL.Rounds.Consistency
public import KFOL.Rounds.PrefixReach
public import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Product Bayes beliefs, including off-path public prefixes -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Math.Probability
open scoped ENNReal
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
set_option backward.isDefEq.respectTransparency false

variable {Role : Type u} [DecidableEq Role] [Finite Role]

/-- Exact canonical reach weights on the actual information-history fiber. -/
theorem productBelief_reach_factor (game : Game Role) (order : ExplicitOrder Role)
    (policies : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role)
    (x : (game.serialized order).information.InformationHistory i
      (game.serialSite order h ht i).val) :
    ((game.serialized order).information.historyReachWeight policies x.val).toReal =
    ((game.serialized order).information.historyReachWeight policies
      (Serialization.historyAtPrefix game.toFOSG order h ht 0
        (Prefix.initial (G := game.toFOSG) (order := order) h))).toReal *
      (game.productBelief order policies h ht i x).toReal := by
  obtain ⟨p,rfl⟩ := game.prefixInformationHistory_surjective order h ht i x
  have hm : game.productBelief order policies h ht i
      (game.prefixInformationHistory order h ht i p) =
      Serialization.prefixLaw game.toFOSG order policies h (order.player.symm i).val
        (order.player.symm i).isLt.le p :=
    pmf_map_apply_of_injective _ (game.prefixInformationHistory_injective order h ht i) p
  exact (game.prefix_reach_factor order policies h ht _ (order.player.symm i).isLt.le p).trans
    (congrArg (fun weight =>
      ((game.serialized order).information.historyReachWeight policies
        (Serialization.historyAtPrefix game.toFOSG order h ht 0
          (Prefix.initial (G := game.toFOSG) (order := order) h))).toReal * weight.toReal) hm.symm)

/-- Normalization sums out precisely the earlier commitments, leaving the
public reach factor. No positivity assumption is needed for this identity. -/
theorem serial_informationMass_toReal (game : Game Role) (order : ExplicitOrder Role)
    (policies : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    ((game.serialized order).information.informationMass policies i
      (game.serialSite order h ht i)).toReal =
    ((game.serialized order).information.historyReachWeight policies
      (Serialization.historyAtPrefix game.toFOSG order h ht 0
        (Prefix.initial (G := game.toFOSG) (order := order) h))).toReal := by
  change (∑' x : (game.serialized order).information.InformationHistory i
      (scheduledView game.toFOSG i (game.information.infoOf i h.trace)),
      (game.serialized order).information.historyReachWeight policies x.val).toReal = _
  calc
    _ = ∑' x : (game.serialized order).information.InformationHistory i
        (scheduledView game.toFOSG i (game.information.infoOf i h.trace)),
        ((game.serialized order).information.historyReachWeight policies x.val).toReal :=
      ENNReal.tsum_toReal_eq (fun _ => PMF.apply_ne_top _ _)
    _ = ∑' x, ((game.serialized order).information.historyReachWeight policies
        (Serialization.historyAtPrefix game.toFOSG order h ht 0
          (Prefix.initial (G := game.toFOSG) (order := order) h))).toReal *
        (game.productBelief order policies h ht i x).toReal :=
      tsum_congr (game.productBelief_reach_factor order policies h ht i)
    _ = _ := by rw [tsum_mul_left,pmf_weight_tsum_one,mul_one]

/-- Fully mixed Bayes beliefs are exactly the product of earlier commitment
laws. The public factor cancels before taking any off-path limit. -/
theorem fullyMixed_bayes_belief_eq_product (game : Game Role) (order : ExplicitOrder Role)
    (assessment : (game.serialized order).information.BehavioralAssessment)
    (hfull : assessment.IsFullyMixed)
    (hbayes : InformationModel.BehavioralAssessment.IsBayesConsistent
      (game.serialized order).information assessment
      (game.serial_decision_recall order).decisionInformationAntichain)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    assessment.belief i (game.serialSite order h ht i) =
      game.productBelief order assessment.strategy h ht i := by
  let site := game.serialSite order h ht i
  have hmass := (game.serialized order).information.informationMass_pos_of_fullSupport
    assessment.strategy hfull i site
  have hfinite := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((game.serialized order).information.informationMass_le_one assessment.strategy i site
      ((game.serial_decision_recall order).decisionInformationAntichain i site))
  have hC : ((game.serialized order).information.historyReachWeight assessment.strategy
      (Serialization.historyAtPrefix game.toFOSG order h ht 0
        (Prefix.initial (G := game.toFOSG) (order := order) h))).toReal ≠ 0 := by
    rw [← game.serial_informationMass_toReal order assessment.strategy h ht i]
    exact (ENNReal.toReal_pos hmass.ne' hfinite).ne'
  apply pmf_ext_toReal
  intro x
  rw [hbayes i site hmass x,ENNReal.toReal_div,
    game.productBelief_reach_factor order assessment.strategy h ht i,
    game.serial_informationMass_toReal order assessment.strategy h ht i]
  exact mul_div_cancel_left₀ _ hC


omit [Finite Role] in
/-- Strategy limits at canonical decision sites induce limits of the actual
finite product beliefs, independently of public reach probabilities. -/
theorem productBelief_converges (game : Game Role) (order : ExplicitOrder Role)
    (sequence : ℕ → (game.serialized order).information.BehavioralAssessment)
    (assessment : (game.serialized order).information.BehavioralAssessment)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    PMFConvergesPointwise
      (fun n => game.productBelief order (sequence n).strategy h ht i)
      (game.productBelief order assessment.strategy h ht i) := by
  have hc (j : Role) : PMFConvergesPointwise
      (fun n => Serialization.currentLaw game.toFOSG order (sequence n).strategy h j)
      (Serialization.currentLaw game.toFOSG order assessment.strategy h j) :=
    (converges.strategy j (game.serialSite order h ht j)).map
      ((choiceEquiv game.toFOSG order j (game.information.infoOf j h.trace)).trans
        (Serialization.choiceAtEquiv game.toFOSG h j))
  exact (Serialization.prefixLaw_converges game.toFOSG order
    (fun n => (sequence n).strategy) assessment.strategy h hc
    (order.player.symm i).val (order.player.symm i).isLt.le).map
      (game.prefixInformationHistory order h ht i)

/-- Kreps-Wilson consistency uniquely forces product beliefs at every public
prefix, including prefixes unreachable under the limit strategy. -/
theorem consistent_belief_eq_product (game : Game Role) (order : ExplicitOrder Role)
    (assessment : (game.serialized order).information.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (game.serial_decision_recall order).decisionInformationAntichain)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    assessment.belief i (game.serialSite order h ht i) =
      game.productBelief order assessment.strategy h ht i := by
  obtain ⟨sequence,approximate,converges⟩ := consistent
  have hs (n : ℕ) : (sequence n).belief i (game.serialSite order h ht i) =
      game.productBelief order (sequence n).strategy h ht i :=
    game.fullyMixed_bayes_belief_eq_product order (sequence n)
      (approximate n).1 (approximate n).2 h ht i
  apply (converges.belief i (game.serialSite order h ht i)).unique
  convert game.productBelief_converges order sequence assessment converges h ht i using 1
  exact funext hs


/-- Every target profile admits consistent beliefs, and those beliefs are the
actual product laws at all public prefixes, even when their reach is zero. -/
theorem exists_consistent_product_assessment (game : Game Role) (order : ExplicitOrder Role)
    (strategy : (i : Role) → (game.serialized order).information.BehavioralPolicy i) :
    ∃ assessment : (game.serialized order).information.BehavioralAssessment,
      assessment.strategy = strategy ∧
      assessment.IsSequentiallyConsistent
        (game.serial_decision_recall order).decisionInformationAntichain ∧
      ∀ (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role),
        assessment.belief i (game.serialSite order h ht i) =
          game.productBelief order strategy h ht i := by
  obtain ⟨assessment,heq,hconsistent⟩ := exists_consistent_assessment
    (game.serialized order).information
    (game.serial_decision_recall order).decisionInformationAntichain strategy
  refine ⟨assessment,heq,hconsistent,?_⟩
  intro h ht i
  simpa only [heq] using game.consistent_belief_eq_product order assessment hconsistent h ht i

end KFOL.Rounds.Game
