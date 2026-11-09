module

public import KFOL.Rounds.Tree

/-! # Recall at serialized commitment decisions

The serializer may forget a player's commitment at an intermediate inactive
observation. At its next decision, the disclosed public prefix records it.
-/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Serialization

open GameTheory.Protocol GameTheory.Languages
open Bridges.FOSGToEFG

universe uι us ua up uq uk
variable {Role : Type uι} [DecidableEq Role]
variable (G : FOSG.Game.{uι,us,ua,up,uq,uk} Role) (order : ExplicitOrder Role)

/-- Completed source decisions, with their scheduled serial information. -/
def completedRecord (i : Role) (h : G.execution.History) :
    List (View G i × G.execution.Action i) :=
  (G.information.ownPlay i h.trace).map (fun p => (⟨.select i,p.1⟩,p.2))

/-- The current commitment appears only after this player's slot. -/
def prefixRecord (i : Role) : State G order → List (View G i × G.execution.Action i)
  | .stage h _ collected => match collected.choices i with
    | none => completedRecord G i h
    | some c => match c.val with
      | none => completedRecord G i h
      | some a => (⟨.select i,G.information.infoOf i h.trace⟩,a) :: completedRecord G i h

set_option backward.isDefEq.respectTransparency false in
/-- Exact own-play memory along every legal serialized trace. -/
theorem ownPlay_eq_record (i : Role) :
    ∀ {state : State G order} (trace : (execution G order).Trace state),
      (information G order).ownPlay i trace = prefixRecord G order i state
  | _, .start => rfl
  | target, .extend (source := source) prior joint isLegal realized => by
    have hprior := ownPlay_eq_record i prior
    cases source with
    | stage history count collected =>
      by_cases hcount : count < order.slots
      · rw [step_select G order collected hcount joint isLegal,
          PMF.mem_support_pure_iff] at realized
        subst target
        rw [InfoSignals.ownPlay_extend,hprior]
        rw [infoOf_eq_viewOfState G order]
        by_cases hi : i = scheduledPlayer G order collected hcount
        · subst i
          have hnone : collected.choices (scheduledPlayer G order collected hcount) = none := by
            apply Option.not_isSome_iff_eq_none.mp
            simp only [collected.selected_iff,scheduledPlayer,Equiv.symm_apply_apply]
            exact Nat.lt_irrefl _
          simp only [prefixRecord,Prefix.advance,scheduledPlayer,dite_true,choiceOfJoint]
          simp only [scheduledPlayer] at hnone
          rw [hnone]
          simp only [viewOfState,phaseOfState,hcount,dite_true,State.history,scheduledPlayer]
          cases joint (order.player ⟨count,hcount⟩) <;> rfl
        · have hnone : joint i = none := by
            apply LegalOption.eq_none_of_inactive (joint i)
              ((execution G order).legalOption_of_legal isLegal i)
            intro ha
            exact hi ha.2.1
          rw [hnone]
          simp only [scheduledPlayer] at hi
          simp only [prefixRecord,Prefix.advance,hi,dite_false]
      · have hcountEq : count = order.slots :=
          Nat.le_antisymm collected.count_le (Nat.le_of_not_gt hcount)
        subst count
        rw [step_resolve G order collected joint isLegal] at realized
        have hmem := (mem_support_resolve_iff G order collected isLegal.1 target).mp realized
        obtain ⟨reached,sourceRealized,rfl⟩ := hmem
        have hnone : joint i = none := by
          apply LegalOption.eq_none_of_inactive (joint i)
            ((execution G order).legalOption_of_legal isLegal i)
          intro ha
          exact (Nat.lt_irrefl _) ha.1
        rw [InfoSignals.ownPlay_extend,hnone,hprior]
        simp only [prefixRecord,Prefix.initial,completedRecord]
        unfold ExecutionProtocol.History.extend
        rw [InfoSignals.ownPlay_extend]
        have hc : collected.choices i = some (collected.completedChoice i) :=
          (Option.some_get _).symm
        rw [hc]
        cases hi : (collected.completedChoice i).val <;>
          simp only [Prefix.joint,hi,List.map_cons]


/-- At the next genuine decision the player has not yet committed in the
current round; its remembered actions are exactly the completed source record. -/
theorem prefixRecord_at_active (i : Role) (state : State G order)
    (ha : (execution G order).active state i) :
    prefixRecord G order i state = completedRecord G i state.history := by
  cases state with
  | stage history count collected =>
    obtain ⟨hc,hi,_⟩ := ha
    subst i
    have hnone : collected.choices (scheduledPlayer G order collected hc) = none := by
      apply Option.not_isSome_iff_eq_none.mp
      simp only [collected.selected_iff,scheduledPlayer,Equiv.symm_apply_apply]
      exact Nat.lt_irrefl _
    simp only [prefixRecord,hnone,State.history]

/-- Source recall transfers at every serial decision, including off-path
public histories. Inactive intermediate observations need not remember a
commitment that is not yet disclosed. -/
theorem decisionRecall_of_perfectRecall (hrecall : G.information.PerfectRecall) :
    (information G order).DecisionRecall := by
  intro i site first second
  rw [ownPlay_eq_record G order,ownPlay_eq_record G order]
  rw [prefixRecord_at_active G order i _ (InformationModel.InformationSite.active (information G order) site first),
    prefixRecord_at_active G order i _ (InformationModel.InformationSite.active (information G order) site second)]
  have hv : viewOfState G order i first.val.state = viewOfState G order i second.val.state :=
    (infoOf_eq_viewOfState G order i first.val.trace).symm.trans
      ((first.property.trans second.property.symm).trans
        (infoOf_eq_viewOfState G order i second.val.trace))
  have hs := congrArg (View.source (G := G) (player := i)) hv
  exact congrArg (List.map (fun p : G.information.InfoState i × G.execution.Action i =>
      ((⟨Phase.select i,p.1⟩ : View G i),p.2)))
    (hrecall i first.val.state.history.trace second.val.state.history.trace hs)

end KFOL.Rounds.Serialization
