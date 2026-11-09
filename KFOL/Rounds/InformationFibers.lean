module

public import KFOL.Rounds.SerializationTrace
public import KFOL.Rounds.Reachability

/-! # Exact serial decision fibers over a disclosed public history -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role]

/-- A partial commitment gives an actual history at the player's current
selection view, including when its public prefix has zero strategy reach. -/
def prefixInformationHistory (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role)
    (p : Prefix game.toFOSG order h (order.player.symm i).val) :
    (game.serialized order).information.InformationHistory i
      (scheduledView game.toFOSG i (game.information.infoOf i h.trace)) := by
  let trace := Serialization.prefixTrace game.toFOSG order
    (Serialization.boundaryTrace game.toFOSG order h.trace) ht _ p
  refine ⟨⟨.stage h _ p,trace⟩,?_⟩
  rw [infoOf_eq_viewOfState game.toFOSG order]
  simp only [viewOfState,State.history,scheduledView,phaseOfState_select
    game.toFOSG order p (order.player.symm i).isLt,scheduledPlayer]
  change (⟨.select (order.player (order.player.symm i)),_⟩ : View game.toFOSG i) = _
  rw [Equiv.apply_symm_apply]

theorem prefixInformationHistory_injective (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    Function.Injective (game.prefixInformationHistory order h ht i) := by
  intro p q he
  have hs := congrArg (fun x => x.val.state) he
  change State.stage (G := game.toFOSG) (order := order) h (order.player.symm i).val p =
    State.stage (G := game.toFOSG) (order := order) h (order.player.symm i).val q at hs
  cases hs
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The only hidden data at a decision is the earlier commitments in this
round. No earlier public history or future action lies in the fiber. -/
theorem prefixInformationHistory_surjective (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    Function.Surjective (game.prefixInformationHistory order h ht i) := by
  rintro ⟨⟨state,trace⟩,hi⟩
  cases state with
  | stage other n p =>
    have hv : viewOfState game.toFOSG order i (.stage other n p) =
        scheduledView game.toFOSG i (game.information.infoOf i h.trace) :=
      (infoOf_eq_viewOfState game.toFOSG order i trace).symm.trans hi
    have hp := congrArg View.source hv
    change game.information.infoOf i other.trace = game.information.infoOf i h.trace at hp
    rw [information_eq_position,information_eq_position] at hp
    have hh : other = h := (game.historyEquivPosition).injective hp
    subst other
    have hphase := congrArg View.phase hv
    change phaseOfState game.toFOSG order (.stage h n p) = .select i at hphase
    have hn : n = (order.player.symm i).val := by
      by_cases hcnt : n < order.slots
      · have he : order.player ⟨n,hcnt⟩ = i := Phase.select.inj (by
          simpa only [phaseOfState,hcnt,dite_true,scheduledPlayer] using hphase)
        have := congrArg (fun j => (order.player.symm j).val) he
        simpa only [Equiv.symm_apply_apply] using this
      · simp only [phaseOfState,hcnt,dite_false] at hphase
        cases hphase
    subst n
    refine ⟨p,?_⟩
    apply Subtype.ext
    change (⟨_,Serialization.prefixTrace game.toFOSG order
      (Serialization.boundaryTrace game.toFOSG order h.trace) ht _ p⟩ :
      (game.serialized order).execution.History) = ⟨_,trace⟩
    congr 1
    exact trace_unique game.toFOSG order _ _

/-- An actual canonical decision fiber is exactly the finite legal prefix
carrier. This is an equivalence of histories, not just an erasure of outcomes. -/
def informationHistoryEquivPrefix (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    (game.serialized order).information.InformationHistory i
      (scheduledView game.toFOSG i (game.information.infoOf i h.trace)) ≃
        Prefix game.toFOSG order h (order.player.symm i).val :=
  (Equiv.ofBijective (game.prefixInformationHistory order h ht i)
    ⟨game.prefixInformationHistory_injective order h ht i,
      game.prefixInformationHistory_surjective order h ht i⟩).symm

end KFOL.Rounds.Game
