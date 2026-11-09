module

public import KFOL.Rounds.SerialRun.Prefix
public import KFOL.Rounds.SerialRun.Deviation
public import KFOL.Rounds.DecisionSites
public import KFOL.Rounds.TerminalErasure

/-! # Product-belief terminal continuations equal observed whole-policy laws -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.SerialRun

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG

universe u

variable {Role : Type u} [DecidableEq Role] [Fintype Role]

/-- The baseline product belief over earlier commitments is exactly the
canonical finite prefix-run law after replacing the scheduled player's whole
policy. Only earlier players have acted, so the replacement changes no mass. -/
theorem productBelief_history_eq_run_prefix_update (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (who : Role) (alternative : (game.serialized order).information.BehavioralPolicy who)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) :
    (game.productBelief order profile h ht who).map Subtype.val =
      (game.serialized order).information.runBehavioralFrom (Profile.update profile who alternative)
        (order.player.symm who).val (boundaryHistory game order h) := by
  change ((Serialization.prefixLaw game.toFOSG order profile h (order.player.symm who).val
      (order.player.symm who).isLt.le).map (game.prefixInformationHistory order h ht who)).map
      (fun x : (game.serialized order).information.InformationHistory who
        (scheduledView game.toFOSG who (game.information.infoOf who h.trace)) => x.val) = _
  rw [PMF.map_comp]
  change (Serialization.prefixLaw game.toFOSG order profile h (order.player.symm who).val
    (order.player.symm who).isLt.le).map
      (Serialization.historyAtPrefix game.toFOSG order h ht (order.player.symm who).val) = _
  have he := prefixLaw_update_before game order profile who alternative h (order.player.symm who).val le_rfl
  rw [← he,← run_prefix game order _ h ht (order.player.symm who).val]

/-- The actual complete terminal law under the baseline product belief and
an arbitrary whole-policy replacement erases exactly to the actual observed
continuation law under the projected replacement profile. This holds at every
public history, including histories of zero baseline reach. -/
theorem productBelief_terminal_deviation (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (who : Role) (alternative : (game.serialized order).information.BehavioralPolicy who)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) :
    ((game.productBelief order profile h ht who).bind fun x =>
      (game.serialized order).information.runBehavioralTerminalFrom
        (game.serial_well_founded_histories order) (Profile.update profile who alternative) x.val).map
        (eraseHistory game.toFOSG order) =
      game.information.runBehavioralTerminalFrom game.well_founded_histories
        (projectBehavioral game.toFOSG order (Profile.update profile who alternative)) h := by
  let changed := Profile.update (sig := (game.serialized order).information.behavioralSignature) profile who alternative
  calc
    _ = (((game.productBelief order profile h ht who).map Subtype.val).bind
        ((game.serialized order).information.runBehavioralTerminalFrom
          (game.serial_well_founded_histories order) changed)).map (eraseHistory game.toFOSG order) := by
      rw [PMF.bind_map]
      rfl
    _ = (((game.serialized order).information.runBehavioralFrom changed (order.player.symm who).val
        (boundaryHistory game order h)).bind
        ((game.serialized order).information.runBehavioralTerminalFrom
          (game.serial_well_founded_histories order) changed)).map (eraseHistory game.toFOSG order) := by
      rw [productBelief_history_eq_run_prefix_update]
    _ = ((game.serialized order).information.runBehavioralTerminalFrom
        (game.serial_well_founded_histories order) changed (boundaryHistory game order h)).map
        (eraseHistory game.toFOSG order) := by
      rw [← (game.serialized order).information.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom
        (game.serial_well_founded_histories order) changed (order.player.symm who).val (boundaryHistory game order h)]
    _ = _ := game.erase_terminal_continuation order changed h

/-- The same bridge read at the actual winner label, ready for the canonical
sequential-rationality utility comparison. -/
theorem productBelief_terminal_winner_deviation (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (who : Role) (alternative : (game.serialized order).information.BehavioralPolicy who)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) :
    ((game.productBelief order profile h ht who).bind fun x =>
      (game.serialized order).information.runBehavioralTerminalFrom
        (game.serial_well_founded_histories order) (Profile.update profile who alternative) x.val).map
        (game.serialWinner order) =
      (game.information.runBehavioralTerminalFrom game.well_founded_histories
        (projectBehavioral game.toFOSG order (Profile.update profile who alternative)) h).map game.winner := by
  calc
    _ = (((game.productBelief order profile h ht who).bind fun x =>
        (game.serialized order).information.runBehavioralTerminalFrom
          (game.serial_well_founded_histories order) (Profile.update profile who alternative) x.val).map
          (eraseHistory game.toFOSG order)).map game.winner := by
      rw [PMF.map_comp]
      rfl
    _ = _ := congrArg (PMF.map game.winner)
      (productBelief_terminal_deviation game order profile who alternative h ht)

/-- The baseline is the same canonical comparison with a self replacement. -/
theorem productBelief_terminal_baseline (game : Game Role) (order : ExplicitOrder Role)
    (profile : Profile (game.serialized order).information.behavioralSignature)
    (who : Role) (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) :
    ((game.productBelief order profile h ht who).bind fun x =>
      (game.serialized order).information.runBehavioralTerminalFrom
        (game.serial_well_founded_histories order) profile x.val).map (eraseHistory game.toFOSG order) =
      game.information.runBehavioralTerminalFrom game.well_founded_histories
        (projectBehavioral game.toFOSG order profile) h := by
  simpa only [Profile.update_eq_self] using
    productBelief_terminal_deviation game order profile who (profile who) h ht

end KFOL.Rounds.Game.SerialRun
