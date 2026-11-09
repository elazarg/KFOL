module

public import KFOL.Rounds.InformationFibers
public import KFOL.Rounds.PrefixLaw

/-! # Canonical decision sites at every disclosed public history -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Languages.Bridges.FOSGToEFG
open GameTheory.Math.Probability
universe u
variable {Role : Type u} [DecidableEq Role]

/-- One legal prefix witness: each earlier role chooses its available zero.
It is used only to certify a decision site, never as an equilibrium strategy. -/
def zeroPrefix (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    (n : ℕ) (hn : n ≤ order.slots) : Prefix game.toFOSG order h n where
  count_le := hn
  choices i := if (order.player.symm i).val < n then
    some ⟨some 0,ht,Nat.zero_le _⟩ else none
  selected_iff i := by split <;> simp_all

/-- Every role has an actual decision at every nonterminal public prefix,
even when its menu is forced or its public reach under a strategy is zero. -/
def serialSite (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    (game.serialized order).information.InformationSite i := by
  let p := game.zeroPrefix order h ht (order.player.symm i).val (order.player.symm i).isLt.le
  let history := game.prefixInformationHistory order h ht i p
  refine ⟨scheduledView game.toFOSG i (game.information.infoOf i h.trace),history,ht,0,?_⟩
  let sourceChoice : ChoiceAt game.toFOSG h i := ⟨some 0,ht,Nat.zero_le _⟩
  exact ((choiceEquiv game.toFOSG order i (game.information.infoOf i h.trace)).symm
    ((Serialization.choiceAtEquiv game.toFOSG h i).symm sourceChoice)).property

/-- Actual product beliefs on the complete decision-history fiber. -/
def productBelief (game : Game Role) (order : ExplicitOrder Role)
    (policies : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role) :
    PMF ((game.serialized order).information.InformationHistory i
      (game.serialSite order h ht i).val) :=
  (Serialization.prefixLaw game.toFOSG order policies h (order.player.symm i).val
    (order.player.symm i).isLt.le).map (game.prefixInformationHistory order h ht i)


/-- Every genuine serial decision site is one of the canonical scheduled
views over a unique disclosed public history. -/
theorem serialSite_surjective (game : Game Role) (order : ExplicitOrder Role) (i : Role)
    (site : (game.serialized order).information.InformationSite i) :
    ∃ (h : game.execution.History) (ht : ¬ game.execution.terminal h.state),
      site = game.serialSite order h ht i := by
  obtain ⟨witness,hterm,action,_⟩ := site.property
  have hactive := InformationModel.InformationSite.active (game.serialized order).information site witness
  rcases witness with ⟨⟨state,trace⟩,hinfo⟩
  cases state with
  | stage h n p =>
    refine ⟨h,hterm,Subtype.ext ?_⟩
    have hv := infoOf_eq_viewOfState game.toFOSG order i trace
    obtain ⟨hc,hi,_⟩ := hactive
    change site.val = scheduledView game.toFOSG i (game.information.infoOf i h.trace)
    calc
      _ = (game.serialized order).information.infoOf i trace := hinfo.symm
      _ = viewOfState game.toFOSG order i (.stage h n p) := hv
      _ = _ := by
        simp only [viewOfState,phaseOfState_select game.toFOSG order p hc,State.history,scheduledView]
        rw [← hi]

end KFOL.Rounds.Game
