module

public import KFOL.Rounds.PrefixLaw
public import KFOL.Rounds.SequentialExistence
public import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Actual canonical probability of one hidden commitment -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game
open GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
private theorem dependentLaw_apply {I : Type*} {A : Type*} (P : I → Set A)
    (law : (i : I) → PMF (P i)) {i j : I} (h : i = j)
    (a : P i) (b : P j) (ha : a.val = b.val) : law i a = law j b := by
  subst j
  have he : a = b := Subtype.ext ha
  rw [he]

variable {Role : Type u} [DecidableEq Role] [Finite Role]

/-- At a scheduled slot only that role contributes to the product law. Forced
one-action menus are included exactly, with probability one. -/
theorem serial_movers (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    {n : ℕ} (p : Prefix game.toFOSG order h n) (hn : n < order.slots) :
    (game.serialized order).execution.movers (.stage h n p) = {order.player ⟨n,hn⟩} := by
  ext i
  simp only [ExecutionProtocol.mem_movers,Finset.mem_singleton]
  constructor
  · intro ha
    exact ha.2.1
  · intro hi
    exact ⟨hn,hi,ht⟩

omit [Finite Role] in
/-- The raw policy value at the serial slot reads precisely the fixed public
view, independently of the earlier current commitments. -/
theorem serial_scheduled_info (game : Game Role) (order : ExplicitOrder Role)
    (h : game.execution.History) {n : ℕ} (p : Prefix game.toFOSG order h n)
    (hn : n < order.slots)
    (trace : (game.serialized order).execution.Trace (.stage h n p)) :
    (game.serialized order).information.infoOf (order.player ⟨n,hn⟩) trace =
      scheduledView game.toFOSG (order.player ⟨n,hn⟩)
        (game.information.infoOf (order.player ⟨n,hn⟩) h.trace) := by
  rw [infoOf_eq_viewOfState game.toFOSG order]
  simp only [viewOfState,phaseOfState_select game.toFOSG order p hn,scheduledPlayer,
    State.history,scheduledView]

set_option backward.isDefEq.respectTransparency false in
/-- The probability of the actual selected joint equals the scheduled
information-local marginal on its original legal choice. -/
theorem serial_selection_probability (game : Game Role) (order : ExplicitOrder Role)
    (policies : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    {n : ℕ} (p : Prefix game.toFOSG order h n) (hn : n < order.slots)
    (trace : (game.serialized order).execution.Trace (.stage h n p))
    (c : ChoiceAt game.toFOSG h (order.player ⟨n,hn⟩)) :
    (((game.serialized order).information.behavioralJoint policies trace ht)
      ⟨selectedJoint game.toFOSG (order.player ⟨n,hn⟩) c.val,
        selectedJoint_legal game.toFOSG order p hn ht c⟩).toReal =
      (Serialization.currentLaw game.toFOSG order policies h (order.player ⟨n,hn⟩) c).toReal := by
  rw [InformationModel.behavioralJoint_prob_eq_prod,
    serial_movers game order h ht p hn,Finset.prod_singleton]
  let e := (choiceEquiv game.toFOSG order (order.player ⟨n,hn⟩)
    (game.information.infoOf (order.player ⟨n,hn⟩) h.trace)).trans
      (Serialization.choiceAtEquiv game.toFOSG h (order.player ⟨n,hn⟩))
  let target := e.symm c
  have hmap : Serialization.currentLaw game.toFOSG order policies h
      (order.player ⟨n,hn⟩) c =
      policies (order.player ⟨n,hn⟩)
        (scheduledView game.toFOSG (order.player ⟨n,hn⟩)
          (game.information.infoOf (order.player ⟨n,hn⟩) h.trace)) target := by
    unfold Serialization.currentLaw
    rw [← e.apply_symm_apply c,pmf_map_apply_of_injective _ e.injective]
  rw [hmap]
  apply congrArg ENNReal.toReal
  apply dependentLaw_apply
    ((game.serialized order).information.menu (order.player ⟨n,hn⟩))
    (policies (order.player ⟨n,hn⟩)) (serial_scheduled_info game order h p hn trace)
  simp only [InformationModel.choicesOfLegal,selectedJoint,ExecutionProtocol.singletonJoint,dite_true]
  rfl


set_option backward.isDefEq.respectTransparency false in
/-- Hidden selection has no extra transition randomness. The complete step
coefficient is exactly the scheduled marginal. -/
theorem serial_selection_step_probability (game : Game Role) (order : ExplicitOrder Role)
    (policies : (i : Role) → (game.serialized order).information.BehavioralPolicy i)
    (h : game.execution.History) (ht : ¬ game.execution.terminal h.state)
    {n : ℕ} (p : Prefix game.toFOSG order h n) (hn : n < order.slots)
    (trace : (game.serialized order).execution.Trace (.stage h n p))
    (c : ChoiceAt game.toFOSG h (order.player ⟨n,hn⟩)) :
    InformationModel.stepProb (game.serialized order).information policies trace
      ⟨selectedJoint game.toFOSG (order.player ⟨n,hn⟩) c.val,
        selectedJoint_legal game.toFOSG order p hn ht c⟩ (.stage h (n+1) (p.advance hn c)) =
      (Serialization.currentLaw game.toFOSG order policies h (order.player ⟨n,hn⟩) c).toReal := by
  rw [InformationModel.stepProb,serial_selection_probability game order policies h ht p hn trace c]
  have hstep : (game.serialized order).execution.step (.stage h n p)
      ⟨selectedJoint game.toFOSG (order.player ⟨n,hn⟩) c.val,
        selectedJoint_legal game.toFOSG order p hn ht c⟩ =
      PMF.pure (.stage h (n+1) (p.advance hn c)) := by
    simp [GameTheory.Languages.Bridges.FOSGToEFG.execution,hn,
      choiceOfJoint,selectedJoint,scheduledPlayer]
  rw [hstep]
  simp only [PMF.pure_apply_self,ENNReal.toReal_one,mul_one]

end KFOL.Rounds.Game
