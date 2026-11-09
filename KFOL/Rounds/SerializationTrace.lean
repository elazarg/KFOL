module

public import KFOL.Rounds.SerializationRecall

/-! # Actual traces for all legal serial commitment prefixes -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Serialization
open GameTheory.Protocol GameTheory.Languages
open Bridges.FOSGToEFG

universe uι us ua up uq uk
variable {Role : Type uι} [DecidableEq Role]
variable (G : FOSG.Game.{uι,us,ua,up,uq,uk} Role) (order : ExplicitOrder Role)

omit [DecidableEq Role] in
theorem prefix_zero (h : G.execution.History) (p : Prefix G order h 0) :
    p = Prefix.initial h := by
  apply Prefix.ext
  funext i
  apply Option.not_isSome_iff_eq_none.mp
  simp only [p.selected_iff,Nat.not_lt_zero,not_false_eq_true]

def lastChoice {h : G.execution.History} {n : ℕ} (p : Prefix G order h (n+1)) :
    ChoiceAt G h (order.player ⟨n,by have := p.count_le; omega⟩) :=
  (p.choices _).get (by
    rw [p.selected_iff,Equiv.symm_apply_apply]
    exact Nat.lt_succ_self _)

theorem advance_retreat {h : G.execution.History} {n : ℕ}
    (p : Prefix G order h (n+1)) (hc : n < order.slots) :
    p.retreat.advance hc (lastChoice G order p) = p := by
  apply Prefix.ext
  funext i
  by_cases hi : i = order.player ⟨n,hc⟩
  · subst i
    simp only [Prefix.advance,dite_true,lastChoice]
    exact Option.some_get _
  · have hn : (order.player.symm i).val ≠ n := by
      intro he
      apply hi
      apply order.player.symm.injective
      simpa only [Equiv.symm_apply_apply] using Fin.ext he
    by_cases hlt : (order.player.symm i).val < n
    · simp only [Prefix.advance,hi,dite_false,Prefix.retreat,ite_eq_left hlt]
    · have hnone : p.choices i = none := by
        apply Option.not_isSome_iff_eq_none.mp
        rw [p.selected_iff]
        omega
      simp only [Prefix.advance,hi,dite_false,Prefix.retreat,ite_eq_right hlt,hnone]

/-- From any realized public boundary, every legal partial commitment can be
realized. No particular behavioral strategy or positive reach is assumed. -/
def prefixTrace {h : G.execution.History}
    (boundary : (execution G order).Trace (.stage h 0 (Prefix.initial h)))
    (ht : ¬ G.execution.terminal h.state) :
    (n : ℕ) → (p : Prefix G order h n) →
      (execution G order).Trace (.stage h n p)
  | 0,p => by
    have he := prefix_zero G order h p
    subst p
    exact boundary
  | n+1,p => by
    have hc : n < order.slots := by have := p.count_le; omega
    let prior := prefixTrace boundary ht n p.retreat
    let joint := selectedJoint G (order.player ⟨n,hc⟩) (lastChoice G order p).val
    have legal : (execution G order).Legal (.stage h n p.retreat) joint :=
      selectedJoint_legal G order p.retreat hc ht (lastChoice G order p)
    apply ExecutionProtocol.Trace.extend prior joint legal
    rw [step_select G order p.retreat hc joint legal,PMF.mem_support_pure_iff]
    congr 1
    have hchoice : choiceOfJoint G order p.retreat hc joint legal.2 = lastChoice G order p := by
      apply Subtype.ext
      simp [joint,choiceOfJoint,selectedJoint,scheduledPlayer]
    rw [hchoice]
    exact (advance_retreat G order p hc).symm

/-- Every literal source history has a corresponding realized serial public
boundary. This includes source histories assigned zero probability by a profile. -/
def boundaryTrace : ∀ {state : G.execution.State} (trace : G.execution.Trace state),
    (execution G order).Trace (.stage ⟨state,trace⟩ 0 (Prefix.initial ⟨state,trace⟩))
  | _,.start => .start
  | target,.extend (source := source) prior joint legal realized => by
    let h : G.execution.History := ⟨source,prior⟩
    let p : Prefix G order h order.slots := Prefix.ofJoint (G := G) (order := order) (history := h) joint legal
    let atSlots := prefixTrace G order (boundaryTrace prior) legal.1 order.slots p
    let noop : (i : Role) → Option (G.execution.Action i) := fun _ => none
    have noLegal : (execution G order).Legal (.stage h order.slots p) noop := by
      refine ⟨legal.1,fun i ha => ?_⟩
      exact (Nat.lt_irrefl _) ha.1
    apply ExecutionProtocol.Trace.extend atSlots noop noLegal
    rw [step_resolve G order p noop noLegal]
    apply (mem_support_resolve_iff G order p noLegal.1 _).mpr
    refine ⟨target,?_,?_⟩
    · change target ∈ (G.execution.step source ⟨joint,legal⟩).support
      exact realized
    · rfl

end KFOL.Rounds.Serialization
