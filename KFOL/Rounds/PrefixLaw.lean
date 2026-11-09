module

public import KFOL.Rounds.SerializationTrace
public import GameTheory.Math.Probability.Joint
public import GameTheory.Math.Probability.Convergence

/-! # Independent local laws on the actual hidden commitment prefixes -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Serialization
open GameTheory.Protocol GameTheory.Languages GameTheory.Math.Probability
open Bridges.FOSGToEFG

universe uι us ua up uq uk
variable {Role : Type uι} [DecidableEq Role]
variable (G : FOSG.Game.{uι,us,ua,up,uq,uk} Role) (order : ExplicitOrder Role)

/-- Source menu adequacy identifies policy choices with actual legal choices
at the public history. -/
def choiceAtEquiv (h : G.execution.History) (i : Role) :
    G.information.Choice i (G.information.infoOf i h.trace) ≃ ChoiceAt G h i where
  toFun c := ⟨c.val,(G.information.menu_adequate i h.trace c.val).mp c.property⟩
  invFun c := ⟨c.val,(G.information.menu_adequate i h.trace c.val).mpr c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Read the given target profile at this player's scheduled public view.
Current hidden choices never enter this local law. -/
def currentLaw (policies : (i : Role) → (information G order).BehavioralPolicy i)
    (h : G.execution.History) (i : Role) : PMF (ChoiceAt G h i) :=
  (policies i (scheduledView G i (G.information.infoOf i h.trace))).map
    ((choiceEquiv G order i (G.information.infoOf i h.trace)).trans (choiceAtEquiv G h i))

theorem lastChoice_advance {h : G.execution.History} {n : ℕ}
    (p : Prefix G order h n) (hc : n < order.slots)
    (c : ChoiceAt G h (order.player ⟨n,hc⟩)) :
    lastChoice G order (p.advance hc c) = c := by
  apply Subtype.ext
  simp only [lastChoice,Prefix.advance,dite_true,Option.get_some]

/-- Appending one selected choice is a bijection, with the literal retreat and
last-choice projections as its inverse. -/
def prefixPairEquiv {h : G.execution.History} {n : ℕ} (hc : n < order.slots) :
    (Prefix G order h n × ChoiceAt G h (order.player ⟨n,hc⟩)) ≃ Prefix G order h (n+1) where
  toFun p := p.1.advance hc p.2
  invFun p := ⟨p.retreat,lastChoice G order p⟩
  left_inv p := by
    exact Prod.ext (Prefix.retreat_advance p.1 hc p.2) (lastChoice_advance G order p.1 hc p.2)
  right_inv p := advance_retreat G order p hc

/-- The ordered product of independent scheduled laws, on actual prefix data.
This is a probability-law construction, not an equilibrium predicate. -/
def prefixLaw (policies : (i : Role) → (information G order).BehavioralPolicy i)
    (h : G.execution.History) : (n : ℕ) → n ≤ order.slots → PMF (Prefix G order h n)
  | 0,_ => PMF.pure (Prefix.initial h)
  | n+1,hc =>
    let step : n < order.slots := Nat.lt_of_succ_le hc
    (bindPairLaw (prefixLaw policies h n (Nat.le_of_lt step))
      (fun _ => currentLaw G order policies h (order.player ⟨n,step⟩))).map
        (prefixPairEquiv G order step)

/-- Every mass is the previous-prefix mass times the next scheduled marginal. -/
theorem prefixLaw_succ_apply (policies : (i : Role) → (information G order).BehavioralPolicy i)
    (h : G.execution.History) (n : ℕ) (hc : n+1 ≤ order.slots)
    (p : Prefix G order h (n+1)) :
    prefixLaw G order policies h (n+1) hc p =
      prefixLaw G order policies h n (Nat.le_trans (Nat.le_succ _) hc) p.retreat *
        currentLaw G order policies h (order.player ⟨n,Nat.lt_of_succ_le hc⟩)
          (lastChoice G order p) := by
  let e := prefixPairEquiv (G := G) (order := order) (h := h) (Nat.lt_of_succ_le hc)
  change (PMF.map e _) p = _
  rw [← e.apply_symm_apply p,pmf_map_apply_of_injective _ e.injective]
  rw [e.apply_symm_apply]
  exact bindPairLaw_apply _ _ _ _


/-- Pointwise limits commute with the finite ordered product of current
commitment laws; the public reach weight does not enter this construction. -/
theorem prefixLaw_converges
    (sequence : ℕ → (i : Role) → (information G order).BehavioralPolicy i)
    (target : (i : Role) → (information G order).BehavioralPolicy i)
    (h : G.execution.History)
    (hc : ∀ i, PMFConvergesPointwise
      (fun k => currentLaw G order (sequence k) h i) (currentLaw G order target h i)) :
    ∀ (n : ℕ) (hn : n ≤ order.slots), PMFConvergesPointwise
      (fun k => prefixLaw G order (sequence k) h n hn) (prefixLaw G order target h n hn) := by
  intro n
  induction n with
  | zero => intro hn; exact pmfConvergesPointwise_const _
  | succ n ih =>
    intro hn
    have step : n < order.slots := Nat.lt_of_succ_le hn
    have previous := ih (Nat.le_of_lt step)
    have joint := previous.bind (fun p =>
      (hc (order.player ⟨n,step⟩)).map (fun c => (p,c)))
    exact joint.map (prefixPairEquiv G order step)

end KFOL.Rounds.Serialization
