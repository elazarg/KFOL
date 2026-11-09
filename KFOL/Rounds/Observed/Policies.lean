module

public import KFOL.Rounds.Reachability

/-! # Exact root and child decomposition of observed-round policies -/

@[expose] public section
noncomputable section

namespace KFOL.Rounds.Game.Observed

open GameTheory.Protocol

universe u

variable {Role : Type u}

/-- Actual root choices are exactly the finite menu indices. -/
def rootChoiceEquiv (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) (who : Role) :
    (Game.round sizes next).information.Choice who Position.root ≃ Fin (sizes who + 1) where
  toFun c := ⟨c.val.getD 0,by
    have h := c.property
    change LegalOption (Game.round sizes next).execution Position.root who c.val at h
    cases hc : c.val with
    | none => rw [hc] at h; exact False.elim (h (by intro hf; exact hf))
    | some n => rw [hc] at h; exact Nat.lt_succ_of_le h.2⟩
  invFun a := ⟨some a.val,by exact ⟨(by intro hf; exact hf),Nat.le_of_lt_succ a.isLt⟩⟩
  left_inv c := by
    apply Subtype.ext
    have h := c.property
    change LegalOption (Game.round sizes next).execution Position.root who c.val at h
    cases hc : c.val with
    | none => rw [hc] at h; exact False.elim (h (by intro hf; exact hf))
    | some n => simp [hc]
  right_inv a := Fin.ext rfl

/-- The parent occurrence and child use the same option values and the same
legal menu. The explicit equivalence bridges the two stuck LegalOption
matchers without introducing an action transport. -/
def childChoiceEquiv (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) (who : Role)
    (a : (i : Role) → Fin (sizes i + 1)) (p : Position (next a)) :
    (Game.round sizes next).information.Choice who (.down a p) ≃
      (next a).information.Choice who p where
  toFun c := ⟨c.val,by
    have h := c.property
    change LegalOption (Game.round sizes next).execution (.down a p) who c.val at h
    change LegalOption (next a).execution p who c.val
    cases hc : c.val <;> simpa only [hc,LegalOption,Position.current] using h⟩
  invFun c := ⟨c.val,by
    have h := c.property
    change LegalOption (next a).execution p who c.val at h
    change LegalOption (Game.round sizes next).execution (.down a p) who c.val
    cases hc : c.val <;> simpa only [hc,LegalOption,Position.current] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Restriction retains the actual parent occurrence of a child, not merely
its syntax. Equal continuation trees at different joint tuples remain separate. -/
def restrictChild (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (who : Role) (policy : (Game.round sizes next).information.BehavioralPolicy who)
    (a : (i : Role) → Fin (sizes i + 1)) : (next a).information.BehavioralPolicy who :=
  fun p => (policy (.down a p)).map (childChoiceEquiv sizes next who a p)

/-- The root component is a law on the actual finite action menu. -/
def rootLaw (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role)
    (who : Role) (policy : (Game.round sizes next).information.BehavioralPolicy who) :
    PMF (Fin (sizes who + 1)) :=
  (policy Position.root).map (rootChoiceEquiv sizes next who)

/-- Assemble one root law and an independently chosen policy in every child. -/
def assemblePolicy (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) (who : Role)
    (root : PMF (Fin (sizes who + 1)))
    (children : (a : (i : Role) → Fin (sizes i + 1)) → (next a).information.BehavioralPolicy who) :
    (Game.round sizes next).information.BehavioralPolicy who
  | .root => root.map (rootChoiceEquiv sizes next who).symm
  | .down a p => (children a p).map (childChoiceEquiv sizes next who a p).symm

/-- Root/child splitting is a genuine playerwise equivalence of the canonical
behavioral-policy carrier. -/
def policyEquiv (sizes : Role → ℕ)
    (next : ((i : Role) → Fin (sizes i + 1)) → Game Role) (who : Role) :
    (Game.round sizes next).information.BehavioralPolicy who ≃
      (PMF (Fin (sizes who + 1)) ×
        ((a : (i : Role) → Fin (sizes i + 1)) → (next a).information.BehavioralPolicy who)) where
  toFun policy := (rootLaw sizes next who policy,restrictChild sizes next who policy)
  invFun parts := assemblePolicy sizes next who parts.1 parts.2
  left_inv policy := by
    funext p
    cases p with
    | root =>
      change ((policy Position.root).map _).map _ = _
      rw [PMF.map_comp]
      simpa using PMF.map_id (policy Position.root)
    | down a p =>
      change ((policy (.down a p)).map _).map _ = _
      rw [PMF.map_comp]
      simpa using PMF.map_id (policy (.down a p))
  right_inv parts := by
    apply Prod.ext
    · change (parts.1.map _).map _ = _
      rw [PMF.map_comp]
      simpa using PMF.map_id parts.1
    · funext a p
      change ((parts.2 a p).map _).map _ = _
      rw [PMF.map_comp]
      simpa using PMF.map_id (parts.2 a p)

end KFOL.Rounds.Game.Observed
