module

public import KFOL.Definitions.DependentSchedule

/-! # Communication decreases a well-founded code, not a fixed binder count -/

@[expose] public section

namespace KFOL.DependentSchedule.Script

universe u v

variable {Role : Type u}

/-- Selecting any legal answer enters a strict child code. -/
inductive Child : Script.{u,v} Role → Script.{u,v} Role → Prop where
  | next (owner : Role) (Action : Type v) (continuation : Action → Script.{u,v} Role)
      (a : Action) : Child (continuation a) (.bind owner Action continuation)

/-- No sequence of communications can descend forever. -/
theorem child_wellFounded : WellFounded (Child (Role := Role)) := by
  refine ⟨fun G => ?_⟩
  induction G with
  | done Result =>
    refine Acc.intro _ ?_
    intro H h
    cases h
  | bind owner Action next ih =>
    refine Acc.intro _ ?_
    intro H h
    cases h with
    | next _ _ _ a => exact ih a

/-- Every dependent trace records finitely many decisions. -/
def traceLength : (G : Script.{u,v} Role) → Trace G → ℕ
  | .done _, _ => 0
  | .bind _ _ next, ⟨a, t⟩ => traceLength (next a) t + 1

/-- Owner order is retained as part of the actual chosen trace. -/
def traceOwners : (G : Script.{u,v} Role) → Trace G → List Role
  | .done _, _ => []
  | .bind owner _ next, ⟨a, t⟩ => owner :: traceOwners (next a) t

theorem traceOwners_length (G : Script.{u,v} Role) (t : Trace G) :
    (traceOwners G t).length = traceLength G t := by
  induction G with
  | done Result => rfl
  | bind owner Action next ih =>
    obtain ⟨a, t⟩ := t
    simp [traceOwners, traceLength, ih]

theorem traceLength_le_of_depthLE (G : Script.{u,v} Role) {n : ℕ} (h : DepthLE n G)
    (t : Trace G) : traceLength G t ≤ n := by
  induction G generalizing n with
  | done Result => exact Nat.zero_le _
  | bind owner Action next ih =>
    cases n with
    | zero => exact False.elim h
    | succ n =>
      obtain ⟨a, t⟩ := t
      exact Nat.succ_le_succ (ih a (h a) t)

end KFOL.DependentSchedule.Script
