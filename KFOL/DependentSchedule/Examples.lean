module

public import KFOL.DependentSchedule.WellFounded
public import KFOL.DependentSchedule.Adequacy

/-! # Value-dependent schedules of unbounded finite length -/

@[expose] public section

namespace KFOL.DependentSchedule.Script

universe u

variable {Role : Type u}

/-- A finite sequence whose owners alternate and whose action types depend
on the remaining length chosen earlier. -/
def alternating (first second : Role) : ℕ → Script.{u,0} Role
  | 0 => .done (fun _ => PUnit)
  | n + 1 => .bind first (Fin (n + 1)) (fun _ => alternating second first n)

def alternatingTrace (first second : Role) :
    (n : ℕ) → Trace (alternating first second n)
  | 0 => PUnit.unit
  | n + 1 => ⟨⟨0, Nat.zero_lt_succ _⟩, alternatingTrace second first n⟩

noncomputable def alternatingStrategies (first second : Role) :
    (n : ℕ) → Strategies (alternating first second n)
  | 0 => fun _ => PUnit.unit
  | n + 1 => assembleFull first (Fin (n + 1)) (fun _ => alternating second first n)
      ⟨0, Nat.zero_lt_succ _⟩ (fun _ => alternatingStrategies second first n)

theorem runFull_alternating_trace (first second : Role) (n : ℕ) :
    (runFull (alternating first second n) (alternatingStrategies first second n)).1 =
      alternatingTrace first second n := by
  induction n generalizing first second with
  | zero => rfl
  | succ n ih =>
    simp only [alternating, alternatingStrategies, runFull, selectFull_assembleFull]
    exact congrArg (fun t => (⟨⟨0, Nat.zero_lt_succ _⟩, t⟩ :
      Trace (.bind first (Fin (n + 1)) (fun _ => alternating second first n))))
      (ih second first)

theorem alternatingTrace_length (first second : Role) (n : ℕ) :
    traceLength (alternating first second n) (alternatingTrace first second n) = n := by
  induction n generalizing first second with
  | zero => rfl
  | succ n ih => simpa [alternating, alternatingTrace, traceLength] using ih second first

/-- The chosen value changes the owner at the same subsequent position:
even lengths start with Bob and odd lengths with Carol. -/
def remaining (bob carol : Role) (n : ℕ) : Script.{u,0} Role :=
  alternating (if n % 2 = 0 then bob else carol)
    (if n % 2 = 0 then carol else bob) n

def remainingTrace (bob carol : Role) (n : ℕ) : Trace (remaining bob carol n) :=
  alternatingTrace (if n % 2 = 0 then bob else carol)
    (if n % 2 = 0 then carol else bob) n

noncomputable def remainingStrategies (bob carol : Role) (n : ℕ) :
    Strategies (remaining bob carol n) :=
  alternatingStrategies (if n % 2 = 0 then bob else carol)
    (if n % 2 = 0 then carol else bob) n

theorem runFull_remaining_trace (bob carol : Role) (n : ℕ) :
    (runFull (remaining bob carol n) (remainingStrategies bob carol n)).1 =
      remainingTrace bob carol n := by
  exact runFull_alternating_trace _ _ _

theorem remainingTrace_length (bob carol : Role) (n : ℕ) :
    traceLength (remaining bob carol n) (remainingTrace bob carol n) = n := by
  exact alternatingTrace_length _ _ _

/-- Alice's chosen natural number determines the remaining length, owner
order, and dependent finite answer types. -/
def unbounded (alice bob carol : Role) : Script.{u,0} Role :=
  .bind alice ℕ (remaining bob carol)

def unboundedTrace (alice bob carol : Role) (n : ℕ) : Trace (unbounded alice bob carol) :=
  ⟨n, remainingTrace bob carol n⟩

noncomputable def unboundedStrategies (alice bob carol : Role) (n : ℕ) :
    Strategies (unbounded alice bob carol) :=
  assembleFull alice ℕ (remaining bob carol) n (remainingStrategies bob carol)

theorem runFull_unbounded_trace (alice bob carol : Role) (n : ℕ) :
    (runFull (unbounded alice bob carol) (unboundedStrategies alice bob carol n)).1 =
      unboundedTrace alice bob carol n := by
  simp only [unbounded, unboundedStrategies, runFull, unboundedTrace]
  rw [selectFull_assembleFull alice ℕ (remaining bob carol) n (remainingStrategies bob carol)]
  exact congrArg (fun t => (⟨n, t⟩ : Trace (unbounded alice bob carol)))
    (runFull_remaining_trace bob carol n)

theorem unboundedTrace_length (alice bob carol : Role) (n : ℕ) :
    traceLength (unbounded alice bob carol) (unboundedTrace alice bob carol n) = n + 1 := by
  simp [unbounded, unboundedTrace, traceLength, remainingTrace_length]

theorem runFull_unbounded_length (alice bob carol : Role) (n : ℕ) :
    traceLength (unbounded alice bob carol)
      (runFull (unbounded alice bob carol) (unboundedStrategies alice bob carol n)).1 = n + 1 := by
  rw [runFull_unbounded_trace, unboundedTrace_length]

/-- The code is well founded but admits no uniform finite decision bound. -/
theorem unbounded_not_depthLE (alice bob carol : Role) (n : ℕ) :
    ¬DepthLE n (unbounded alice bob carol) := by
  intro h
  have hh := traceLength_le_of_depthLE (unbounded alice bob carol) h
    (unboundedTrace alice bob carol n)
  rw [unboundedTrace_length] at hh
  exact Nat.not_succ_le_self n hh

end KFOL.DependentSchedule.Script
