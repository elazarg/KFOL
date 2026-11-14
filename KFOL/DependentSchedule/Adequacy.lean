module

public import KFOL.DependentSchedule.Execution

/-! # Full policies and endpoint plans have the same complete execution -/

@[expose] public section

namespace KFOL.DependentSchedule.Script

universe u v

variable {Role : Type u}

@[simp] theorem localOwner_send (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (a : Action) (p : Local owner (next a)) :
    localOwner owner Action next (send owner Action next a p) = ⟨a, p⟩ := by
  simp [localOwner, send]

@[simp] theorem localOther_receive (player owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (h : player ≠ owner)
    (p : (a : Action) → Local player (next a)) :
    localOther player owner Action next h (receive player owner Action next h p) = p := by
  simp [localOther, receive]

theorem reduce_owner (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (p : Full owner (.bind owner Action next)) :
    reduce owner (.bind owner Action next) p =
      send owner Action next (fullOwner owner Action next p).1
        (reduce owner (next (fullOwner owner Action next p).1)
          ((fullOwner owner Action next p).2 (fullOwner owner Action next p).1)) := by
  simp [reduce]

theorem reduce_other (player owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (h : player ≠ owner)
    (p : Full player (.bind owner Action next)) :
    reduce player (.bind owner Action next) p =
      receive player owner Action next h
        (fun a => reduce player (next a) (fullOther player owner Action next h p a)) := by
  simp [reduce, h]

theorem select_reduce (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (p : Strategies (.bind owner Action next)) :
    selectPlans owner Action next (reduceProfile (.bind owner Action next) p) =
      ⟨(selectFull owner Action next p).1,
        reduceProfile (next (selectFull owner Action next p).1)
          (selectFull owner Action next p).2⟩ := by
  classical
  have hc : localOwner owner Action next (reduce owner (.bind owner Action next) (p owner)) =
      ⟨(fullOwner owner Action next (p owner)).1,
        reduce owner (next (fullOwner owner Action next (p owner)).1)
          ((fullOwner owner Action next (p owner)).2 (fullOwner owner Action next (p owner)).1)⟩ :=
    (congrArg (localOwner owner Action next) (reduce_owner owner Action next (p owner))).trans
      (localOwner_send owner Action next _ _)
  unfold selectPlans selectFull
  simp only [reduceProfile]
  rw [hc]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext i
    by_cases hi : i = owner
    · subst i
      simp [reduceProfile]
    · simp [reduceProfile, hi, reduce_other]

theorem selectFull_assembleFull (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (a : Action)
    (children : (answer : Action) → Strategies (next answer)) :
    selectFull owner Action next (assembleFull owner Action next a children) =
      ⟨a, children a⟩ := by
  classical
  have hroot : fullOwner owner Action next
      (assembleFull owner Action next a children owner) = ⟨a, fun answer => children answer owner⟩ := by
    simp [fullOwner, assembleFull]
  unfold selectFull
  rw [hroot]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    funext player
    by_cases h : player = owner
    · subst player
      simp
    · simp [h, fullOther, assembleFull]

/-- Adequacy preserves the whole shared trace and all dependent returns,
not just a terminal winner or payoff. -/
theorem runFull_eq_run_reduce (G : Script.{u,v} Role) (p : Strategies G) :
    runFull G p = run G (reduceProfile G p) := by
  induction G with
  | done Result => rfl
  | bind owner Action next ih =>
    have hplans := congrArg
      (fun chosen : (a : Action) × Plans (next a) =>
        let e := run (next chosen.1) chosen.2
        (⟨⟨chosen.1, e.1⟩, e.2⟩ : Execution (.bind owner Action next)))
      (select_reduce owner Action next p)
    have hfull := congrArg (fun e : Execution (next (selectFull owner Action next p).1) =>
      (⟨⟨(selectFull owner Action next p).1, e.1⟩, e.2⟩ :
        Execution (.bind owner Action next)))
      (ih _ (selectFull owner Action next p).2)
    exact hfull.trans hplans.symm

end KFOL.DependentSchedule.Script
