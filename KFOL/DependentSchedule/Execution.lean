module

public import KFOL.Definitions.DependentSchedule

/-! # Shared-trace execution and reduction of full policies -/

@[expose] public section

namespace KFOL.DependentSchedule.Script

universe u v

variable {Role : Type u}

open Classical

theorem local_owner_type (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) :
    Local owner (.bind owner Action next) = ((a : Action) × Local owner (next a)) := by
  simp [Local]

theorem local_other_type (player owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (h : player ≠ owner) :
    Local player (.bind owner Action next) = ((a : Action) → Local player (next a)) := by
  simp [Local, h]

theorem full_owner_type (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) :
    Full owner (.bind owner Action next) =
      (Action × ((a : Action) → Full owner (next a))) := by
  simp [Full]

theorem full_other_type (player owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (h : player ≠ owner) :
    Full player (.bind owner Action next) = ((a : Action) → Full player (next a)) := by
  simp [Full, h]

noncomputable def localOwner (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) :
    Local owner (.bind owner Action next) → ((a : Action) × Local owner (next a)) :=
  cast (local_owner_type owner Action next)

noncomputable def localOther (player owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (h : player ≠ owner) :
    Local player (.bind owner Action next) → ((a : Action) → Local player (next a)) :=
  cast (local_other_type player owner Action next h)

noncomputable def send (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (a : Action) (p : Local owner (next a)) :
    Local owner (.bind owner Action next) :=
  cast (local_owner_type owner Action next).symm ⟨a, p⟩

noncomputable def receive (player owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (h : player ≠ owner)
    (p : (a : Action) → Local player (next a)) : Local player (.bind owner Action next) :=
  cast (local_other_type player owner Action next h).symm p

noncomputable def fullOwner (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) :
    Full owner (.bind owner Action next) → (Action × ((a : Action) → Full owner (next a))) :=
  cast (full_owner_type owner Action next)

noncomputable def fullOther (player owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (h : player ≠ owner) :
    Full player (.bind owner Action next) → ((a : Action) → Full player (next a)) :=
  cast (full_other_type player owner Action next h)

/-- Assemble one root action with complete policy profiles for every
continuation, including alternatives to the selected action. -/
noncomputable def assembleFull (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (a : Action)
    (children : (answer : Action) → Strategies (next answer)) :
    Strategies (.bind owner Action next) := by
  intro player
  by_cases h : player = owner
  · subst player
    exact cast (full_owner_type owner Action next).symm
      ⟨a, fun answer => children answer owner⟩
  · exact cast (full_other_type player owner Action next h).symm
      (fun answer => children answer player)

/-- Discard only alternatives after the player's own selected action. -/
noncomputable def reduce (player : Role) :
    (G : Script.{u,v} Role) → Full player G → Local player G
  | .done _, p => p
  | .bind owner Action next, p => by
      classical
      by_cases h : player = owner
      · subst player
        let q := fullOwner owner Action next p
        exact send owner Action next q.1 (reduce owner (next q.1) (q.2 q.1))
      · exact receive player owner Action next h
          (fun a => reduce player (next a) (fullOther player owner Action next h p a))

noncomputable def reduceProfile (G : Script.{u,v} Role) (p : Strategies G) : Plans G :=
  fun i => reduce i G (p i)

/-- All endpoints continue with the single witness supplied by the owner. -/
noncomputable def selectPlans (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (p : Plans (.bind owner Action next)) :
    (a : Action) × Plans (next a) := by
  let q := localOwner owner Action next (p owner)
  refine ⟨q.1, fun i => ?_⟩
  by_cases h : i = owner
  · subst i
    exact q.2
  · exact localOther i owner Action next h (p i) q.1

/-- A full policy retains all alternatives, but execution chooses the owner's
one action and applies every role's continuation at that same action. -/
noncomputable def selectFull (owner : Role) (Action : Type v)
    (next : Action → Script.{u,v} Role) (p : Strategies (.bind owner Action next)) :
    (a : Action) × Strategies (next a) := by
  let q := fullOwner owner Action next (p owner)
  refine ⟨q.1, fun i => ?_⟩
  by_cases h : i = owner
  · subst i
    exact q.2 q.1
  · exact fullOther i owner Action next h (p i) q.1

/-- Execution from endpoint plans, independently of full-policy execution. -/
noncomputable def run : (G : Script.{u,v} Role) → Plans G → Execution G
  | .done _, p => ⟨PUnit.unit, p⟩
  | .bind owner Action next, p =>
      let chosen := selectPlans owner Action next p
      let result := run (next chosen.1) chosen.2
      ⟨⟨chosen.1, result.1⟩, result.2⟩

/-- Execution directly reads full policies; it does not call `reduce`. -/
noncomputable def runFull : (G : Script.{u,v} Role) → Strategies G → Execution G
  | .done _, p => ⟨PUnit.unit, p⟩
  | .bind owner Action next, p =>
      let chosen := selectFull owner Action next p
      let result := runFull (next chosen.1) chosen.2
      ⟨⟨chosen.1, result.1⟩, result.2⟩

end KFOL.DependentSchedule.Script
