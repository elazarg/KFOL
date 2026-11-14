module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Basic

/-! # Well-founded dependent schedules and their local interfaces

A continuation is a genuine family of script codes. Its owners, answer
types, length, and terminal return types may depend on the preceding answer.
Full strategies retain off-path continuations; endpoint plans retain only
the continuation of an owner's selected answer.
-/

@[expose] public section

namespace KFOL.DependentSchedule

universe u v w

/-- A public schedule with dependent continuations and typed terminal returns.
The inductive carrier ensures well-foundedness, without a uniform depth bound. -/
inductive Script (Role : Type u) : Type (max u (v + 1)) where
  | done (Result : Role → Type v)
  | bind (owner : Role) (Action : Type v) (next : Action → Script Role)

namespace Script

variable {Role : Type u}

open Classical

/-- The executable endpoint interface at one role. -/
noncomputable def Local (player : Role) : Script.{u,v} Role → Type v
  | .done Result => Result player
  | .bind owner Action next =>
      if player = owner then (a : Action) × Local player (next a)
      else (a : Action) → Local player (next a)

/-- A complete policy retains alternatives after its own earlier decisions. -/
noncomputable def Full (player : Role) : Script.{u,v} Role → Type v
  | .done Result => Result player
  | .bind owner Action next =>
      if player = owner then Action × ((a : Action) → Full player (next a))
      else (a : Action) → Full player (next a)

/-- One shared dependent trace, rather than one trace per endpoint. -/
def Trace : Script.{u,v} Role → Type v
  | .done _ => PUnit
  | .bind _ Action next => (a : Action) × Trace (next a)

/-- The terminal answer type reached along the shared trace. -/
def Return (player : Role) : (G : Script.{u,v} Role) → Trace G → Type v
  | .done Result, _ => Result player
  | .bind _ _ next, ⟨a, t⟩ => Return player (next a) t

/-- A trace and all endpoint returns at that same trace. -/
def Execution (G : Script.{u,v} Role) : Type (max u v) :=
  (t : Trace G) × ((i : Role) → Return i G t)

/-- Executable endpoint plans at every role. -/
noncomputable abbrev Plans (G : Script.{u,v} Role) := (i : Role) → Local i G

/-- Full policies at every role, including all legal off-path alternatives. -/
noncomputable abbrev Strategies (G : Script.{u,v} Role) := (i : Role) → Full i G

/-- A uniform finite depth is an additional property, not a formation premise. -/
def DepthLE : ℕ → Script.{u,v} Role → Prop
  | _, .done _ => True
  | 0, .bind _ _ _ => False
  | n + 1, .bind _ _ next => ∀ a, DepthLE n (next a)

end Script

namespace Views

variable {View : Type u}

/-- A complete decision function on every legal view in a domain. The answer
family is indexed by the view, not by an unobservable history or code address. -/
abbrev Policy (Answer : View → Type v) (domain : Set View) :=
  (view : domain) → Answer view.val

/-- Prefix and suffix policies must agree if their decision views overlap. -/
def Agree {Answer : View → Type v} {P Q : Set View}
    (first : Policy Answer P) (second : Policy Answer Q) : Prop :=
  ∀ view (hp : view ∈ P) (hq : view ∈ Q), first ⟨view, hp⟩ = second ⟨view, hq⟩

/-- A fiber product of full policy spaces over their shared information sets. -/
def GluingData (Answer : View → Type v) (P Q : Set View) :=
  {pair : Policy Answer P × Policy Answer Q // Agree pair.1 pair.2}

/-- All decisions belonging to other players are fixed; the selected player
may change its complete policy, including off-path decisions. -/
def Deviation {Role : Type*} (owner : View → Role) (player : Role)
    {Answer : View → Type v} {domain : Set View}
    (source target : Policy Answer domain) : Prop :=
  ∀ view : domain, owner view.val ≠ player → source view = target view

end Views

/-- A well-founded semantic arena whose answer family is pulled back from
the legal decision view. The same view may occur at different private histories.
The result can be a tagged dependent record of boundary context and store. -/
inductive ViewArena (View : Type u) (Answer : View → Type v) (Result : Type w) where
  | done (result : Result)
  | ask (view : View) (next : Answer view → ViewArena View Answer Result)

namespace ViewArena

variable {View : Type u} {Answer : View → Type v} {Result : Type w}

/-- All legal decision views, independently of any selected policy. -/
def Occurs (view : View) : ViewArena View Answer Result → Prop
  | .done _ => False
  | .ask request next => view = request ∨ ∃ a, Occurs view (next a)

/-- All legal exits, including those inconsistent with a chosen player's
earlier decisions. -/
def Exits (result : Result) : ViewArena View Answer Result → Prop
  | .done value => result = value
  | .ask _ next => ∃ a, Exits result (next a)

def legalViews (G : ViewArena View Answer Result) : Set View :=
  {view | Occurs view G}

abbrev Policies (G : ViewArena View Answer Result) := Views.Policy Answer G.legalViews

end ViewArena

end KFOL.DependentSchedule
