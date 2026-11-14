module

public import KFOL.DependentSchedule.PolicyGluing

/-! # Execution and private-boundary grafting over legal decision views

This is a semantic interface for full policy tables. It does not assert
that an arbitrary choice of view labels satisfies an audience or sealing
discipline; that obligation belongs to the implementation of the interface.
-/

@[expose] public section

namespace KFOL.DependentSchedule.ViewArena

universe u v w z y

variable {View : Type u} {Answer : View → Type v} {Result : Type w}

/-- Reuse the complete legal policy table at the selected continuation. -/
def childPolicy (request : View) (next : Answer request → ViewArena View Answer Result)
    (policy : Policies (.ask request next)) (a : Answer request) : Policies (next a) :=
  fun view => policy ⟨view.val, Or.inr ⟨a, view.property⟩⟩

/-- Execute a well-founded arena using only its requested legal views. -/
noncomputable def run : (G : ViewArena View Answer Result) → Policies G → Result
  | .done result, _ => result
  | .ask request next, policy =>
      let a := policy ⟨request, Or.inl rfl⟩
      run (next a) (childPolicy request next policy a)

theorem run_exits (G : ViewArena View Answer Result) (policy : Policies G) :
    Exits (run G policy) G := by
  induction G with
  | done result => rfl
  | ask request next ih =>
    exact ⟨policy ⟨request, Or.inl rfl⟩,
      ih _ (childPolicy request next policy _)⟩

/-- Connect a continuation at every legal exit without publishing a new
boundary record or forgetting the inherited decision views. -/
def graft {NextResult : Type z} : ViewArena View Answer Result →
    (Result → ViewArena View Answer NextResult) → ViewArena View Answer NextResult
  | .done result, next => next result
  | .ask request children, next => .ask request (fun a => graft (children a) next)

/-- Suffix policy domains contain views from every legal boundary result,
independently of the result reached by a chosen prefix policy. -/
def suffixViews {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) : Set View :=
  {view | ∃ result, Exits result G ∧ Occurs view (next result)}

theorem occurs_graft {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) (view : View) :
    Occurs view (graft G next) ↔ Occurs view G ∨ view ∈ suffixViews G next := by
  induction G with
  | done result =>
    simp only [graft, Occurs, suffixViews, Set.mem_ofPred_eq, Exits, false_or]
    constructor
    · intro h
      exact ⟨result, rfl, h⟩
    · rintro ⟨other, rfl, h⟩
      exact h
  | ask request children ih =>
    constructor
    · rintro (h | ⟨a, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases (ih a).mp h with h | ⟨result, he, hv⟩
        · exact Or.inl (Or.inr ⟨a, h⟩)
        · exact Or.inr ⟨result, ⟨a, he⟩, hv⟩
    · rintro ((h | ⟨a, h⟩) | ⟨result, ⟨a, he⟩, hv⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, (ih a).mpr (Or.inl h)⟩
      · exact Or.inr ⟨a, (ih a).mpr (Or.inr ⟨result, he, hv⟩)⟩

theorem legalViews_graft {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) :
    (graft G next).legalViews = G.legalViews ∪ suffixViews G next := by
  ext view
  exact occurs_graft G next view

def firstPolicy {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) (policy : Policies (graft G next)) :
    Policies G :=
  fun view => policy ⟨view.val, (occurs_graft G next view.val).mpr (Or.inl view.property)⟩

def remainingPolicy {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) (policy : Policies (graft G next)) :
    Views.Policy Answer (suffixViews G next) :=
  fun view => policy ⟨view.val, (occurs_graft G next view.val).mpr (Or.inr view.property)⟩

def secondPolicy {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) (policy : Policies (graft G next))
    (result : Result) (hr : Exits result G) : Policies (next result) :=
  fun view => policy ⟨view.val,
    (occurs_graft G next view.val).mpr (Or.inr ⟨result, hr, view.property⟩)⟩

/-- Complete policy tables at a private boundary form a fiber product over
shared decision views, rather than two independent choices on that overlap. -/
noncomputable def graftPolicyEquiv {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) :
    Policies (graft G next) ≃ Views.GluingData Answer G.legalViews (suffixViews G next) :=
  (Equiv.cast (congrArg (Views.Policy Answer) (legalViews_graft G next))).trans
    (Views.unionEquivGluing Answer G.legalViews (suffixViews G next))

/-- Execution first uses the prefix policy and then the same full suffix
policy at the boundary actually reached. The suffix policy remains defined
on every other legal boundary, including off-path ones. -/
theorem run_graft {NextResult : Type z} (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) (policy : Policies (graft G next)) :
    run (graft G next) policy =
      run (next (run G (firstPolicy G next policy)))
        (secondPolicy G next policy (run G (firstPolicy G next policy))
          (run_exits G (firstPolicy G next policy))) := by
  induction G with
  | done result => rfl
  | ask request children ih =>
    let a := policy ⟨request, Or.inl rfl⟩
    exact ih a (childPolicy request (fun a => graft (children a) next) policy a)

/-- Whole-player deviations retain all off-path decisions and become the
corresponding compatible pair of component deviations. -/
theorem deviation_graft_iff {NextResult : Type z} {Role : Type y}
    (owner : View → Role) (player : Role) (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult)
    (source target : Policies (graft G next)) :
    Views.Deviation owner player source target ↔
      Views.Deviation owner player (firstPolicy G next source) (firstPolicy G next target) ∧
      Views.Deviation owner player (remainingPolicy G next source) (remainingPolicy G next target) := by
  constructor
  · intro h
    constructor
    · intro view hv
      exact h ⟨view.val, (occurs_graft G next view.val).mpr (Or.inl view.property)⟩ hv
    · intro view hv
      exact h ⟨view.val, (occurs_graft G next view.val).mpr (Or.inr view.property)⟩ hv
  · rintro ⟨hfirst, hrest⟩ view hv
    rcases (occurs_graft G next view.val).mp view.property with h | h
    · exact hfirst ⟨view.val, h⟩ hv
    · exact hrest ⟨view.val, h⟩ hv

/-- Rebracketing is the same arena, with the same requests and legal views. -/
theorem graft_assoc {Middle : Type z} {Last : Type y}
    (G : ViewArena View Answer Result) (next : Result → ViewArena View Answer Middle)
    (last : Middle → ViewArena View Answer Last) :
    graft (graft G next) last = graft G (fun result => graft (next result) last) := by
  induction G with
  | done result => rfl
  | ask request children ih =>
    exact congrArg (fun children => ViewArena.ask request children) (funext ih)

theorem graft_done (G : ViewArena View Answer Result) :
    graft G (fun result => .done result) = G := by
  induction G with
  | done result => rfl
  | ask request children ih =>
    exact congrArg (fun children => ViewArena.ask request children) (funext ih)

end KFOL.DependentSchedule.ViewArena
