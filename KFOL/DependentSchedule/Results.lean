module

public import KFOL.DependentSchedule.Public

/-! # Aggregate contracts for the report's dynamic schedule claims -/

@[expose] public section

namespace KFOL.DependentSchedule.Results

universe u v w z y

/-- Full-policy reduction preserves the complete shared dependent execution. -/
theorem public_execution {Role : Type u} (G : Script.{u,v} Role) (p : G.Strategies) :
    G.runFull p = G.run (G.reduceProfile p) :=
  Script.runFull_eq_run_reduce G p

/-- Well-founded schedules can have arbitrarily long finite executions,
with genuine value-dependent owner order and answer types. -/
theorem wellFounded_with_unbounded {Role : Type u} (alice bob carol : Role) :
    WellFounded (Script.Child.{u,v} (Role := Role)) ∧
    (∀ n, ¬Script.DepthLE n (Script.unbounded alice bob carol)) ∧
    ∀ n, Script.traceLength (Script.unbounded alice bob carol)
      ((Script.unbounded alice bob carol).runFull
        (Script.unboundedStrategies alice bob carol n)).1 = n + 1 :=
  ⟨Script.child_wellFounded, Script.unbounded_not_depthLE alice bob carol,
    Script.runFull_unbounded_length alice bob carol⟩

/-- A private boundary in a view-indexed arena preserves full legal policy
tables, execution, and whole-player deviations. No audience/sealing theorem
for an arbitrary syntactic disclosure calculus is asserted here. -/
theorem private_connection {View : Type u} {Answer : View → Type v}
    {Result : Type w} {NextResult : Type z} {Role : Type y}
    (G : ViewArena View Answer Result)
    (next : Result → ViewArena View Answer NextResult) :
    Nonempty ((ViewArena.graft G next).Policies ≃
      Views.GluingData Answer G.legalViews (ViewArena.suffixViews G next)) ∧
    (∀ policy : (ViewArena.graft G next).Policies,
      (ViewArena.graft G next).run policy =
        (next (G.run (ViewArena.firstPolicy G next policy))).run
          (ViewArena.secondPolicy G next policy
            (G.run (ViewArena.firstPolicy G next policy))
            (ViewArena.run_exits G (ViewArena.firstPolicy G next policy)))) ∧
    ∀ (owner : View → Role) (player : Role)
      (source target : (ViewArena.graft G next).Policies),
      Views.Deviation owner player source target ↔
        Views.Deviation owner player (ViewArena.firstPolicy G next source)
          (ViewArena.firstPolicy G next target) ∧
        Views.Deviation owner player (ViewArena.remainingPolicy G next source)
          (ViewArena.remainingPolicy G next target) :=
  ⟨⟨ViewArena.graftPolicyEquiv G next⟩, ViewArena.run_graft G next,
    fun owner player => ViewArena.deviation_graft_iff owner player G next⟩

end KFOL.DependentSchedule.Results
