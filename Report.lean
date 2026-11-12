module

public import KFOL.Results.Certificates
public import KFOL.Results.Algebra
public import KFOL.Results.Games
public import KFOL.Definitions.PaperGames
public import KFOL.Query.Compilation
public import KFOL.Query.Relations
public import KFOL.Query.ZeroExtension
public import KFOL.Core.TernaryInterpolation
public import KFOL.Core.MinorantPatches
public import KFOL.Core.MinorantFivePatches
public import KFOL.Core.FivePointInterpolation
public import KFOL.Core.SourceCertificates
public import KFOL.Core.LocalNormalForm
public import KFOL.Core.ProfileEnvelope
public import KFOL.Core.ProfileRelations
public import KFOL.Core.ProfileBounds
public import KFOL.Core.WholeInputs
public import KFOL.Core.ProfileQueries
public import KFOL.Core.ProfileCompletion
public import KFOL.Core.ProfilePointObstruction
public import KFOL.Core.Staircase
public import KFOL.Core.RainbowPersistence
public import KFOL.Core.ProfilePersistence
public import KFOL.Core.CyclicPersistence
public import KFOL.Core.CrownFullSyntax
public import KFOL.Core.AtomicObserver
public import KFOL.Core.Hypergraphs
public import KFOL.Core.ExponentialCrown
public import KFOL.Core.BichainFiber
public import KFOL.Core.AtomicAmalgamation
public import KFOL.Audit.Namespace

/-! # Audited report statements and mathematical proof ingredients

Implementation contracts (word codecs, machine states and intermediate
certificates) reside in the library. Every proof below names a library theorem.
-/

@[expose] public section
noncomputable section
namespace KFOL.Report
open FirstOrder WinnerSet Classical
universe u v w

/-- `game:prop:winner-count`: overlap and absorption exhaust the losses. -/
theorem winner_accounting {Role : Type u} {Var : Type v} [Finite Role]
    (t : Term Role Var) (ν : Var → WinnerSet Role) :
    (t.eval ν).val.ncard + t.overlapLoss ν + t.absorptionLoss ν = t.leafMass ν :=
  Results.Algebra.winner_accounting t ν

theorem winner_leaf_mass {Role : Type u} {Var : Type v} [Finite Role]
    (t : Term Role Var) (ν : Var → WinnerSet Role) :
    t.leafMass ν = t.choiceCount + 1 + t.inputExcess ν :=
  Results.Algebra.winner_leaf_mass t ν

theorem winner_budget_eq_iff {Role : Type u} {Var : Type v} [Finite Role]
    (t : Term Role Var) (ν : Var → WinnerSet Role) :
    (t.eval ν).val.ncard = t.leafMass ν ↔ t.DisjointChoices ν :=
  Results.Algebra.winner_budget_eq_iff t ν

theorem atomic_winner_budget {Role : Type u} {Var : Type v} [Finite Role]
    (t : Term Role Var) (ν : Var → WinnerSet Role) (atomic : ∀ x, (ν x).val.ncard = 1) :
    (t.eval ν).val.ncard ≤ min (Nat.card Role) (t.choiceCount + 1) :=
  Results.Algebra.atomic_winner_budget t ν atomic

theorem absorbing_winner_budget {Role : Type u} {Var : Type v} [Finite Role]
    (t : Term Role Var) (ν : Var → WinnerSet Role) :
    (t.eval ν).val.ncard + t.absorbingCount ν ≤ t.leafMass ν :=
  Results.Algebra.absorbing_winner_budget t ν

/-- `game:cor:ground-size`: the best value at each exact syntax size. -/
theorem public_sharp_winner_budget {Role : Type u} [Finite Role]
    (three : Fin 3 ↪ Role) (n : ℕ) :
    (∀ G : Strategic.Tree Role, G.choiceCount = n →
      (Strategic.value G).val.ncard ≤ min (Nat.card Role) (n + 1)) ∧
    ∃ G : Strategic.Tree Role, G.choiceCount = n ∧
      (Strategic.value G).val.ncard = min (Nat.card Role) (n + 1) :=
  Results.Games.public_sharp_winner_budget three n

theorem public_sharp_absorbing_budget {Role : Type u} [Finite Role]
    (three : Fin 3 ↪ Role) (n h : ℕ) (hn : h ≤ n) :
    (∀ G : Strategic.Tree Role, G.choiceCount = n → G.absorbingCount = h →
      (Strategic.value G).val.ncard ≤ min (Nat.card Role) (n + 1 - h)) ∧
    ∃ G : Strategic.Tree Role, G.choiceCount = n ∧ G.absorbingCount = h ∧
      (Strategic.value G).val.ncard = min (Nat.card Role) (n + 1 - h) :=
  Results.Games.public_sharp_absorbing_budget three n h hn


theorem core_source_reconstruction {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    (v : Var → WinnerSet Role) (k : Role) :
    k ∈ (t.eval v).val ↔ ∃ j, k ∈ (v j).val ∧
      k ∈ (t.eval (Core.Sources.probe three k j (Core.Sources.pattern k j v))).val :=
  Results.Algebra.core_source_reconstruction three t ht v k

theorem core_source_probe_count {Role : Type u} [Fintype Role]
    {Var : Type v} [Fintype Var] [DecidableEq Var] :
    Fintype.card (Core.Sources.ProbeIndex Role Var) =
      Fintype.card Var * Fintype.card Role ^ Fintype.card Var :=
  Results.Algebra.core_source_probe_count

theorem core_guard_synthesis {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) {k : Role} {j : Var}
    (G : Finset (Core.Sources.Guard k j)) (hG : G.Nonempty) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ p : Core.Sources.Pattern k j,
      (k ∈ (t.eval (Core.Sources.probe three k j p)).val ↔
        ∃ g ∈ G, Core.Sources.Enabled g p) :=
  Results.Algebra.core_guard_synthesis three G hG

theorem core_binary_interpolation {Role : Type u} {Var : Type v}
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    Core.PairwiseInterpolable f ↔ Core.PreservesBinary f :=
  Results.Algebra.core_binary_interpolation f

theorem core_pairwise_obstruction {Role : Type u} (three : Fin 3 ↪ Role) :
    Core.PairwiseInterpolable (Core.pairwiseCounterexample three) ∧
    Core.PreservesBinary (Core.pairwiseCounterexample three) ∧
    (∀ v w : Fin 3 → WinnerSet Role, (∀ i, (v i).val ⊆ (w i).val) →
      (Core.pairwiseCounterexample three v).val ⊆ (Core.pairwiseCounterexample three w).val) ∧
    (∀ A, Core.pairwiseCounterexample three (fun _ => A) = A) ∧
    (∃ s : Term Role (Fin 3), s.IsCore ∧ ∀ v r,
      (Core.pairwiseCounterexample three v = WinnerSet.singleton r ↔
        s.eval v = WinnerSet.singleton r)) ∧
    ¬∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v, t.eval v = Core.pairwiseCounterexample three v :=
  Results.Algebra.core_pairwise_obstruction three

theorem core_local_normal_forms {Role : Type u} [Fintype Role]
    {Var : Type v} [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) (hf : Core.LocallyInterpolable 3 f) :
    (∀ v k, k ∈ (f v).val ↔ ∃ j, k ∈ (v j).val ∧
      k ∈ (f (Core.Sources.probe three k j (Core.Sources.pattern k j v))).val) ∧
    Core.Sources.Canonical (Core.Sources.normalForm three f) ∧
    ∀ v, Core.Sources.meaning (Core.Sources.normalForm three f) v = (f v).val :=
  Core.Sources.local_normal_forms three f hf

theorem core_profile_maximum {Role : Type u} [Fintype Role]
    {Var : Type v} [Fintype Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (ht : t.IsCore) :
    ∃ e : Term Role Var, e.IsCore ∧
      (∀ v r, e.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) ∧
      (∀ v, (t.eval v).Ambiguous → (e.eval v).val = ⋃ j, (v j).val) ∧
      ∀ f : (Var → WinnerSet Role) → WinnerSet Role,
        (∀ v, (f v).val ⊆ ⋃ j, (v j).val) →
        (∀ v r, f v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) →
        ∀ v, (f v).val ⊆ (e.eval v).val :=
  Core.exists_profile_maximum three t ht

theorem core_profile_nonconvexity {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
    ∃ s t : Term Role (Fin 3), s.IsCore ∧ t.IsCore ∧
      (∀ v r, s.eval v = WinnerSet.singleton r ↔ t.eval v = WinnerSet.singleton r) ∧
      (∀ v r, Core.threewiseCounterexample three v = WinnerSet.singleton r ↔
        t.eval v = WinnerSet.singleton r) ∧
      (∀ v, (s.eval v).val ⊆ (Core.threewiseCounterexample three v).val ∧
        (Core.threewiseCounterexample three v).val ⊆ (t.eval v).val) ∧
      ¬∃ u : Term Role (Fin 3), u.IsCore ∧ ∀ v, u.eval v = Core.threewiseCounterexample three v :=
  Core.profile_fiber_nonconvex three

theorem core_local_interpolation {Role : Type u} {Var : Type v} (n : ℕ)
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    Core.LocallyInterpolable n f ↔ Core.PreservesInvariants n f :=
  Core.locallyInterpolable_iff_preservesInvariants n f

theorem core_four_valuation_persistence {Role : Type u} {Var : Type v} (three : Fin 3 ↪ Role)
    (tag : Var → Fin 3) (t : Term Role Var) (ht : t.IsCore)
    (hB : three 2 ∉ (t.eval (fun x =>
      ![(WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 1)),
        WinnerSet.singleton (three 0),
        (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2))] (tag x))).val)
    (hC : three 0 ∉ (t.eval (fun x =>
      ![WinnerSet.singleton (three 0), WinnerSet.singleton (three 1),
        WinnerSet.singleton (three 2)] (tag x))).val)
    (hD : three 2 ∉ (t.eval (fun x =>
      ![WinnerSet.singleton (three 1), WinnerSet.singleton (three 2),
        WinnerSet.singleton (three 0)] (tag x))).val) :
    three 2 ∉ (t.eval (fun x =>
      ![(WinnerSet.singleton (three 0)).union (WinnerSet.singleton (three 2)),
        WinnerSet.singleton (three 1), WinnerSet.singleton (three 0)] (tag x))).val :=
  Core.four_valuation_persistence three tag t ht hB hC hD


theorem core_ternary_obstruction {Role : Type u} (three : Fin 3 ↪ Role) :
    Core.LocallyInterpolable 3 (Core.threewiseCounterexample three) ∧
    Core.PreservesInvariants 3 (Core.threewiseCounterexample three) ∧
    (∃ s : Term Role (Fin 3), s.IsCore ∧ ∀ v r,
      (Core.threewiseCounterexample three v = WinnerSet.singleton r ↔
        s.eval v = WinnerSet.singleton r)) ∧
    (∀ i : Fin 3, ∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v,
      WinnerSet.view (three i) (Core.threewiseCounterexample three v) =
        WinnerSet.view (three i) (t.eval v)) ∧
    ¬∃ t : Term Role (Fin 3), t.IsCore ∧ ∀ v, t.eval v = Core.threewiseCounterexample three v :=
  Core.Threewise.counterexample three

theorem core_three_local_without_minorant {Role : Type u} (three : Fin 3 ↪ Role) :
    ∃ f : (Fin 4 → WinnerSet Role) → WinnerSet Role,
      Core.LocallyInterpolable 3 f ∧ Core.PreservesInvariants 3 f ∧
        ¬∃ t : Term Role (Fin 4), t.IsCore ∧ ∀ v, (t.eval v).val ⊆ (f v).val :=
  Core.exists_three_local_without_core_minorant three

theorem core_four_local_without_minorant {Role : Type u} (three : Fin 3 ↪ Role) :
    ∃ f : (Fin 5 → WinnerSet Role) → WinnerSet Role,
      Core.LocallyInterpolable 4 f ∧ Core.PreservesInvariants 4 f ∧
        ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ v, (t.eval v).val ⊆ (f v).val :=
  Core.exists_four_local_without_core_minorant three

theorem core_five_local_profile_obstruction {Role : Type u} [Fintype Role]
    (three : Fin 3 ↪ Role) :
    ∃ s t : Term Role (Fin 5), ∃ f : (Fin 5 → WinnerSet Role) → WinnerSet Role,
      s.IsCore ∧ t.IsCore ∧ Core.LocallyInterpolable 5 f ∧ Core.PreservesInvariants 5 f ∧
      (∀ v r, s.eval v = singleton r ↔ t.eval v = singleton r) ∧
      (∀ v r, f v = singleton r ↔ s.eval v = singleton r) ∧
      (∀ v, (s.eval v).val ⊆ (f v).val ∧ (f v).val ⊆ (t.eval v).val) ∧
      ¬∃ u : Term Role (Fin 5), u.IsCore ∧ ∀ v, u.eval v = f v :=
  Core.exists_five_local_profile_fiber_nonconvex three

/-- `core:prop:bichain`: the three-owner quotient is the union-expanded bichain. -/
theorem observer_bichain :
    (∀ x y : Bichain.Value,
      Bichain.Value.viewEquiv (Bichain.Value.inf x y) = PlayerView.choice 1
        (Bichain.Value.viewEquiv x) (Bichain.Value.viewEquiv y)) ∧
    (∀ x y : Bichain.Value,
      Bichain.Value.viewEquiv (Bichain.Value.sup x y) = PlayerView.choice 2
        (Bichain.Value.viewEquiv x) (Bichain.Value.viewEquiv y)) ∧
    (∀ x y : Bichain.Value,
      Bichain.Value.viewEquiv (Bichain.Value.union x y) = PlayerView.choice 0
        (Bichain.Value.viewEquiv x) (Bichain.Value.viewEquiv y)) ∧
    ∀ x y : Bichain.Value,
      Bichain.Value.median x y .neutral = Bichain.Value.union x y :=
  Bichain.Value.observer_model

/-- `core:thm:bichain-fiber`: existence in the Boolean projection fiber. -/
theorem bichain_projection_fiber {Var : Type v} (t : Bichain.Term (Option Var))
    (ht : t.IsPure) :
    t.IsBooleanProjection ↔ ∃ g : Option (Bichain.Term Var), ∀ v,
      t.eval v = (Bichain.Term.optionalLift g).eval v :=
  Bichain.Term.isBooleanProjection_iff_recovery t ht

/-- Uniqueness in `core:thm:bichain-fiber`, including the additional zero trace. -/
theorem bichain_projection_fiber_unique {Var : Type v}
    (g h : Option (Bichain.Term Var)) :
    (∀ v, (Bichain.Term.optionalLift g).eval v = (Bichain.Term.optionalLift h).eval v) ↔
      g.map (fun t => t.eval) = h.map (fun t => t.eval) :=
  Bichain.Term.optionalLift_eq_iff g h

/-- `core:thm:atomic-observer`: a closed test on one atomic observer table. -/
theorem core_atomic_observer {Role : Type u} {Var : Type v} [Fintype Var]
    (three : Fin 3 ↪ Role) (h : Finset Var → Finset Var → Prop) :
    Core.AtomicObserver.Admissible h ↔ ∃ t : Term Role Var, t.IsCore ∧
      ∀ L U, L ⊆ U → (h L U ↔
        three 0 ∈ (t.eval (Core.AtomicObserver.values three L U)).val) :=
  Core.AtomicObserver.admissible_iff_embedding three h

/-- `core:prop:observer-amalgamation`: separate complete views need not glue. -/
theorem core_observer_amalgamation :
    ∃ F : (Fin 3 → WinnerSet (Fin 3)) → WinnerSet (Fin 3),
      (∀ v, (F v).val = Core.AtomicAmalgamation.raw v) ∧
      (∀ v r, F v = singleton r ↔ ∀ j, v j = singleton r) ∧
      (∀ r : Fin 3, ∃ t : Term (Fin 3) (Fin 3), t.IsCore ∧ ∀ v,
        WinnerSet.view r (F v) = WinnerSet.view r (t.eval v)) ∧
      ¬∃ t : Term (Fin 3) (Fin 3), t.IsCore ∧
        ∀ i, t.eval (Core.AtomicAmalgamation.atomicInput i) =
          F (Core.AtomicAmalgamation.atomicInput i) :=
  Core.AtomicAmalgamation.exists_amalgamation_failure

/-- `core:lem:cyclic-persistence`: cyclic derivatives cannot point in only one direction. -/
theorem core_cyclic_persistence {Role : Type u} {Var : Type v} [Finite Var]
    (three : Fin 3 ↪ Role) (next : Equiv.Perm Var) (i : Var) (hi : next i ≠ i)
    (t : Term Role Var) (ht : t.IsCore) :
    three 0 ∈ (t.eval (Core.Crown.positive three next i)).val →
      ∃ j, three 0 ∈ (t.eval (Core.Crown.negative three next j)).val :=
  Core.Crown.persistence three next i hi t ht

/-- `core:cor:full-not-finitely-related`: constants and role switches do not remove the obstruction. -/
theorem full_not_finitely_related {Role : Type u} [Fintype Role]
    (three : Fin 3 ↪ Role) (m : ℕ) :
    ∃ f : (Fin (m+3) → WinnerSet Role) → WinnerSet Role,
      Core.LocallyInterpolable m f ∧
        ¬∃ t : Term Role (Fin (m+3)), ∀ v, t.eval v = f v :=
  Core.Crown.exists_full_syntax_obstruction three m

theorem full_no_finite_relation_basis {Role : Type u} [Fintype Role]
    {Index : Type v} [Finite Index] (three : Fin 3 ↪ Role) (arity : Index → ℕ)
    (relations : ∀ i, Set (Fin (arity i) → WinnerSet Role))
    (hrelations : ∀ i, Core.InvariantRelation (arity i) (relations i)) :
    ∃ n : ℕ, ∃ f : (Fin n → WinnerSet Role) → WinnerSet Role,
      (∀ i, Core.PreservesRelation (relations i) f) ∧
        ¬∃ t : Term Role (Fin n), ∀ v, t.eval v = f v :=
  Core.Crown.exists_full_finite_family_obstruction three arity relations hrelations

/-- `core:thm:exponential-locality`: an exact exponential interpolation threshold. -/
theorem core_exponential_locality {Role : Type u} [Fintype Role]
    (three : Fin 3 ↪ Role) (d : ℕ) (hd : 2 ≤ d) :
    ∃ f : ((Fin d × Bool) → WinnerSet Role) → WinnerSet Role,
      Core.LocallyInterpolable (2 ^ d) f ∧
      ¬Core.LocallyInterpolable (2 ^ d + 1) f ∧
      (∀ A : WinnerSet Role, f (fun _ => A) = A) ∧
      ¬∃ t : Term Role (Fin d × Bool), ∀ values, t.eval values = f values :=
  Core.GrayCrown.exists_exponential_obstruction three d hd

theorem core_peeling_interpolation {Role : Type u} {Row : Type v} {Var : Type w}
    [Fintype Role] [Fintype Row] [DecidableEq Role] [DecidableEq Row]
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role) (U : Row → Set Role)
    (N : Finset Row) (D : Finset (Row × Role)) (p : Option (Row × Role)) :
    Core.Interpolation.Peels values U N D p ↔
      ∃ t : Term Role Var, t.IsCore ∧
        Core.Interpolation.Fits N U D p (fun i => t.eval (values i)) :=
  Core.Interpolation.peels_iff three values U N D p

/-- `core:thm:hypergraph-basis`: a complete relation schema with closed cut axioms. -/
theorem core_closed_hypergraph_basis {Role : Type u} {Row : Type v}
    [Fintype Role] [DecidableEq Role] [Fintype Row] [DecidableEq Row]
    (three : Fin 3 ↪ Role) (R : (Row → WinnerSet Role) → Prop) :
    (∀ r x y, R x → R y → R (fun i => WinnerSet.choice r (x i) (y i))) ↔
      ∃ D : Core.Hypergraphs.Diagram Row Role, D.Admissible ∧
        ∀ x : Row → Set Role,
          (∃ y : Row → WinnerSet Role, R y ∧ ∀ i, (y i).val = x i) ↔ D.Models x :=
  Core.Hypergraphs.choiceClosed_iff_hypergraphs three R

/-- The complete operation criterion in `core:thm:hypergraph-basis`. -/
theorem core_hypergraph_operations {Role : Type u} {Var : Type v}
    [Fintype Role] [DecidableEq Role] [Fintype Var]
    (three : Fin 3 ↪ Role) (f : (Var → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v) ↔
      ∀ m (D : Core.Hypergraphs.Diagram (Fin m) Role), D.Admissible →
        ∀ values : Fin m → Var → WinnerSet Role,
          (∀ j, D.Models (fun i => (values i j).val)) →
            D.Models (fun i => (f (values i)).val) :=
  Core.Hypergraphs.operation_iff_hypergraphs three f

/-- `core:cor:hypergraph-guards`: complete global obstruction conditions. -/
theorem core_hypergraph_guards {Role : Type u} {Var : Type v}
    [Fintype Role] [DecidableEq Role] [Fintype Var] [DecidableEq Var]
    (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Core.Sources.Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ Core.Sources.normalForm three (fun v => t.eval v) = G) ↔
      Core.Sources.Canonical G ∧
      (∃ q : Core.Sources.ProbeIndex Role Var, Core.Sources.coefficients G q.1 q.2.1 q.2.2) ∧
      ∀ q : Core.Sources.ProbeIndex Role Var, Core.Sources.coefficients G q.1 q.2.1 q.2.2 →
        ∀ D : Core.Hypergraphs.Diagram (Core.Sources.ProbeIndex Role Var) Role,
          D.Admissible → (∀ j, D.Models (fun z => (Core.Sources.probeAt three z j).val)) →
            ¬D.Supports (some (q,q.1))
              ((Core.Sources.negativeProbes G).image (fun z => (z,z.1))) :=
  Core.Sources.guard_table_iff_hypergraph_persistence three G

/-- `core:thm:profile-relations`: closed profile relations have restricted Horn theories. -/
theorem core_profile_relations {Index : Type u} {Role : Type v}
    [Fintype Index] [DecidableEq Index] [DecidableEq Role]
    (owner : Index → Role) (three : Fin 3 ↪ Role) (R : Set (Index → Bool)) :
    Core.ProfileRelations.ChoiceClosed owner R ↔
      ∃ T : Core.ProfileRelations.Theory owner,
        ∀ x, x ∈ R ↔ T.Models x :=
  Core.ProfileRelations.choiceClosed_iff_theory owner three R

theorem core_singleton_profiles {Role : Type u} [DecidableEq Role] [Fintype Role]
    {Var : Type v} [Fintype Var] (three : Fin 3 ↪ Role)
    (F : Role → (Var → Bool) → Bool) :
    (∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      ∀ i v, Core.profile i v t = F i v) ↔ Core.AdmissibleProfiles F :=
  Results.Algebra.core_singleton_profiles three F

/-- `core:thm:one-bound-profiles`: closed input conditions for one bound and rainbow demands. -/
theorem core_single_bound_profiles {Role : Type u} {Var : Type v} [DecidableEq Role]
    (J : Finset Role) (A : Role → Var → Bool) (values : Var → WinnerSet Role)
    (U : Set Role) :
    letI := Equational.coreStructure Role
    (∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ r ∈ J, Core.profile r (A r) t = true) ∧ (t.realize values).val ⊆ U) ↔
      (∃ j, ∀ r ∈ J, A r j = true) ∧
      ((∃ j, (∀ r ∈ J, A r j = true) ∧ (values j).val ⊆ U) ∨
        ∃ s ∈ J, s ∈ U ∧ ∃ j, values j = singleton s ∧
          ∀ r ∈ J, r ≠ s → A r j = true) :=
  Core.rainbow_budget_iff J A values U

/-- The projection or single-choice witness clause of `core:thm:one-bound-profiles`. -/
theorem core_single_bound_small_witness {Role : Type u} {Var : Type v} [DecidableEq Role]
    (J : Finset Role) (A : Role → Var → Bool) (values : Var → WinnerSet Role)
    (U : Set Role) :
    letI := Equational.coreStructure Role
    (∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      (∀ r ∈ J, Core.profile r (A r) t = true) ∧ (t.realize values).val ⊆ U) →
      (∃ j, (∀ r ∈ J, A r j = true) ∧ (values j).val ⊆ U) ∨
        ∃ s j l, (∀ r ∈ J,
          Core.profile r (A r) (Core.choiceTerm s (.var j) (.var l)) = true) ∧
          ((Core.choiceTerm s (.var j) (.var l)).realize values).val ⊆ U :=
  Core.rainbow_budget_small_witness J A values U

/-- The ownerwise positive/negative separation test used in `core:thm:bounded-profiles`. -/
theorem core_bounded_profile_pair {Role : Type u} {Var : Type v} [DecidableEq Role]
    (r : Role) (A B : Var → Bool) (values : Var → WinnerSet Role) (U : Set Role) :
    letI := Equational.coreStructure Role
    Core.ProfileBounds.PairSafe r A B values U ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        Core.profile r A t = true ∧ Core.profile r B t = false ∧
          (t.realize values).val ⊆ U :=
  Core.ProfileBounds.pairSafe_iff r A B values U

/-- `core:thm:bounded-query`: a requested winner adds two direct input tests. -/
theorem core_bounded_rainbow_query {Role : Type u} {Var : Type v} [DecidableEq Role]
    (J : Finset Role) (A : Role → Var → Bool) (values : Var → WinnerSet Role)
    (U : Set Role) (k : Role) :
    letI := Equational.coreStructure Role
    Core.ProfileBounds.QuerySafe J A values U k ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r ∈ J, Core.profile r (A r) t = true) ∧
        (t.realize values).val ⊆ U ∧ k ∈ (t.realize values).val :=
  Core.ProfileBounds.querySafe_iff J A values U k

/-- `core:thm:bounded-profiles`: a closed criterion for all profiles and one output bound. -/
theorem core_bounded_profiles {Role : Type u} {Var : Type v}
    [DecidableEq Role] [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role) (U : Set Role) :
    letI := Equational.coreStructure Role
    Core.ProfileBounds.ProfileCondition Φ values U ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r A, Core.profile r A t = Φ r A) ∧ (t.realize values).val ⊆ U :=
  Core.ProfileBounds.profileCondition_iff three Φ values U

/-- Removing the bound recovers exactly the original singleton-profile conditions. -/
theorem core_unbounded_profile_condition {Role : Type u} {Var : Type v} [Fintype Role]
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role) :
    Core.ProfileBounds.ProfileCondition Φ values Set.univ ↔ Core.AdmissibleProfiles Φ :=
  Core.ProfileBounds.profileCondition_univ_iff_admissibleProfiles Φ values

/-- `core:cor:profile-bound`: an output bound can couple individually realizable profiles. -/
theorem core_profile_bound_coupling :
    letI := Equational.coreStructure (Fin 3)
    ∃ (values : Fin 4 → WinnerSet (Fin 3))
      (P : Fin 3 → (Fin 4 → Bool) → Bool),
      Core.AdmissibleProfiles P ∧
      (∀ r, ∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 4),
        (∀ E, Core.profile r E t = P r E) ∧ 1 ∉ (t.realize values).val) ∧
      ¬∃ t : Equational.Term (Equational.CoreSymbol (Fin 3)) (Fin 4),
        (∀ r E, Core.profile r E t = P r E) ∧ 1 ∉ (t.realize values).val :=
  Core.safe_profiles_not_ownerwise

/-- `core:thm:one-point-completion`: all profiles and one exact value have a closed test. -/
theorem core_exact_profile_point {Role : Type u} {Var : Type v}
    [DecidableEq Role] [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (Φ : Role → (Var → Bool) → Bool) (values : Var → WinnerSet Role)
    (target : WinnerSet Role) :
    letI := Equational.coreStructure Role
    Core.ProfileBounds.OnePointCondition Φ values target ↔
      ∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
        (∀ r A, Core.profile r A t = Φ r A) ∧ t.realize values = target :=
  Core.ProfileBounds.onePointCondition_iff three Φ values target

/-- The `core:thm:five-local-profile` example passes every exact one-point profile test. -/
theorem core_pointwise_profile_obstruction {Role : Type u}
    [Fintype Role] [DecidableEq Role] (three : Fin 3 ↪ Role) :
    ∃ (Φ : Role → (Fin 5 → Bool) → Bool)
      (f : (Fin 5 → WinnerSet Role) → WinnerSet Role),
      Core.AdmissibleProfiles Φ ∧ Core.LocallyInterpolable 5 f ∧
      (∀ values, Core.ProfileBounds.OnePointCondition Φ values (f values)) ∧
      ¬∃ t : Term Role (Fin 5), t.IsCore ∧ ∀ values, t.eval values = f values :=
  Core.exists_pointwise_profile_obstruction three

/-- `core:prop:whole-inputs`: every winner has a whole input contained in the output. -/
theorem core_whole_input_provenance {Role : Type u} {Var : Type v}
    (t : Term Role Var) (ht : t.IsCore) (values : Var → WinnerSet Role)
    (k : Role) (hk : k ∈ (t.eval values).val) :
    ∃ j, k ∈ (values j).val ∧ (values j).val ⊆ (t.eval values).val :=
  Core.whole_input_provenance_of_isCore t ht values k hk

theorem core_output_is_input_union {Role : Type u} {Var : Type v}
    (t : Term Role Var) (ht : t.IsCore) (values : Var → WinnerSet Role) :
    (t.eval values).val =
      ⋃ j, ⋃ (_ : (values j).val ⊆ (t.eval values).val), (values j).val :=
  Core.eval_eq_iUnion_whole_inputs t ht values

/-- `core:prop:omission`: all inputs containing an omitted owner are irrelevant. -/
theorem core_omission_independence {Role : Type u} {Var : Type v}
    (a : Role) (t : Term Role Var) (ht : t.IsCore)
    (values changed : Var → WinnerSet Role)
    (agree : ∀ j, a ∉ (values j).val → changed j = values j)
    (habsent : a ∉ (t.eval values).val) : t.eval changed = t.eval values :=
  Core.omission_independence a t ht values changed agree habsent

/-- `core:thm:negative-budgets`: upper-bound feasibility has no bounded row test. -/
theorem core_negative_budget_obstructions {Role : Type u} (three : Fin 3 ↪ Role) (n : ℕ) :
    ∃ values : Fin n → Fin n → WinnerSet Role,
      (∀ i j, ∃ r : Fin 3, values i j = singleton (three r)) ∧
      (∀ S : Finset (Fin n), S ≠ Finset.univ →
        ∃ j : Fin n, ∀ i ∈ S, three 0 ∉ (values i j).val) ∧
      ¬∃ t : Term Role (Fin n), t.IsCore ∧
        ∀ i, three 0 ∉ (t.eval (values i)).val :=
  Core.Staircase.exists_atomic_irredundant_negative_budgets three n

theorem core_colored_graph_representation {Role : Type u} {Var : Type v} [Nonempty Role]
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    Core.ColoredGraph.Represents f ↔
      ∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v :=
  Core.ColoredGraph.represents_iff f

theorem core_colored_graph_guards {Role : Type u} {Var : Type v}
    [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (G : ∀ (k : Role) (j : Var), Finset (Core.Sources.Guard k j)) :
    (∃ t : Term Role Var, t.IsCore ∧ Core.Sources.normalForm three (fun v => t.eval v) = G) ↔
      ∃ (n : ℕ) (H : Core.ColoredGraph.Graph Role (Fin n)) (label : Fin n → Var),
        0 < n ∧ H.NoRainbow ∧ H.NoAlternatingPath ∧ ∀ k j g,
          g ∈ G k j ↔ Core.Sources.Prime
            (fun p => H.Wins Set.univ label (Core.Sources.probe three k j p) k) g :=
  Core.ColoredGraph.guard_realization_iff three G

theorem core_three_valuation_persistence {Role : Type u} {Var : Type v} (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (tag : Var → Fin 3) (t : Term Role Var) (ht : t.IsCore)
    (hf : t.eval (fun x => ![(WinnerSet.singleton a).union (WinnerSet.singleton b),
      WinnerSet.singleton b, WinnerSet.singleton b] (tag x)) = WinnerSet.singleton b)
    (hs : t.eval (fun x => ![WinnerSet.singleton b,
      (WinnerSet.singleton b).union (WinnerSet.singleton c),
      (WinnerSet.singleton a).union (WinnerSet.singleton b)] (tag x)) =
        (WinnerSet.singleton b).union (WinnerSet.singleton c)) :
    b ∈ (t.eval (fun x => ![WinnerSet.singleton a, WinnerSet.singleton b,
      WinnerSet.singleton c] (tag x))).val :=
  Results.Algebra.core_three_valuation_persistence a b c hab hac hbc tag t ht hf hs

theorem idempotency_certificates : ∀ {Role : Type u} [Fintype Role] (_three : Fin 3 ↪ Role),
    (∀ D : Set (WinnerSet Role), (∀ A ∈ D, WinnerSet.Ambiguous A) →
      ((∀ (n : ℕ) (t : Term Role (Fin n)),
        (∀ A ∈ D, t.eval (fun _ => A) = A) →
          ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ↔
        (∀ k, ∃ A ∈ D, k ∉ A.val) ∧
          (∀ a b, (∀ A ∈ D, a ∈ A.val ↔ b ∈ A.val) → a = b))) ∧
    (∀ D : Finset (WinnerSet Role),
      (∀ (n : ℕ) (t : Term Role (Fin n)),
        (∀ A ∈ D, t.eval (fun _ => A) = A) →
          ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) →
      (if Fintype.card Role = 3 then 3 else Nat.clog 2 (Fintype.card Role + 1)) ≤ D.card) ∧
    (∃ D : Finset (WinnerSet Role), (∀ A ∈ D, WinnerSet.Ambiguous A) ∧
      (∀ (n : ℕ) (t : Term Role (Fin n)),
        (∀ A ∈ D, t.eval (fun _ => A) = A) →
          ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧
      D.card = if Fintype.card Role = 3 then 3 else Nat.clog 2 (Fintype.card Role + 1)) :=
  @KFOL.Results.idempotency_certificates

theorem reset_substitution : ∀ {Var : Type v} {Var' : Type w} [DecidableEq Var] [DecidableEq Var']
    (t : Reset.Term Var) (inner : Var → Reset.Term Var'),
    Reset.Term.root (t.subst inner) = (inner t.root).root ∧
    (∀ {Role : Type u} (valuation : Var' → WinnerSet Role),
      Reset.Term.eval (t.subst inner) valuation =
        t.eval (fun i => (inner i).eval valuation)) ∧
    (∀ j, Reset.Term.table (t.subst inner) j = Reset.Term.minimize
      (t.varFinset.biUnion (fun i => (t.table i).biUnion (fun A =>
        ((inner i).table j).image (fun C => A.image (fun k => (inner k).root) ∪ C))))) :=
  @KFOL.Results.reset_substitution

theorem reset_family_product : ∀ {Var : Type v} [DecidableEq Var] (s t : Reset.Term Var),
    (Reset.Term.step s t).feasible =
      {D : Finset Var | D = ∅ ∨ ∃ A ∈ s.feasible, ∃ C ∈ t.feasible,
        C.Nonempty ∧ D = A ∪ C} :=
  @KFOL.Results.reset_family_product

theorem core_variable_bound_obstruction : ∀ {Role : Type u} [DecidableEq Role] [Fintype Role]
    (_three : Fin 3 ↪ Role),
    letI := Equational.coreStructure Role
    letI := Core.Native.structureOf (Role := Role)
    Fintype.card (Core.Native Role) = Fintype.card Role + 2 ∧
    (∀ e : Equational.Identity (Equational.CoreSymbol Role),
      e.variableCount ≤ Fintype.card Role → e.Holds (WinnerSet Role) →
        e.Holds (Core.Native Role)) ∧
    (Core.exhaustionIdentity _three).Holds (WinnerSet Role) ∧
    ¬(Core.exhaustionIdentity _three).Holds (Core.Native Role) ∧
    (Core.exhaustionIdentity _three).variableCount = Fintype.card Role + 1 ∧
    ¬Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Core.Native Role) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role),
      (∀ e ∈ T, e.variableCount ≤ Fintype.card Role) → ¬Equational.IsBasis (WinnerSet Role) T) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role),
      Equational.IsBasis (WinnerSet Role) T → ∃ e ∈ T, Fintype.card Role + 1 ≤ e.variableCount) :=
  @KFOL.Results.core_variable_bound_obstruction

/-- `owner:thm:no-four-variable-basis`: the concrete local obstruction. -/
theorem owner_four_variable_obstruction :
    letI := Owner.fourStructure (Role := Unit)
    Fintype.card Owner.FourVariableObstruction.Carrier = 6 ∧
    (∀ e : Equational.Identity (Owner.Symbol Unit), e.variableCount ≤ 4 →
      e.Holds Owner.Four → e.Holds Owner.FourVariableObstruction.Carrier) ∧
    Owner.FourVariableObstruction.actionBand.Holds Owner.Four ∧
    ¬Owner.FourVariableObstruction.actionBand.Holds Owner.FourVariableObstruction.Carrier ∧
    Owner.FourVariableObstruction.actionBand.variableCount = 5 :=
  Results.Algebra.owner_four_variable_obstruction

theorem core_typed_upper_clone_cover : ∀ {Role : Type u} [DecidableEq Role]
    {C : Type v} [(Equational.language (Equational.CoreSymbol Role)).Structure C]
    {P : Type w} [(Equational.language (Equational.CoreSymbol Role)).Structure P]
    (_three : Fin 3 ↪ Role)
    (hC : letI := Equational.coreStructure Role
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) C)
    (e : C)
    (_reflecting : ∀ (r : Role) (c : C),
      Core.join _three (Core.operation r e c) e = e → Core.join _three c e = e)
    (R : Set Role) (_proper : R ≠ Set.univ)
    (η : Core.ideal hC _three e →[Equational.language (Equational.CoreSymbol Role)]
      Core.Native.atomicRestriction R)
    (_typed : ∀ (c : Core.ideal hC _three e) (r : Role),
      (η c).val = Core.Native.atom r ↔ Core.operation r e c.val ≠ e)
    (_hP : letI := Equational.coreStructure Role
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) P)
    (q : P →[Equational.language (Equational.CoreSymbol Role)] C)
    (_onto : Function.Surjective q)
    (label : P →[Equational.language (Equational.CoreSymbol Role)] Core.Native.atomicRestriction R)
    (_compatible : ∀ (u : P) (hu : Core.join _three (q u) e = e), label u = η ⟨q u, hu⟩),
    letI := Equational.coreStructure Role
    letI := Core.upperStructure (Role := Role) e
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Option C) :=
  @KFOL.Results.core_typed_upper_clone_cover

theorem public_equilibrium_strategic_form : ∀ {Role : Type u} [DecidableEq Role]
    {g : Strategic.Tree Role} (p : Strategic.Profile g),
    (Strategic.IsNash p ↔ GameTheory.IsNash (Strategic.gameForm g)
      (Strategic.winningPreference Role) (fun _ => p)) ∧
    (Strategic.IsSubgamePerfect p ↔
      ∀ {h : Strategic.Tree Role} (q : Strategic.Profile h), Strategic.Restriction p q →
        GameTheory.IsNash (Strategic.gameForm h) (Strategic.winningPreference Role) (fun _ => q)) :=
  @KFOL.Results.public_equilibrium_strategic_form

theorem public_term_interpretation : ∀ {Role : Type u} {Var : Type v}
    (components : Var → Strategic.Tree Role) (t : Term Role Var),
    Strategic.value (Strategic.compile components t) =
      t.eval (fun x => Strategic.value (components x)) :=
  @KFOL.Results.public_term_interpretation

theorem native_nonfinite_basis : ∀ {Role : Type u} [DecidableEq Role] [Finite Role]
    (_three : Fin 3 ↪ Role),
    letI := Core.Native.structureOf (Role := Role)
    (∀ (d : ℕ) (T : Equational.Theory (Equational.CoreSymbol Role)),
      (∀ e ∈ T, e.variableCount ≤ d) →
        ¬(∀ e : Equational.Identity (Equational.CoreSymbol Role),
          e.Holds (Core.Native Role) ↔ Equational.Derives T e.lhs e.rhs)) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role), T.Finite →
      ¬(∀ e : Equational.Identity (Equational.CoreSymbol Role),
        e.Holds (Core.Native Role) ↔ Equational.Derives T e.lhs e.rhs)) :=
  @KFOL.Results.native_nonfinite_basis

theorem round_protocol_foundations : ∀ {Role : Type u} [Fintype Role] [DecidableEq Role]
    (game : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role),
    Finite game.execution.History ∧ Finite (game.serialized order).execution.History ∧
    game.information.PerfectRecall ∧ (game.serialized order).information.DecisionRecall ∧
    (∀ p : Rounds.Game.Position game, game.execution.Reachable p) ∧
    (∀ h : game.execution.History, game.information.IsSubgameRoot h) ∧
    (∃ bound, 0 < bound ∧ game.execution.BoundedHorizon bound) ∧
    (∃ bound, 0 < bound ∧ (game.serialized order).execution.BoundedHorizon bound) ∧
    (∀ payoff : Role → (game.serialized order).execution.History → ℝ,
      ∃ assessment : (game.serialized order).information.BehavioralAssessment,
        assessment.IsSequentialEquilibrium
          (game.serial_decision_recall order).decisionInformationAntichain
          (game.serial_well_founded_histories order) payoff) :=
  @KFOL.Results.round_protocol_foundations

theorem round_profile_consistency : ∀ {Role : Type u} [DecidableEq Role] [Finite Role]
    (game : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (strategy : (i : Role) → (game.serialized order).information.BehavioralPolicy i),
    ∃ assessment : (game.serialized order).information.BehavioralAssessment,
      assessment.strategy = strategy ∧
      assessment.IsSequentiallyConsistent
        (game.serial_decision_recall order).decisionInformationAntichain ∧
      ∀ (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role),
        assessment.belief i (game.serialSite order h ht i) =
          game.productBelief order strategy h ht i :=
  @KFOL.Results.round_profile_consistency

theorem round_product_beliefs : ∀ {Role : Type u} [DecidableEq Role] [Finite Role]
    (game : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (assessment : (game.serialized order).information.BehavioralAssessment)
    (_consistent : assessment.IsSequentiallyConsistent
      (game.serial_decision_recall order).decisionInformationAntichain),
    ∀ (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role),
      assessment.belief i (game.serialSite order h ht i) =
        game.productBelief order assessment.strategy h ht i :=
  @KFOL.Results.round_product_beliefs

theorem scalar_parallel_laws : (∀ x : ℝ, 0*x/(0+x) = 0 ∧ x*0/(x+0) = 0) ∧
    (∀ x y : ℝ, x*y/(x+y) = y*x/(y+x)) ∧
    (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      (x*y/(x+y))*z/(x*y/(x+y)+z) = x*(y*z/(y+z))/(x+y*z/(y+z))) ∧
    (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → x ≤ y → x*z/(x+z) ≤ y*z/(y+z)) ∧
    (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      x*(min y z)/(x+min y z) = min (x*y/(x+y)) (x*z/(x+z)) ∧
      x*(max y z)/(x+max y z) = max (x*y/(x+y)) (x*z/(x+z))) :=
  @KFOL.Results.scalar_parallel_laws

theorem scalar_rational_values : ∀ {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (_hab : a ≠ b)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role),
    (∀ term : Rounds.Game.ScalarTerm,
      (term.game a b).sequentialValues order =
        {Rounds.Game.Scalar.distribution a b (term.rate:ℝ) term.rate_nonneg_real term.rate_le_one_real}) ∧
    ({q : ℚ | ∃ term : Rounds.Game.ScalarTerm, term.UnaryGenerated ∧ term.rate = q} = Set.Icc 0 1) ∧
    (∀ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1), ∃ term : Rounds.Game.ScalarTerm,
      term.UnaryGenerated ∧ (term.game a b).sequentialValues order =
        {Rounds.Game.Scalar.distribution a b (q:ℝ) (by exact_mod_cast h0) (by exact_mod_cast h1)}) :=
  @KFOL.Results.scalar_rational_values

theorem pair_game_boolean_full_abstraction : ∀ {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (left right : Rounds.Game Role) (_hleft : left.UsesOnly a b) (_hright : right.UsesOnly a b)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role),
    Countable {probe : Rounds.Game.ScalarTerm // probe.UnaryGenerated} ∧
    (left.sequentialValues order = right.sequentialValues order ↔
      ∀ context : Rounds.Game.Context Role, context.BooleanMenus →
        (c ∈ Rounds.Game.possibleWinners ((context.fill left).sequentialValues order) ↔
         c ∈ Rounds.Game.possibleWinners ((context.fill right).sequentialValues order))) ∧
    (left.sequentialValues order = right.sequentialValues order ↔
      ∀ context : Rounds.Game.Context Role, context.BooleanMenus →
        Rounds.Game.possibleWinners ((context.fill left).sequentialValues order) =
          Rounds.Game.possibleWinners ((context.fill right).sequentialValues order)) ∧
    (left.sequentialValues order = right.sequentialValues order ↔
      ∀ probe : Rounds.Game.ScalarTerm, probe.UnaryGenerated →
        (c ∈ Rounds.Game.possibleWinners
          ((Rounds.Game.publicChoice a left (probe.game a c)).sequentialValues order) ↔
         c ∈ Rounds.Game.possibleWinners
          ((Rounds.Game.publicChoice a right (probe.game a c)).sequentialValues order))) :=
  @KFOL.Results.pair_game_boolean_full_abstraction

theorem boolean_threshold_state_lower_bound : ∀ {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (N : ℕ) {Summary : Type v} [Fintype Summary] (code : Fin (N+1) → Summary)
    (_adequate : ∀ n k, code n = code k → ∀ m : Fin N,
      (c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.threshold a b c n.val (m.val+1)).sequentialValues order) ↔
       c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.threshold a b c k.val (m.val+1)).sequentialValues order))),
    Function.Injective code ∧ N+1 ≤ Fintype.card Summary :=
  @KFOL.Results.boolean_threshold_state_lower_bound

theorem scalar_rational_observation_order : ∀ {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (left right : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (_hleft : left.sequentialValues order = {Rounds.Game.Scalar.distribution a b x hx0 hx1})
    (_hright : right.sequentialValues order = {Rounds.Game.Scalar.distribution a b y hy0 hy1}),
    x ≤ y ↔ ∀ probe : Rounds.Game.ScalarTerm, probe.UnaryGenerated → probe.rate < 1 →
      (c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.publicChoice a right (probe.game a c)).sequentialValues order) →
       c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.publicChoice a left (probe.game a c)).sequentialValues order)) :=
  @KFOL.Results.scalar_rational_observation_order

open GameTheory GameTheory.Math.Probability Rounds.Game Rounds.Game.Scalar in
theorem scalar_diagonal_security : ∀ {Role : Type u} [DecidableEq Role] [Fintype Role] (a b : Role) (_hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (_hs : 0 < x+y),
    ∃ (row : PMF (Fin (binarySizes a b a+1)))
      (col : PMF (Fin (binarySizes a b b+1))),
      (row 0).toReal = y/(x+y) ∧
      (col 0).toReal = y/(x+y) ∧
      ∀ profile : (i : Role) → PMF (Fin (binarySizes a b i+1)),
        ((stageForm (binarySizes a b) (diagonalTable a b
          (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play
            (Profile.update (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
              profile a row) a).toReal = x*y/(x+y) ∧
        ((stageForm (binarySizes a b) (diagonalTable a b
          (distribution a b x hx0 hx1) (distribution a b y hy0 hy1))).mixed.play
            (Profile.update (sig := {Strategy := fun i => PMF (Fin (binarySizes a b i+1)),Outcome := Role})
              profile b col) a).toReal = x*y/(x+y) :=
  @KFOL.Results.scalar_diagonal_security

theorem public_choice_small_support : ∀ {Role : Type u} {Index : Type v}
    [Fintype Role] [Nontrivial Role] [Nonempty Index]
    (owner : Role) (branches : Index → Strategic.Tree Role),
    ∃ (S : Finset Index) (_ : S.Nonempty) (term : Term Role S),
      S.card ≤ Fintype.card Role - 1 ∧ term.IsCore ∧
      Strategic.possibleWinners (Strategic.compile (fun i : S => branches i.val) term) =
        Strategic.FiniteChoice.possibleWinners owner branches :=
  @KFOL.Results.public_choice_small_support

theorem public_choice_support_sharp : ∀ {Role : Type u} [Fintype Role] [DecidableEq Role]
    (owner : Role),
    Strategic.FiniteChoice.possibleWinners owner
      (fun i : {r : Role // r ≠ owner} => Strategic.Tree.leaf i.val) = {r | r ≠ owner} ∧
    ∀ (S : Finset Role) (_hS : S.Nonempty), owner ∉ S →
      Strategic.FiniteChoice.possibleWinners owner (fun i : S => Strategic.Tree.leaf i.val) =
        {r | r ≠ owner} →
      S = Finset.univ.erase owner ∧ S.card = Fintype.card Role - 1 :=
  @KFOL.Results.public_choice_support_sharp

theorem reset_circuit_exponential_tables : ∀ (n : ℕ),
    ∃ (equation : Circuit.Equation Reset.Symbol (Bool ⊕ (ℕ × Bool)))
      (term : Reset.Term (Bool ⊕ (ℕ × Bool))),
      equation.WellFormed ∧ equation.gates.length = 6*n+3 ∧
      Circuit.operationCount equation.gates = 4*n+1 ∧
      Circuit.edgeCount equation.gates = 8*n+2 ∧
      equation.unfold = some (term,term) ∧ 2^n ≤ (term.table (.inl true)).card :=
  @KFOL.Results.reset_circuit_exponential_tables

theorem reset_circuit_tree_succinctness : ∀ (n : ℕ),
    ∃ (equation : Circuit.Equation Reset.Symbol (Bool ⊕ (ℕ × Bool)))
      (term : Reset.Term (Bool ⊕ (ℕ × Bool))),
      equation.WellFormed ∧ equation.gates.length = 6*n+3 ∧
      equation.gates.countP (fun gate => match gate with | .input _ => true | .func _ _ => false) = 2*n+2 ∧
      Circuit.operationCount equation.gates = 4*n+1 ∧
      Circuit.edgeCount equation.gates = 8*n+2 ∧
      equation.unfold = some (term,term) ∧
      (term.table (.inl true)).card = 2^n ∧
      (∀ A ∈ term.table (.inl true), A.card = n+1) ∧
      term.occurrences (.inl true) = 2^n ∧
      ∀ (Role : Type u) (_three : Fin 3 ↪ Role) (other : Reset.Term (Bool ⊕ (ℕ × Bool))),
        (∀ valuation : (Bool ⊕ (ℕ × Bool)) → WinnerSet Role,
          other.eval valuation = term.eval valuation) →
        2^n ≤ other.occurrences (.inl true) ∧
          2^n+1 ≤ other.leafCount ∧ 2^(n+1)+1 ≤ other.size :=
  @KFOL.Results.reset_circuit_tree_succinctness

theorem well_founded_quantifier_fold {Role : Type u} [Fintype Role] [Nontrivial Role]
    (G : Strategic.QuantifiedTree.{u,v} Role) :
    ∃ (pruned : Strategic.QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Strategic.QuantifiedTree.Prunes (Fintype.card Role-1) G pruned),
      pruning.PreservesValues ∧ (∃ depth, Strategic.QuantifiedTree.DepthLE depth pruned) ∧
      Strategic.QuantifiedTree.Compiles pruned binary ∧
      Strategic.possibleWinners binary = Strategic.QuantifiedTree.possibleWinners G :=
  Results.Games.well_founded_quantifier_fold G

theorem serial_order_independence {Role : Type u} [Fintype Role] [DecidableEq Role]
    (G : Rounds.Game Role) (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    G.value = G.sequentialValues order :=
  Results.Games.value_eq_serial G order

theorem reset_circuit_reduction : ∀ {Role : Type u} (_three : Fin 3 ↪ Role)
    (formula : Reductions.CNF),
    (Circuit.ResetCNF.equation formula).WellFormed ∧
    (Circuit.ResetCNF.equation formula).gates.length =
      7 * (Reductions.ResetUnion.support formula).length + 2 * formula.flatten.length + 3 ∧
    Circuit.operationCount (Circuit.ResetCNF.equation formula).gates =
      5 * (Reductions.ResetUnion.support formula).length + 2 * formula.flatten.length + 1 ∧
    (let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
     (Circuit.ResetCNF.equation formula).Holds (WinnerSet Role) ↔ ¬Reductions.Satisfiable formula) :=
  @KFOL.Results.reset_circuit_reduction

theorem reset_circuit_generator : ∀ {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (equation : Circuit.Equation Reset.Symbol Var),
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    equation.Holds (WinnerSet Role) ↔ equation.WellFormed ∧
      ∀ valuation : Var → WinnerSet Role,
        (∀ j, ∃ stage : Fin 3, valuation j = Reset.chainValue three stage) →
        ∃ value, equation.eval valuation = some (value,value) :=
  @KFOL.Results.reset_circuit_generator

open Classical in
theorem arbitrary_public_quantifier : ∀ {Role : Type u}
    (owner : Role) (Action : Type v) (nonempty : Nonempty Action)
    (next : Action → Strategic.QuantifiedTree.{u,v} Role),
    Strategic.QuantifiedTree.possibleWinners (.node owner Action nonempty next) =
      if ∃ a, Strategic.QuantifiedTree.possibleWinners (next a) = {owner} then {owner}
      else {player | ∃ a, player ∈ Strategic.QuantifiedTree.possibleWinners (next a)} :=
  @KFOL.Results.arbitrary_public_quantifier

theorem reset_table_size {Var : Type v} [DecidableEq Var] (t : Reset.Term Var) :
    (∀ j, (t.table j).card ≤ t.occurrences j) ∧
    (∑ j ∈ t.varFinset, (t.table j).card) ≤ t.leafCount ∧
    t.size + 1 = 2 * t.leafCount :=
  Results.Algebra.reset_table_size t

theorem two_player_forcing_coordinates : ∀ {Role : Type u} (labels : Fin 2 ≃ Role),
    Function.Injective (TwoPlayers.forcingCoordinates labels) ∧
    (∀ A B : WinnerSet Role,
      TwoPlayers.forcingCoordinates labels (WinnerSet.choice (labels 0) A B) =
        ((TwoPlayers.forcingCoordinates labels A).1 || (TwoPlayers.forcingCoordinates labels B).1,
         (TwoPlayers.forcingCoordinates labels A).2 && (TwoPlayers.forcingCoordinates labels B).2)) ∧
    (∀ A B : WinnerSet Role,
      TwoPlayers.forcingCoordinates labels (WinnerSet.choice (labels 1) A B) =
        ((TwoPlayers.forcingCoordinates labels A).1 && (TwoPlayers.forcingCoordinates labels B).1,
         (TwoPlayers.forcingCoordinates labels A).2 || (TwoPlayers.forcingCoordinates labels B).2)) ∧
    (∀ A : WinnerSet Role,
      TwoPlayers.forcingCoordinates labels (WinnerSet.rename (Equiv.swap (labels 0) (labels 1)) A) =
        ((TwoPlayers.forcingCoordinates labels A).2,(TwoPlayers.forcingCoordinates labels A).1)) ∧
    (∀ p : Bool × Bool, (∃ A, TwoPlayers.forcingCoordinates labels A = p) ↔
      ¬(p.1 = true ∧ p.2 = true)) :=
  @KFOL.Results.two_player_forcing_coordinates

/-! ## Guarded navigation queries and their expressive boundaries -/

theorem public_query_compilation {Role : Type u} {Var : Type v} [DecidableEq Role]
    (t : Term Role Var) (ht : t.IsPublic) :
    (∀ (valuation : Var → WinnerSet Role) (node : Query.Node valuation),
      (Query.compile t ht).Holds (Query.document valuation) .root node ↔
        ∃ r ∈ (t.eval valuation).val, node = .role r) ∧
    (Query.compile t ht).size ≤ 12 * t.size ^ 2 :=
  Query.public_compilation t ht

theorem public_query_equivalence {Role : Type u} {Var : Type v} [DecidableEq Role]
    (s t : Term Role Var) (hs : s.IsPublic) (ht : t.IsPublic) :
    (∀ (valuation : Var → WinnerSet Role) (node : Query.Node valuation),
      (Query.compile s hs).Holds (Query.document valuation) .root node ↔
        (Query.compile t ht).Holds (Query.document valuation) .root node) ↔ s.Equivalent t :=
  Query.compile_equivalence s t hs ht

theorem finite_powerset_relational_representation {α : Type u} [Finite α] (mul : Set α → Set α → Set α)
    (assoc : ∀ A B C, mul (mul A B) C = mul A (mul B C))
    (add_left : ∀ A B C, mul (A ∪ B) C = mul A C ∪ mul B C)
    (add_right : ∀ A B C, mul A (B ∪ C) = mul A B ∪ mul A C)
    (zero_left : ∀ A, mul ∅ A = ∅) (zero_right : ∀ A, mul A ∅ = ∅) :
    Function.Injective (Relational.regularRelation mul) ∧
    Relational.regularRelation mul ∅ = (fun _ _ => False) ∧
    (∀ A B, Relational.regularRelation mul (A ∪ B) = fun x y =>
      Relational.regularRelation mul A x y ∨ Relational.regularRelation mul B x y) ∧
    ∀ A B, Relational.regularRelation mul (mul A B) =
      Relation.Comp (Relational.regularRelation mul A) (Relational.regularRelation mul B) :=
  Relational.finite_powerset_representation mul assoc add_left add_right zero_left zero_right

theorem owned_choice_zero_extension {Role : Type u} (owner : Role) :
    (∀ A B : WinnerSet Role, choiceWithZero owner A.val B.val = (choice owner A B).val) ∧
    (∀ A B C, choiceWithZero owner (choiceWithZero owner A B) C =
      choiceWithZero owner A (choiceWithZero owner B C)) ∧
    (∀ A B, choiceWithZero owner A B = choiceWithZero owner B A) ∧
    (∀ A, choiceWithZero owner A A = A) ∧
    (∀ A B C, choiceWithZero owner (A ∪ B) C =
      choiceWithZero owner A C ∪ choiceWithZero owner B C) ∧
    (∀ A B C, choiceWithZero owner A (B ∪ C) =
      choiceWithZero owner A B ∪ choiceWithZero owner A C) ∧
    (∀ A, choiceWithZero owner ∅ A = ∅) ∧
    ∀ A, choiceWithZero owner A ∅ = ∅ :=
  WinnerSet.choiceWithZero_laws owner

theorem owned_choice_zero_representation {Role : Type u} (owner : Role) :
    Function.Injective (Relational.regularRelation (choiceWithZero owner)) ∧
    Relational.regularRelation (choiceWithZero owner) ∅ = (fun _ _ => False) ∧
    (∀ A B, Relational.regularRelation (choiceWithZero owner) (A ∪ B) = fun x y =>
      Relational.regularRelation (choiceWithZero owner) A x y ∨
      Relational.regularRelation (choiceWithZero owner) B x y) ∧
    ∀ A B, Relational.regularRelation (choiceWithZero owner) (choiceWithZero owner A B) =
      Relation.Comp (Relational.regularRelation (choiceWithZero owner) A)
        (Relational.regularRelation (choiceWithZero owner) B) :=
  WinnerSet.choiceWithZero_representation owner

theorem owned_choice_relational_representation {Role : Type u} (owner : Role) :
    Function.Injective (Query.relation owner) ∧
    (∀ A B : WinnerSet Role, Query.relation owner (A.union B) =
      fun x y => Query.relation owner A x y ∨ Query.relation owner B x y) ∧
    ∀ A B : WinnerSet Role, Query.relation owner (WinnerSet.choice owner A B) =
      Relation.Comp (Query.relation owner A) (Query.relation owner B) :=
  Query.relational_representation owner

theorem reset_no_relational_representation {Role : Type u}
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (Node : Type v) :
    ¬∃ encode : WinnerSet Role → Node → Node → Prop, Function.Injective encode ∧
      (∀ A B, encode (A.union B) = fun x y => encode A x y ∨ encode B x y) ∧
      ∀ A B, encode (A.reset B) = Relation.Comp (encode A) (encode B) :=
  Query.no_reset_relational_representation a b c hab hac hbc Node

theorem intersection_not_definable {Role : Type u} (three : Fin 3 ↪ Role) :
    ¬∃ t : Term Role (Fin 2), ∀ valuation : Fin 2 → WinnerSet Role,
      ((valuation 0).val ∩ (valuation 1).val).Nonempty →
        (t.eval valuation).val = (valuation 0).val ∩ (valuation 1).val :=
  Query.no_intersection three

theorem expanded_variety_envelope {Role : Type u} (three : Fin 3 ↪ Role) (M : Type v)
    [(Equational.language (Equational.CoreSymbol Role)).Structure M] [Nonempty M] :
    let _ := Equational.coreStructure Role
    let _ := Equational.publicStructure Role
    let _ := Equational.fullStructure Role
    let _ := Envelope.structureOf (Role := Role) (M := M)
    let _ := Envelope.publicStructureOf (Role := Role) (M := M)
    (Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M ↔
      Equational.InVariety (Equational.PublicSymbol Role) (WinnerSet Role) (Envelope.Carrier Role M)) ∧
    (Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M ↔
      Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) (Envelope.Carrier Role M)) :=
  Results.Algebra.expanded_variety_envelope three M

theorem permutation_envelope_cardinality {Role : Type u} [DecidableEq Role] [Fintype Role]
    (M : Type v) [Fintype M] :
    Fintype.card (Envelope.Carrier Role M) =
      1 + (Fintype.card Role).factorial * Fintype.card M :=
  Results.Algebra.permutation_envelope_cardinality M

/-! ## Sealed rounds: distribution sets and the scalar fragment -/

open Rounds.Game in
theorem public_nonidempotence {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    midpointLaw (PMF.pure a) (PMF.pure c) ∉ (Public.nonconvexTree a b c).value ∧
    midpointLaw (PMF.pure a) (PMF.pure c) ∈
      (publicChoice b (Public.nonconvexTree a b c) (Public.nonconvexTree a b c)).value :=
  Results.Games.public_nonidempotence a b c hab hac hbc

open Rounds.Game in
theorem constant_sum_value {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (hab : a ≠ b) (G : Rounds.Game Role) (uses : G.UsesOnly a b) :
    ∃ x : ℝ, G.HasScalarValue a b x :=
  Results.Games.constant_sum_value a b hab G uses

open Rounds.Game in
theorem scalar_diagonal_values {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (hab : a ≠ b) (G H : Rounds.Game Role) (x y : ℝ)
    (hx : G.HasScalarValue a b x) (hy : H.HasScalarValue a b y) :
    (diagonal a b G H).HasScalarValue a b (Scalar.parallel x y) :=
  Results.Games.diagonal_value a b hab G H x y hx hy

open Rounds.Game in
theorem reciprocal_values {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (hab : a ≠ b) (n : ℕ) :
    (reciprocal a b n).HasScalarValue a b (1/((n:ℝ)+1)) :=
  Results.Games.reciprocal_values a b hab n

open Rounds.Game in
theorem scalar_contextual_equivalence {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (G H : ScalarTerm) :
    (G.rate = H.rate ↔ SameContextualWinners (G.game a b) (H.game a b)) ∧
    (G.rate = H.rate ↔ ContextuallyEquivalent c (G.game a b) (H.game a b)) :=
  Results.Games.scalar_full_abstraction a b c hab hac hbc G H

end KFOL.Report

#audit_namespace KFOL.Report
