module

public import KFOL.Results.Certificates
public import KFOL.Results.Algebra
public import KFOL.Results.Games
public import KFOL.Definitions.PaperGames
public import KFOL.Query.Compilation
public import KFOL.Query.Relations
public import KFOL.Query.ZeroExtension
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

theorem core_source_reconstruction {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (t : Term Role Var) (ht : t.IsCore)
    (v : Var → WinnerSet Role) (k : Role) :
    k ∈ (t.eval v).val ↔ ∃ j, k ∈ (v j).val ∧
      k ∈ (t.eval (Core.Sources.probe three k j (Core.Sources.pattern k j v))).val :=
  Results.Algebra.core_source_reconstruction three t ht v k

theorem core_prime_guard_normal_form {Role : Type u} [Fintype Role]
    {Var : Type v} [Fintype Var] (three : Fin 3 ↪ Role)
    (t : Term Role Var) (ht : t.IsCore) (v : Var → WinnerSet Role) :
    (Core.Sources.meaning (Core.Sources.normalForm three (fun w => t.eval w)) v =
      (t.eval v).val) ∧ ∀ k j, IsAntichain (· ≤ ·)
        (Core.Sources.normalForm three (fun w => t.eval w) k j :
          Set (Core.Sources.Guard k j)) :=
  Results.Algebra.core_prime_guard_normal_form three t ht v

theorem core_prime_guard_equality {Role : Type u} [Fintype Role]
    {Var : Type v} [Fintype Var] (three : Fin 3 ↪ Role)
    (s t : Term Role Var) (hs : s.IsCore) (ht : t.IsCore) :
    Core.Sources.normalForm three (fun v => s.eval v) =
      Core.Sources.normalForm three (fun v => t.eval v) ↔ ∀ v, s.eval v = t.eval v :=
  Results.Algebra.core_prime_guard_equality three s t hs ht

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

theorem core_singleton_profiles {Role : Type u} [DecidableEq Role] [Fintype Role]
    {Var : Type v} [Fintype Var] (three : Fin 3 ↪ Role)
    (F : Role → (Var → Bool) → Bool) :
    (∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      ∀ i v, Core.profile i v t = F i v) ↔ Core.AdmissibleProfiles F :=
  Results.Algebra.core_singleton_profiles three F

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

theorem core_cut_synthesis {Role : Type u} {Var : Type v} {Row : Type w}
    [Fintype Role] [Fintype Row] [Nonempty Row] (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ i, t.eval (values i) = U i) ↔
      Core.Cuts.Recognizes values U :=
  Results.Algebra.core_cut_synthesis three values U

theorem core_cut_maximum {Role : Type u} {Var : Type v} {Row : Type w}
    [Fintype Role] [Fintype Row] (three : Fin 3 ↪ Role)
    (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role)
    (B : Core.Cuts.State Role Row)
    (h : ∃ i r, (⟨B, i, r⟩ : Core.Cuts.Fact Role Row) ∈
      FiniteHorn.saturate (Core.Cuts.system values U)) :
    ∃ t : Term Role Var, t.IsCore ∧
      (∀ i, (t.eval (values i)).val ⊆ Core.Cuts.region U B i) ∧
      ∀ i r, r ∈ (t.eval (values i)).val ↔ (⟨B, i, r⟩ : Core.Cuts.Fact Role Row) ∈
        FiniteHorn.saturate (Core.Cuts.system values U) :=
  Results.Algebra.core_cut_maximum three values U B h

theorem core_cut_round_bound {Role : Type u} {Var : Type v} {Row : Type w}
    [Fintype Role] [Fintype Row]
    (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role) :
    let N := Fintype.card Role * Fintype.card Row *
      (Fintype.card Role + 2) ^ Fintype.card Row
    FiniteHorn.step (Core.Cuts.system values U)
      (FiniteHorn.stage (Core.Cuts.system values U) N) =
        FiniteHorn.stage (Core.Cuts.system values U) N :=
  Results.Algebra.core_cut_round_bound values U

theorem core_cut_recognition {Role : Type u} {Var : Type v}
    [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v) ↔ Core.CutRecognizes f :=
  Results.Algebra.core_cut_recognition three f

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
