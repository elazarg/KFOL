module

public import KFOL.Results.Certificates
public import KFOL.Results.Algebra
public import KFOL.Results.Games
public import KFOL.Definitions.PaperGames
public import KFOL.Query.Compilation
public import KFOL.Query.Relations
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

end KFOL.Report

#audit_namespace KFOL.Report
