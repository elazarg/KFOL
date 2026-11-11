module

public import KFOL.Results.Algebra
public import KFOL.Results.Complexity
public import KFOL.Results.Games
public import KFOL.Audit.Namespace

/-! # Claims of the main paper and the report results it cites

Mathematical vocabulary starts in `KFOL/Definitions/PaperAlgebra`, `PaperGames`
and `Complexity`, alongside their underlying definitions. Report.lean contains
report-only results; implementation contracts remain in the library.
-/

@[expose] public section
namespace KFOL.Paper
universe u v w
variable {Role : Type u} {Var : Type v}

/-! ## Public games -/

/-- `game:thm:adequacy`. -/
theorem public_backward_induction :
    (∀ G : Strategic.Tree Role, ∃ p : Strategic.Profile G, Strategic.IsSubgamePerfect p) ∧
    (∀ r : Role, Strategic.value (.leaf r) = WinnerSet.singleton r) ∧
    (∀ (r : Role) (G H : Strategic.Tree Role),
      Strategic.value (.node r G H) = WinnerSet.choice r (Strategic.value G) (Strategic.value H)) :=
  Results.public_backward_induction

theorem public_realizability [Finite Role] (three : Fin 3 ↪ Role) (A : WinnerSet Role) :
    ∃ G : Strategic.Tree Role, Strategic.value G = A :=
  Results.Games.public_realizability three A

theorem public_forcing (G : Strategic.Tree Role) (r : Role) :
    Strategic.CanForce G r ↔ Strategic.value G = WinnerSet.singleton r :=
  Results.public_forcing G r

theorem quantifier_fold {G : Strategic.QuantifiedTree.{u,v} Role} {binary : Strategic.Tree Role}
    (compiled : Strategic.QuantifiedTree.Compiles G binary) :
    Strategic.possibleWinners binary = Strategic.QuantifiedTree.possibleWinners G :=
  Strategic.QuantifiedTree.Compiles.possibleWinners_eq compiled

theorem finite_depth_quantifier_reduction [Fintype Role] [Nontrivial Role]
    (depth : ℕ) (G : Strategic.QuantifiedTree.{u,v} Role)
    (bounded : Strategic.QuantifiedTree.DepthLE depth G) :
    (∃ p : Strategic.QuantifiedTree.Profile G, Strategic.QuantifiedTree.IsSubgamePerfect p) ∧
    ∃ (pruned : Strategic.QuantifiedTree.{u,v} Role) (binary : Strategic.Tree Role)
      (pruning : Strategic.QuantifiedTree.Prunes (Fintype.card Role-1) G pruned),
      pruning.PreservesValues ∧ Strategic.QuantifiedTree.DepthLE depth pruned ∧
      Strategic.QuantifiedTree.Compiles pruned binary ∧
      Strategic.possibleWinners binary = Strategic.QuantifiedTree.possibleWinners G :=
  Results.Games.finite_depth_quantifier_fold depth G bounded

/-! ## Winner algebras, reset and guarded choice -/

/-- `game:thm:union`. -/
theorem neutral_union (r s t : Role) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (A B : WinnerSet Role) :
    WinnerSet.choice t (WinnerSet.choice r A B) (WinnerSet.choice s A B) = A.union B :=
  Results.Algebra.neutral_union r s t hrs hrt hst A B

theorem owned_choice_semilattices (r : Role) :
    ∃ s : SemilatticeSup (WinnerSet Role),
      (∀ A B, @Max.max _ s.toMax A B = WinnerSet.choice r A B) ∧
      (∀ A B, @LE.le _ s.toLE A B ↔
        B = WinnerSet.singleton r ∨ (A ≠ WinnerSet.singleton r ∧ A.val ⊆ B.val)) :=
  Results.Algebra.owned_choice_semilattices r

theorem no_boolean_product (three : Fin 3 ↪ Role) {Index : Type w}
    (M : Index → Type v) [∀ i, BooleanAlgebra (M i)] (select : Role → Index → Bool) :
    ¬∃ f : WinnerSet Role → ∀ i, M i, Function.Injective f ∧ ∀ r A B i,
      f (WinnerSet.choice r A B) i = if select r i then f A i ⊔ f B i else f A i ⊓ f B i :=
  Results.Algebra.no_boolean_product three M select

/-- `view:thm:view`. -/
theorem player_views [Fintype Role] (three : Fin 3 ↪ Role) (k : Role) :
    (∀ A B : WinnerSet Role, A.ObservationallyEquivalent k B ↔ A.SameView k B) ∧
    (∀ A B : WinnerSet Role, WinnerSet.view k A = WinnerSet.view k B ↔ A.SameView k B) ∧
    Function.Surjective (WinnerSet.view k) ∧
    Nat.card (Quotient (Setoid.ker (WinnerSet.view k))) = Fintype.card Role + 1 :=
  Results.Algebra.player_views three k

theorem public_subdirect_representation [Fintype Role] (three : Fin 3 ↪ Role) :
    Nat.card (WinnerSet Role) = 2 ^ Fintype.card Role - 1 ∧
    Function.Injective (fun A : WinnerSet Role => fun k => WinnerSet.view k A) ∧
    (∀ k : Role, Function.Surjective (WinnerSet.view k) ∧ Nat.card (PlayerView k) = Fintype.card Role + 1) ∧
    ∀ (t : Term Role Var), t.IsPublic → ∀ k valuation,
      WinnerSet.view k (t.eval valuation) = PlayerView.eval three k t (fun x => WinnerSet.view k (valuation x)) :=
  Results.Algebra.public_subdirect_representation three

theorem player_view_orders (three : Fin 3 ↪ Role) (k r : Role) :
    (∀ A B : WinnerSet Role, WinnerSet.view k (WinnerSet.choice r A B) =
      PlayerView.choice r (WinnerSet.view k A) (WinnerSet.view k B)) ∧
    ∃ order : SemilatticeSup (PlayerView k), let _ := order
      (∀ p q : PlayerView k, p ⊔ q = PlayerView.choice r p q) ∧
      ∀ p q : PlayerView k, p ≤ q ↔ PlayerView.Below r p q :=
  Results.Algebra.player_view_orders three k r

theorem unique_winner_observations (t : Term Role Var) (ht : t.IsPublic) (active : Var → Bool) (parameters : Var → WinnerSet Role) :
    ((∃ C : WinnerSet Role, ∀ X : WinnerSet Role,
      t.eval (fun x => if active x then X else parameters x) = C) ∨
      ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun x => if active x then X else parameters x)).val) ∧
    ∀ A B : WinnerSet Role, A.Ambiguous → B.Ambiguous → ∀ r,
      (t.eval (fun x => if active x then A else parameters x) = WinnerSet.singleton r) ↔
        (t.eval (fun x => if active x then B else parameters x) = WinnerSet.singleton r) :=
  Results.Algebra.unique_winner_observations t ht active parameters

theorem switching_observation (k : Role) (A B : WinnerSet Role) :
    (∀ n (t : Term Role (Option (Fin n))) (parameters : Fin n → WinnerSet Role),
      k ∈ (t.eval (fun x => x.elim A parameters)).val ↔
        k ∈ (t.eval (fun x => x.elim B parameters)).val) ↔ A = B :=
  Results.Algebra.switching_observation k A B

theorem congruence_classification [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role) :
    (∀ θ : WinnerSet.Congruence Role, ∃! c : ClosureOperator (WinnerSet Role),
      WinnerSet.AtomClosure c ∧ ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ c : ClosureOperator (WinnerSet Role), WinnerSet.AtomClosure c →
      ∃ θ : WinnerSet.Congruence Role, ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ θ : WinnerSet.Congruence Role, ∃! F : Set (WinnerSet Role), WinnerSet.AdmissibleFamily F ∧
      ∀ A B, θ.r A B ↔ WinnerSet.familyClosureValue F A = WinnerSet.familyClosureValue F B) ∧
    (∀ F : Set (WinnerSet Role), WinnerSet.AdmissibleFamily F → ∃ θ : WinnerSet.Congruence Role,
      ∀ A B, θ.r A B ↔ WinnerSet.familyClosureValue F A = WinnerSet.familyClosureValue F B) :=
  Results.Algebra.congruence_classification three

theorem symmetric_congruence_chain [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role) :
    (∀ θ : WinnerSet.SymmetricCongruence Role, ∃! m : Fin (Nat.card Role),
      ∀ A B, θ.r A B ↔ WinnerSet.threshold m.val A = WinnerSet.threshold m.val B) ∧
    (∀ m : Fin (Nat.card Role), ∃ θ : WinnerSet.SymmetricCongruence Role,
      ∀ A B, θ.r A B ↔ WinnerSet.threshold m.val A = WinnerSet.threshold m.val B) ∧
    Nat.card (WinnerSet.SymmetricCongruence Role) = Nat.card Role ∧
    (∀ m n : ℕ, m ≤ n → ∀ A B : WinnerSet Role,
      WinnerSet.threshold n A = WinnerSet.threshold n B → WinnerSet.threshold m A = WinnerSet.threshold m B) ∧
    (∀ A : WinnerSet Role, WinnerSet.threshold 0 A = WinnerSet.full) ∧
    (∀ A : WinnerSet Role, WinnerSet.threshold (Nat.card Role - 1) A = A) ∧
    ∀ m < Nat.card Role, Nat.card (Quotient (Setoid.ker (WinnerSet.threshold (Role := Role) m))) =
      1 + ∑ j ∈ Finset.Icc 1 m, (Nat.card Role).choose j :=
  Results.Algebra.symmetric_congruence_chain three

theorem uniform_matroid_identification [Finite Role] [Nonempty Role] (m : ℕ) (hm : m < Nat.card Role) :
    ∃ M : Matroid Role, M.E = Set.univ ∧
      (∀ I : Set Role, M.Indep I ↔ I.ncard ≤ m+1) ∧ M.eRank = (m+1 : ℕ) ∧
      ∀ A : WinnerSet Role, (WinnerSet.threshold m A).val = M.closure A.val :=
  Results.uniform_matroid_identification m hm

/-- `sym:lem:provenance`. -/
theorem status_cell_provenance (t : Term Role Var) (base : Var → WinnerSet Role) :
    ∃ (C : Set Role) (P : Var → Finset (Equiv.Perm Role)), C.Finite ∧
      (∀ j, ∀ p ∈ P j, (base j).Ambiguous) ∧ ∀ valuation : Var → WinnerSet Role,
        (∀ j r, base j = WinnerSet.singleton r ↔ valuation j = WinnerSet.singleton r) →
        (t.eval valuation).val = C ∪ ⋃ j, ⋃ p ∈ P j, p '' (valuation j).val :=
  Results.Algebra.status_cell_provenance t base

/-- `sym:thm:pairs`. -/
theorem pair_countervaluations (s t : Term Role Var) (failure : ¬s.Equivalent t) :
    ∃ valuation : Var → WinnerSet Role,
      (∀ x, ∃ a b : Role, (valuation x).val = {a,b}) ∧ s.eval valuation ≠ t.eval valuation :=
  Results.Algebra.pair_countervaluations s t failure

theorem optimal_test_domain [Fintype Role] (three : Fin 3 ↪ Role) :
    (∀ D : Set (WinnerSet Role), CompleteTestDomain D ↔
      ∀ a b, (WinnerSet.singleton a).union (WinnerSet.singleton b) ∈ D) ∧
    IsLeast {D : Set (WinnerSet Role) | CompleteTestDomain D} {A | ∃ a b : Role, A.val = {a,b}} ∧
    Nat.card {A : WinnerSet Role // ∃ a b : Role, A.val = {a,b}} =
      Fintype.card Role * (Fintype.card Role + 1) / 2 :=
  Results.Algebra.optimal_test_domain three

theorem reduct_test_domains [Fintype Role] (three : Fin 3 ↪ Role) (D : Set (WinnerSet Role)) :
    CompletePublicTestDomain D ↔ (∀ r, WinnerSet.singleton r ∈ D) ∧
      ∀ k, ∃ A ∈ D, A.Ambiguous ∧ k ∉ A.val :=
  Results.Algebra.reduct_test_domains three D

theorem minimum_reduct_test_domain [Fintype Role] (three : Fin 3 ↪ Role) :
    IsLeast {m : ℕ | ∃ D : Finset (WinnerSet Role), CompletePublicTestDomain (D : Set (WinnerSet Role)) ∧ D.card = m}
      (if Fintype.card Role = 3 then 6 else Fintype.card Role + 2) :=
  Results.Algebra.minimum_reduct_test_domain three

/-- `gen:thm:core`. -/
theorem idempotent_elimination (three : Fin 3 ↪ Role) (t : Term Role Var) :
    (t.Idempotent ↔ ¬t.HasWinner ∧ ∀ x p, (x,p) ∈ t.inputOccurrences → p = 1) ∧
    (t.Idempotent ↔ ∃ c : Term Role Var, c.IsCore ∧ c.Equivalent t) :=
  Results.Algebra.idempotent_elimination three t

theorem intrinsic_player_views [Fintype Role] (three : Fin 3 ↪ Role) :
    (∀ t : Term Role Var, t.Idempotent → ∀ k valuation,
      WinnerSet.view k (t.eval valuation) = PlayerView.eval three k t (fun x => WinnerSet.view k (valuation x))) ∧
    Function.Injective (fun A : WinnerSet Role => fun k => WinnerSet.view k A) ∧
    (∀ k : Role, Function.Surjective (WinnerSet.view k) ∧ Nat.card (PlayerView k) = Fintype.card Role + 1) ∧
    ∀ k, ∃ A B : WinnerSet Role, A ≠ B ∧
      (∀ j, j ≠ k → WinnerSet.view j A = WinnerSet.view j B) ∧ WinnerSet.view k A ≠ WinnerSet.view k B :=
  Results.Algebra.intrinsic_player_views three

theorem semilattice_trace (three : Fin 3 ↪ Role) :
    (∀ n (t : Term Role (Fin n)), t.Idempotent → ∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ valuation : Fin n → WinnerSet Role, (∀ x, (valuation x).Ambiguous) →
        ∀ r, r ∈ (t.eval valuation).val ↔ ∃ x ∈ S, r ∈ (valuation x).val) ∧
    (∀ n, 0 < n → ∀ t : Term Role (Fin n),
      ¬∀ A B : WinnerSet Role, ∀ i, t.eval (Function.update (fun _ => A) i B) = A) ∧
    (∀ t : Term Role (Fin 3), ¬((∀ A B : WinnerSet Role, t.eval (fun i => if i = 0 then A else B) = A) ∧
      (∀ A B : WinnerSet Role, t.eval (fun i => if i = 2 then B else A) = B))) ∧
    ∀ n (s t : Term Role (Fin n)), s.IsCore → t.IsCore → s.Equivalent t → s.vars = t.vars :=
  Results.Algebra.semilattice_trace three

/-- `gen:thm:source`. -/
theorem common_source {Index : Type w} (t : Term Role Var) (valuation : Index → Var → WinnerSet Role)
    (regions : Index → Set Role) (hd : Pairwise fun i j => Disjoint (regions i) (regions j))
    (hf : ∀ i, (t.eval (valuation i)).val ⊆ regions i) :
    ∃ (leaf : Role ⊕ Var) (p : Equiv.Perm Role), (leaf,p) ∈ t.sourceOccurrences ∧
      (∀ i, (WinnerSet.rename p (leaf.elim WinnerSet.singleton (valuation i))).val ⊆ regions i) ∧
      ((∃ i j : Index, i ≠ j) → ∃ x, leaf = .inr x ∧ (x,p) ∈ t.inputOccurrences) :=
  Results.Algebra.common_source t valuation regions hd hf

theorem atomic_repeated_triples (t : Term Role Var) (valuation : Fin 3 → Var → Role)
    (hrepeat : ∀ x, Atomic.Repeat (valuation 0 x) (valuation 1 x) (valuation 2 x))
    (out : Fin 3 → Role)
    (heval : ∀ i, t.eval (fun x => WinnerSet.singleton (valuation i x)) = WinnerSet.singleton (out i)) :
    Atomic.Repeat (out 0) (out 1) (out 2) :=
  Results.Algebra.atomic_repeated_triples t valuation hrepeat out heval

theorem no_atomic_if_then_else (three : Fin 3 ↪ Role) (a b : Role) (hab : a ≠ b) (t : Term Role (Fin 3)) :
    ¬((∀ y z : Role, t.eval (fun i => WinnerSet.singleton (if i = 0 then a else if i = 1 then y else z)) = WinnerSet.singleton y) ∧
      (∀ y z : Role, t.eval (fun i => WinnerSet.singleton (if i = 0 then b else if i = 1 then y else z)) = WinnerSet.singleton z)) :=
  Results.Algebra.no_atomic_if_then_else three a b hab t

theorem atomic_functions [Finite Role] (three : Fin 3 ↪ Role) [Finite Var] (f : (Var → Role) → Role) :
    (∃ t : Term Role Var, t.AtomicRealizes f) ↔ Atomic.EssentiallyUnary f ∨ Atomic.AtMostTwo f :=
  Results.Algebra.atomic_functions three f

/-- `gen:cor:determinacy`. -/
theorem determinacy (three : Fin 3 ↪ Role) [Finite Var] (t : Term Role Var)
    (ha : t.AtomPreserving) (hd : t.Idempotent) :
    ∃ i : Var, ∀ x : Var → Role, t.eval (fun j => WinnerSet.singleton (x j)) = WinnerSet.singleton (x i) :=
  Results.Algebra.determinacy three t ha hd

/-- `reset:thm:binary`. -/
theorem binary_atom_preserving_iff [Finite Role] (three : Fin 3 ↪ Role) (f : (Fin 2 → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role (Fin 2), t.IsCore ∧ t.AtomPreserving ∧ t.Idempotent ∧ ∀ v, t.eval v = f v) ↔
      (∀ v, f v = v 0) ∨ (∀ v, f v = v 1) ∨
      (∀ v, f v = (v 0).reset (v 1)) ∨ (∀ v, f v = (v 1).reset (v 0)) :=
  Results.Algebra.binary_atom_preserving_iff three f

theorem one_constant_rigidity (t : Term Role Var) (ht : t.IsCore) (active : Var → Bool) (r : Role) :
    ((∀ X : WinnerSet Role, t.eval (fun x => if active x then X else WinnerSet.singleton r) = WinnerSet.singleton r) ∨
      ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun x => if active x then X else WinnerSet.singleton r)).val) ∧
    ∀ q, q ≠ r → t.eval (fun x => if active x then WinnerSet.singleton q else WinnerSet.singleton r) = WinnerSet.singleton r →
      ∀ X : WinnerSet Role, t.eval (fun x => if active x then X else WinnerSet.singleton r) = WinnerSet.singleton r :=
  Results.Algebra.one_constant_rigidity t ht active r

theorem reset_definability [Finite Role] (three : Fin 3 ↪ Role) :
    ∃ t : Term Role (Fin 2), t.IsCore ∧
      ∀ valuation : Fin 2 → WinnerSet Role, t.eval valuation = (valuation 0).reset (valuation 1) :=
  Results.Algebra.reset_definability three

theorem owner_definability (a : Role) :
    (∀ X Y Z : WinnerSet Role, WinnerSet.guardedChoice a X Y Z = (WinnerSet.choice a Y Z).reset X) ∧
    (∀ X : WinnerSet Role, WinnerSet.guardedChoice a X X X = X) ∧
    ∀ i (Y Z : WinnerSet Role), WinnerSet.guardedChoice a (WinnerSet.singleton i) Y Z = WinnerSet.singleton i :=
  Results.Algebra.owner_definability a

theorem guarded_choice_example (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c ∉ (WinnerSet.guardedChoice a ((WinnerSet.singleton a).union (WinnerSet.singleton b))
      (WinnerSet.singleton a) (WinnerSet.singleton c)).val ∧
    c ∈ (WinnerSet.guardedChoice a ((WinnerSet.singleton a).union (WinnerSet.singleton b))
      (WinnerSet.singleton b) (WinnerSet.singleton c)).val :=
  Results.Algebra.guarded_choice_example a b c hab hac hbc

theorem reset_selection (t : Reset.Term Var) (valuation : Var → WinnerSet Role) :
    ((t.eval valuation).Ambiguous ↔ (valuation t.root).Ambiguous) ∧
    ∀ r, r ∈ (t.eval valuation).val ↔
      ∃ j, t.Selected {i | (valuation i).Ambiguous} j ∧ r ∈ (valuation j).val :=
  Results.Algebra.reset_selection t valuation

theorem reset_table_semantic_definition [DecidableEq Var] (three : Fin 3 ↪ Role) (t : Reset.Term Var) :
    (∀ valuation : Var → WinnerSet Role, ∀ r, r ∈ (t.eval valuation).val ↔
      ∃ j, ∃ A ∈ t.table j, (∀ k ∈ A, (valuation k).Ambiguous) ∧ r ∈ (valuation j).val) ∧
    ∀ j (A : Finset Var), A ∈ t.table j ↔
      three 2 ∈ (t.eval (Reset.markerValuation three j A)).val ∧
      ∀ B ⊆ A, three 2 ∈ (t.eval (Reset.markerValuation three j B)).val → A ⊆ B :=
  Results.Algebra.reset_table_semantic_definition three t

/-- `reset:thm:three`. -/
theorem reset_tables_semantics [DecidableEq Var] (three : Fin 3 ↪ Role) (s t : Reset.Term Var) :
    (s.Equivalent Role t ↔ s.table = t.table) ∧
    (s.Equivalent Role t ↔ ∀ valuation : Var → WinnerSet Role,
      (∀ i, ∃ k : Fin 3, valuation i = Reset.chainValue three k) → s.eval valuation = t.eval valuation) ∧
    ∀ {Role' : Type w} (_three' : Fin 3 ↪ Role'), s.Equivalent Role t ↔ s.Equivalent Role' t :=
  Results.Algebra.reset_tables_semantics three s t

theorem reset_minimum_generator (three : Fin 3 ↪ Role) :
    letI := Reset.structureOf (WinnerSet.reset (Role := Role))
    letI := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    (∀ e : Equational.Identity Reset.Symbol, e.Holds (WinnerSet Role) ↔ e.Holds (Fin 3)) ∧
    ∀ (M : Type v) [Fintype M] [(Equational.language Reset.Symbol).Structure M],
      (∀ e : Equational.Identity Reset.Symbol, e.Holds (WinnerSet Role) ↔ e.Holds M) → 3 ≤ Fintype.card M :=
  Results.Algebra.reset_minimum_generator three

/-- `reset:thm:basis`. -/
theorem reset_basis (three : Fin 3 ↪ Role) (s t : Reset.Term Var) :
    (s.Equivalent Role t ↔ Equational.Derives Reset.basis s t) ∧ Nat.card Reset.basis = 6 :=
  Results.Algebra.reset_basis three s t

/-- `reset:thm:anti`. -/
theorem reset_antimatroids [DecidableEq Var] (three : Fin 3 ↪ Role) :
    ∃ e : {f : (Var → WinnerSet Role) → WinnerSet Role // ∃ t : Reset.Term Var, ∀ v, f v = t.eval v} ≃
      Reset.RootedAntimatroid Var, ∀ t : Reset.Term Var,
      let F := e ⟨t.eval,⟨t,fun _ => rfl⟩⟩
      F.ground = t.varFinset ∧ F.root = t.root ∧
      (∀ A : Finset Var, A ∈ F.feasible ↔ A ⊆ t.varFinset ∧ ∀ j ∈ A, t.Selected (A : Set Var) j) ∧
      ∀ (B : Set Var) j, F.Ready B j ↔ t.Selected B j :=
  Results.Algebra.reset_antimatroids three

theorem reset_table_synthesis [DecidableEq Var] [Fintype Var] (G : Reset.GuardTable Var) :
    G.WellFormed ↔ ∃ t : Reset.Term Var, t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * (∑ j, (G.guards j).card) :=
  Results.Algebra.reset_table_realization G

/-- `owner:lem:root`. -/
theorem owner_root_status (t : Owner.Term Role Var) (valuation : Var → WinnerSet Role) :
    ((t.eval valuation).Ambiguous ↔ (valuation t.root).Ambiguous) ∧
    ∀ r, t.eval valuation = WinnerSet.singleton r ↔ valuation t.root = WinnerSet.singleton r :=
  Results.Algebra.owner_root_status t valuation

/-- `owner:thm:guards`. -/
theorem owner_guard_completeness [DecidableEq Role] [DecidableEq Var] (s t : Owner.Term Role Var)
    (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hs : s.OwnersIn (fun r => r = k ∨ r = a)) (ht : t.OwnersIn (fun r => r = k ∨ r = a)) :
    (Owner.Covers (s.guards k) (t.guards k) ↔
      ∀ valuation : Var → WinnerSet Role, k ∈ (s.eval valuation).val → k ∈ (t.eval valuation).val) ∧
    (¬Owner.Covers (s.guards k) (t.guards k) → ∃ valuation : Var → WinnerSet Role,
      k ∈ (s.eval valuation).val ∧ k ∉ (t.eval valuation).val ∧ ∀ j,
        ∃ r ∈ ({k,a,b} : Set Role), ∃ q ∈ ({k,a,b} : Set Role), (valuation j).val = {r,q}) :=
  Results.Algebra.owner_guard_completeness s t k a b hka hkb hab hs ht

/-- `owner:thm:one-table`. -/
theorem owner_one_table [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (a k : Role) (hka : k ≠ a) (s t : Owner.Term Role Var)
    (hs : s.OwnersIn (fun r => r = a)) (ht : t.OwnersIn (fun r => r = a)) :
    s.Equivalent t ↔ Owner.Covers (s.guards k) (t.guards k) ∧ Owner.Covers (t.guards k) (s.guards k) :=
  Results.Algebra.owner_one_table three a k hka s t hs ht

/-- `owner:thm:four`. -/
theorem owner_minimum_generator [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role) (a k : Role) (hka : k ≠ a) :
    Fintype.card Owner.Four = 4 ∧
    (∀ s t : Owner.Term Role Var, s.OwnersIn (fun r => r = a) → t.OwnersIn (fun r => r = a) →
      (s.Equivalent t ↔ ∀ valuation : Var → Owner.Four, s.evalFour valuation = t.evalFour valuation)) ∧
    ∀ (M : Type w) [Fintype M] [(Equational.language (Owner.Symbol Unit)).Structure M],
      letI := Owner.fourStructure (Role := Unit)
      (∀ e : Equational.Identity (Owner.Symbol Unit), e.Holds Owner.Four ↔ e.Holds M) → 4 ≤ Fintype.card M :=
  Results.Algebra.owner_minimum_generator three a k hka

theorem owner_table_synthesis [DecidableEq Role] [DecidableEq Var] (T : Owner.GuardTable Var)
    (a k b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (positions : List Var) (hcan : T.Canonical) (hlisted : T.Listed positions)
    (realizable : ∃ t : Owner.Term Role Var, T.Realizes a t) :
    ∃ t : Owner.Term Role Var, T.Realizes a t ∧
      t.size ≤ 1 + T.entries.length * (10 * positions.length + 7) :=
  Results.Algebra.owner_table_realization T a k b hka hkb hab positions hcan hlisted realizable

/-- `owner:thm:basis-main`. -/
theorem owner_thirty_six_equation_basis (three : Fin 3 ↪ Role) (a k : Role) (hka : k ≠ a) :
    letI := Owner.oneOwnerStructure a
    (Set.range Owner.FiniteBasis.fiveVariableAxiom).ncard = 36 ∧
    (∀ i : Fin 36, (Owner.FiniteBasis.fiveVariableAxiom i).variableCount ≤ 5) ∧
    Equational.IsBasis (WinnerSet Role) (Set.range Owner.FiniteBasis.fiveVariableAxiom) ∧
    ∀ (T : Equational.Theory (Owner.Symbol Unit)) n,
      Equational.IsBasis (WinnerSet Role) T → Equational.HasVariableBound T n → 5 ≤ n :=
  Results.Algebra.owner_thirty_six_equation_basis three a k hka

theorem joint_owner_observation_failure (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ s t : Owner.Term Role (Fin 4), s.OwnersIn (fun r => r = a ∨ r = b) ∧
      t.OwnersIn (fun r => r = a ∨ r = b) ∧
      (∀ valuation : Fin 4 → WinnerSet Role,
        (a ∈ (s.eval valuation).val ↔ a ∈ (t.eval valuation).val) ∧
        (b ∈ (s.eval valuation).val ↔ b ∈ (t.eval valuation).val)) ∧ ¬s.Equivalent t :=
  Results.Algebra.joint_owner_observation_failure a b c hab hac hbc

theorem strict_two_owner_policy (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∃ t : Reset.Term (Fin 3), ∀ v : Fin 3 → WinnerSet Role,
      t.eval v = (WinnerSet.choice a (WinnerSet.choice b (v 1) (v 2)) (v 1)).reset (v 0) :=
  Results.Algebra.strict_two_owner_policy a b c hab hac hbc

theorem two_owner_selective {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (a b : Role) (hab : a ≠ b) :
    (∀ X Y Z : WinnerSet Role, WinnerSet.twoOwnerSelective a b X Y Z = WinnerSet.policyReset {a,b} X Y Z) ∧
    Problems.policyLanguage (fun _ : Unit => ({a,b} : Finset Role)) ∈ Cslib.Complexity.P Problems.wordEncoding :=
  Results.Complexity.two_owner_selective three a b hab

theorem choice_union_basis (three : Fin 3 ↪ Role) (owner : Role) :
    letI := Dissemilattice.winnerStructure owner
    Dissemilattice.theory.ncard = 7 ∧ Dissemilattice.theory.Finite ∧
    Equational.IsBasis (WinnerSet Role) Dissemilattice.theory ∧
    ∀ (M : Type v) [(Equational.language Dissemilattice.Symbol).Structure M],
      Equational.InVariety Dissemilattice.Symbol (WinnerSet Role) M ↔
        Nonempty M ∧ Dissemilattice.Laws (Dissemilattice.add (M := M)) Dissemilattice.mul :=
  Results.Algebra.choice_union_basis three owner

/-- Canonical normal forms asserted in the discussion. -/
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

/-- `core:thm:no-basis`. -/
theorem core_nonfinite_basis [DecidableEq Role] [Finite Role] (three : Fin 3 ↪ Role) :
    letI := Equational.coreStructure Role
    ¬Equational.HasFiniteBasis (Equational.CoreSymbol Role) (WinnerSet Role) ∧
    ∀ n : ℕ, ∃ (B : Type u) (_str : (Equational.language (Equational.CoreSymbol Role)).Structure B),
      Nonempty B ∧ Finite B ∧
      (∀ e : Equational.Identity (Equational.CoreSymbol Role),
        e.variableCount ≤ n → e.Holds (WinnerSet Role) → e.Holds B) ∧
      ∃ e : Equational.Identity (Equational.CoreSymbol Role), e.Holds (WinnerSet Role) ∧ ¬e.Holds B :=
  Results.Algebra.core_nonfinite_basis three

/-- `core:thm:no-basis`, `full:thm:nonfinite-basis`. -/
theorem expanded_nonfinite_basis [DecidableEq Role] [Finite Role] (three : Fin 3 ↪ Role) :
    (let _ := Equational.publicStructure Role
     ¬Equational.HasFiniteBasis (Equational.PublicSymbol Role) (WinnerSet Role)) ∧
    (let _ := Equational.fullStructure Role
     ¬Equational.HasFiniteBasis (Equational.FullSymbol Role) (WinnerSet Role)) ∧
    ∀ n : ℕ,
    ∃ (B : Type u)
      (full : (Equational.language (Equational.FullSymbol Role)).Structure B)
      (publicChoice : (Equational.language (Equational.PublicSymbol Role)).Structure B),
      Nonempty B ∧ Finite B ∧
      (∀ e : Equational.Identity (Equational.FullSymbol Role), e.variableCount ≤ n →
        (let _ := Equational.fullStructure Role; e.Holds (WinnerSet Role)) →
        @Equational.Identity.Holds _ e B full) ∧
      (∀ e : Equational.Identity (Equational.PublicSymbol Role), e.variableCount ≤ n →
        (let _ := Equational.publicStructure Role; e.Holds (WinnerSet Role)) →
        @Equational.Identity.Holds _ e B publicChoice) ∧
      (let _ := Equational.fullStructure Role
       ¬@Equational.InVariety _ (WinnerSet Role) B inferInstance full) ∧
      (let _ := Equational.publicStructure Role
       ¬@Equational.InVariety _ (WinnerSet Role) B inferInstance publicChoice) :=
  Results.Algebra.expanded_nonfinite_basis three

theorem reset_circuit_large_tables (n : ℕ) :
    ∃ (C : Circuit.Equation Reset.Symbol (Bool ⊕ (ℕ × Bool))) (t : Reset.Term (Bool ⊕ (ℕ × Bool))),
      C.WellFormed ∧ C.gates.length = 6*n+3 ∧ C.unfold = some (t,t) ∧ 2^n ≤ (t.table (.inl true)).card :=
  Results.Games.reset_circuit_large_tables n

/-! ## Equational complexity and algorithms -/
open Problems

/-- `gen:thm:complexity`. -/
theorem equational_complexity (signature : PublicSignature) :
    (∀ K : ℕ, 3 ≤ K → Cslib.Complexity.coNPComplete (fullEquationEncoding K) (fullEquations signature K)) ∧
    Cslib.Complexity.coNPComplete wordEncoding (uniformFullLanguage signature) :=
  Results.Complexity.equational_complexity signature

/-- `thm:raw-pairs`. -/
theorem raw_pair_dichotomy {Role : Type} [Fintype Role] (three : Fin 3 ↪ Role)
    (selected : Finset (Raw.Operation Role)) :
    (selected.card ≤ 1 → rawLanguage selected ∈ Cslib.Complexity.P wordEncoding) ∧
    (1 < selected.card → Cslib.Complexity.coNPComplete wordEncoding (rawLanguage selected)) :=
  Results.Complexity.raw_pair_dichotomy three selected

/-- `owner:cor:complexity`. -/
theorem owner_count_dichotomy {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owners : Finset Role) :
    (owners.card ≤ 1 → ownerLanguage owners Eq ∈ Cslib.Complexity.P wordEncoding) ∧
    (1 < owners.card → Cslib.Complexity.coNPComplete wordEncoding (ownerLanguage owners Eq)) ∧
    ∀ observer : Role,
      ((owners.erase observer).card ≤ 1 →
        ownerLanguage owners (fun x y => observer ∈ x.val → observer ∈ y.val) ∈ Cslib.Complexity.P wordEncoding ∧
        ownerLanguage owners (fun x y => observer ∈ x.val ↔ observer ∈ y.val) ∈ Cslib.Complexity.P wordEncoding) ∧
      (1 < (owners.erase observer).card →
        Cslib.Complexity.coNPComplete wordEncoding
          (ownerLanguage owners (fun x y => observer ∈ x.val → observer ∈ y.val)) ∧
        Cslib.Complexity.coNPComplete wordEncoding
          (ownerLanguage owners (fun x y => observer ∈ x.val ↔ observer ∈ y.val))) :=
  Results.Complexity.owner_count_dichotomy three owners

theorem policy_family_dichotomy {Role Label : Type}
    [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]
    (policies : Label → Finset Role) (three : Fin 3 ↪ Role) :
    ((Policies.PatternChain (policySets policies) ∨
      Policies.PatternIntersectionClosed (policySets policies) ∧ Policies.RepeatedPattern (policySets policies)) → policyLanguage policies ∈ Cslib.Complexity.P wordEncoding) ∧
    (¬(Policies.PatternChain (policySets policies) ∨
      Policies.PatternIntersectionClosed (policySets policies) ∧ Policies.RepeatedPattern (policySets policies)) →
      Cslib.Complexity.coNPComplete wordEncoding (policyLanguage policies)) :=
  Results.Complexity.policy_family_dichotomy policies three

theorem guarded_pair_complexity {Role : Type} [Fintype Role] (first second marker : Role)
    (different : first ≠ second) (outside_first : first ≠ marker) (outside_second : second ≠ marker) :
    Cslib.Complexity.coNPComplete wordEncoding (guardedLanguage first second) :=
  Results.Complexity.guarded_pair_complexity first second marker different outside_first outside_second

theorem reset_circuit_complexity {Role : Type u} (three : Fin 3 ↪ Role) :
    Cslib.Complexity.coNPComplete wordEncoding (resetCircuitLanguage Role) ∧
    Cslib.Complexity.coNPComplete wordEncoding resetChainCircuitLanguage :=
  Results.Complexity.reset_circuit_complexity three

/-- The reset/union theories strictly decrease with the role count (thm:colouring-theories). -/
theorem role_count_identity_theories (n : ℕ) (hn : 3 ≤ n) :
    {e : Equational.Identity ResetUnion.Symbol |
      letI := ResetUnion.structureOf (Role := Fin (n+1)); e.Holds (WinnerSet (Fin (n+1)))} ⊂
    {e : Equational.Identity ResetUnion.Symbol |
      letI := ResetUnion.structureOf (Role := Fin n); e.Holds (WinnerSet (Fin n))} :=
  Results.role_count_identity_theories n hn

theorem canonicalization_collapse {K : ℕ} (three : Fin 3 ↪ Fin K)
    (canonicalize : CoreTerm K → List Bool) (runtime : PolynomialTime canonicalize (coreTermEncoding K) wordEncoding)
    (compare : List Bool × List Bool → Bool)
    (comparison : PolynomialTime compare pairWordEncoding booleanEncoding)
    (correct : ∀ s t : CoreTerm K, compare (canonicalize s,canonicalize t) = true ↔ s.val.Equivalent t.val) :
    Cslib.Complexity.P wordEncoding = Cslib.Complexity.NP wordEncoding :=
  Results.Complexity.canonicalization_collapse three canonicalize runtime compare comparison correct

theorem uniform_equality_algorithms :
    ∃ resetCheck ownerCheck : List Bool → Bool,
      PolynomialTime resetCheck wordEncoding booleanEncoding ∧
      PolynomialTime ownerCheck wordEncoding booleanEncoding ∧
      ∀ (Role : Type u) [DecidableEq Role] (_three : Fin 3 ↪ Role),
        (∀ word, resetCheck word = true ↔ word ∈ resetLanguage Role) ∧
        (∀ owner word, ownerCheck word = true ↔ word ∈ oneOwnerLanguage (Role := Role) owner) :=
  Results.Complexity.uniform_equality_algorithms

theorem reset_table_recognition_polynomial : resetTableLanguage ∈ Cslib.Complexity.P wordEncoding :=
  Results.Complexity.reset_table_recognition_polynomial

theorem reset_table_synthesis_polynomial :
    ∃ synthesize : List Bool → Option (List Bool), PolynomialTime synthesize wordEncoding partialWordEncoding ∧
      (∀ input, (synthesize input).isSome = true ↔ input ∈ resetTableLanguage) ∧
      ∀ input output, synthesize input = some output → ResetSynthesis input output :=
  Results.Complexity.reset_table_synthesis_polynomial

theorem owner_table_algorithms {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owner : Role) :
    {input : OwnerTableInput | OwnerTableRealizable owner input} ∈ Cslib.Complexity.P ownerTableEncoding ∧
    ∃ synthesize : OwnerTableInput → Option (OwnerTableOutput Role),
      PolynomialTime synthesize ownerTableEncoding (ownerTableOutputEncoding Role) ∧
      (∀ input, (synthesize input).isSome = true ↔ OwnerTableRealizable owner input) ∧
      ∀ input output, synthesize input = some output → OwnerSynthesisOutput owner input output :=
  Results.Complexity.owner_table_algorithms three owner

theorem core_extraction_polynomial :
    ∃ extract : List Bool → Option (List Bool), PolynomialTime extract wordEncoding partialWordEncoding ∧
      ∀ (K : ℕ) (_large : 3 ≤ K) (term : Term (Fin K) ℕ),
        ((extract (termCode K term)).isSome = true ↔ term.Idempotent) ∧
        ∀ word, extract (termCode K term) = some word → CoreExtractionOutput K term word :=
  Results.Complexity.core_extraction_polynomial

/-! ## Completely disclosed sealed rounds -/
section Rounds
open Rounds.Game
variable [Fintype Role] [DecidableEq Role]

/-- `se:thm:round`. -/
theorem round_recursion :
    (∀ G : Rounds.Game Role, G.value = G.observedValues) ∧
    (∀ r : Role, (Rounds.Game.leaf r).value = {PMF.pure r}) ∧
    (∀ (sizes : Role → ℕ) (next : ((i : Role) → Fin (sizes i+1)) → Rounds.Game Role),
      (Rounds.Game.round sizes next).value = roundOperator sizes (fun a => (next a).value)) :=
  Results.Games.round_recursion

/-- `se:cor:public`. -/
theorem public_mixed_support (G : Strategic.Tree Role) :
    possibleWinners (publicTree G).value = (Strategic.value G).val :=
  Results.Games.public_mixed_support G

/-- `se:thm:infinite`. -/
theorem infinite_winner_algebra (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (∀ n m : ℕ, possibleWinners (threshold a b c n m).value =
      if n < m then {a,b} else if n = m then {a,b,c} else {a,c}) ∧
    (∀ n m : ℕ, (threshold a b c n m).BooleanMenus) ∧
    (∀ (Carrier : Type w) [Finite Carrier], ¬Nonempty (WinnerSummary a c Carrier)) :=
  Results.Games.infinite_winner_algebra a b c hab hac hbc

end Rounds

/-! ## The two-player boundary case -/
open Classical in
theorem two_player_identification (labels : Fin 2 ≃ Role) :
    ∃ q : WinnerSet Role ≃ Fin 3,
      (∀ i, q (TwoPlayers.value labels i) = i) ∧
      (∀ A B, q (WinnerSet.choice (labels 0) A B) = max (q A) (q B)) ∧
      (∀ A B, q (WinnerSet.choice (labels 1) A B) = min (q A) (q B)) ∧
      (∀ A, q (WinnerSet.rename (Equiv.swap (labels 0) (labels 1)) A) = (q A).rev) :=
  Results.two_player_identification labels

theorem two_player_degeneracies (labels : Fin 2 ≃ Role) :
    (∀ A B : WinnerSet Role, A.reset B = B) ∧
    (∀ (r : Role) (X Y Z : WinnerSet Role), WinnerSet.guardedChoice r X Y Z = X) ∧
    (∀ {Var : Type v} (t : Term Role Var), t.AtomPreserving) ∧
    (¬∃ t : Term Role (Fin 2), ∀ x : Fin 2 → WinnerSet Role, t.eval x = (x 0).union (x 1)) ∧
    (∃ t : Term Role (Fin 2), t.Idempotent ∧ ¬∃ s : Term Role (Fin 2), s.IsCore ∧ s.Equivalent t) :=
  Results.Games.two_player_degeneracies labels

theorem two_player_finite_basis (labels : Fin 2 ≃ Role) :
    letI := TwoPlayers.Kleene.winnerStructure labels
    TwoPlayers.Kleene.basis.Finite ∧ Equational.IsBasis (WinnerSet Role) TwoPlayers.Kleene.basis :=
  Results.Games.two_player_basis labels

theorem two_player_round_support (sizes : Fin 2 → ℕ)
    (next : ((i : Fin 2) → Fin (sizes i+1)) → Rounds.Game (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2),
      (∀ a, (g a).val = Rounds.Game.possibleWinners (next a).value) ∧
      Rounds.Game.possibleWinners (Rounds.Game.round sizes next).value =
        ((Rounds.Game.TwoPlayers.serialZero sizes g).union (Rounds.Game.TwoPlayers.serialOne sizes g)).val :=
  Results.Games.two_player_round_support sizes next

theorem two_player_round_contexts :
    (∀ (G H : Rounds.Game (Fin 2)), Rounds.Game.possibleWinners G.value = Rounds.Game.possibleWinners H.value →
      Rounds.Game.SameContextualWinners G H) ∧
    Rounds.Game.possibleWinners (Rounds.Game.diagonal (0 : Fin 2) 1 (.leaf 0) (.leaf 0)).value = {0,1} :=
  Results.Games.two_player_round_contexts

end KFOL.Paper

#audit_namespace KFOL.Paper
