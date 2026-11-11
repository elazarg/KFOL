module

public import KFOL.Definitions.PaperAlgebra
public import KFOL.Results.Certificates
public import KFOL.Algebra.FullBasis.NonfiniteBasis
public import KFOL.Owner.FourVariableObstruction
public import KFOL.Owner.Basis.Exchange

@[expose] public section
namespace KFOL.Results.Algebra
universe u v w
variable {Role : Type u} {Var : Type v}

/-- All-arity synthesis of the core's singleton-output predicates. -/
theorem core_singleton_profiles [DecidableEq Role] [Fintype Role] [Fintype Var]
    (three : Fin 3 ↪ Role) (F : Role → (Var → Bool) → Bool) :
    (∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      ∀ i v, Core.profile i v t = F i v) ↔ Core.AdmissibleProfiles F :=
  Core.exists_term_iff_admissibleProfiles three F

/-- Neutral union, game:thm:union. -/
theorem neutral_union (r s t : Role) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (A B : WinnerSet Role) :
    WinnerSet.choice t (WinnerSet.choice r A B) (WinnerSet.choice s A B) = A.union B :=
  WinnerSet.three_owner_union A B r s t hrs hrt hst

/-- Each owned choice is a semilattice join. -/
theorem owned_choice_semilattices (r : Role) :
    ∃ s : SemilatticeSup (WinnerSet Role),
      (∀ A B, @Max.max _ s.toMax A B = WinnerSet.choice r A B) ∧
      (∀ A B, @LE.le _ s.toLE A B ↔
        B = WinnerSet.singleton r ∨ (A ≠ WinnerSet.singleton r ∧ A.val ⊆ B.val)) :=
  Results.owned_choice_semilattices r

/-- Owned choices have no faithful Boolean product representation. -/
theorem no_boolean_product (three : Fin 3 ↪ Role) {Index : Type w}
    (M : Index → Type v) [∀ i, BooleanAlgebra (M i)] (select : Role → Index → Bool) :
    ¬∃ f : WinnerSet Role → ∀ i, M i, Function.Injective f ∧ ∀ r A B i,
      f (WinnerSet.choice r A B) i = if select r i then f A i ⊔ f B i else f A i ⊓ f B i :=
  Results.no_boolean_product three M select

/-- Player views, view:thm:view. -/
theorem player_views [Fintype Role] (three : Fin 3 ↪ Role) (k : Role) :
    (∀ A B : WinnerSet Role, A.ObservationallyEquivalent k B ↔ A.SameView k B) ∧
    (∀ A B : WinnerSet Role, WinnerSet.view k A = WinnerSet.view k B ↔ A.SameView k B) ∧
    Function.Surjective (WinnerSet.view k) ∧
    Nat.card (Quotient (Setoid.ker (WinnerSet.view k))) = Fintype.card Role + 1 :=
  Results.player_views three k

/-- The player quotients give a faithful subdirect representation. -/
theorem public_subdirect_representation [Fintype Role] (three : Fin 3 ↪ Role) :
    Nat.card (WinnerSet Role) = 2 ^ Fintype.card Role - 1 ∧
    Function.Injective (fun A : WinnerSet Role => fun k => WinnerSet.view k A) ∧
    (∀ k : Role, Function.Surjective (WinnerSet.view k) ∧ Nat.card (PlayerView k) = Fintype.card Role + 1) ∧
    ∀ (t : Term Role Var), t.IsPublic → ∀ k valuation,
      WinnerSet.view k (t.eval valuation) = PlayerView.eval three k t (fun x => WinnerSet.view k (valuation x)) :=
  by
    obtain ⟨hc,hi,hf,he⟩ := Results.public_subdirect_representation three
    exact ⟨hc,hi,hf,he Var⟩

/-- The quotient operations are joins of the explicit layered player orders. -/
theorem player_view_orders (three : Fin 3 ↪ Role) (k r : Role) :
    (∀ A B : WinnerSet Role, WinnerSet.view k (WinnerSet.choice r A B) =
      PlayerView.choice r (WinnerSet.view k A) (WinnerSet.view k B)) ∧
    ∃ order : SemilatticeSup (PlayerView k), let _ := order
      (∀ p q : PlayerView k, p ⊔ q = PlayerView.choice r p q) ∧
      ∀ p q : PlayerView k, p ≤ q ↔ PlayerView.Below r p q :=
  Results.player_view_orders three k r

/-- Public unary contexts are constant or extensive, and unique-winner tests collapse ambiguity. -/
theorem unique_winner_observations (t : Term Role Var) (ht : t.IsPublic) (active : Var → Bool) (parameters : Var → WinnerSet Role) :
    ((∃ C : WinnerSet Role, ∀ X : WinnerSet Role,
      t.eval (fun x => if active x then X else parameters x) = C) ∨
      ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun x => if active x then X else parameters x)).val) ∧
    ∀ A B : WinnerSet Role, A.Ambiguous → B.Ambiguous → ∀ r,
      (t.eval (fun x => if active x then A else parameters x) = WinnerSet.singleton r) ↔
        (t.eval (fun x => if active x then B else parameters x) = WinnerSet.singleton r) :=
  Results.unique_winner_observations t ht active parameters

/-- Internal switching makes a single player observation faithful. -/
theorem switching_observation (k : Role) (A B : WinnerSet Role) :
    (∀ n (t : Term Role (Option (Fin n))) (parameters : Fin n → WinnerSet Role),
      k ∈ (t.eval (fun x => x.elim A parameters)).val ↔
        k ∈ (t.eval (fun x => x.elim B parameters)).val) ↔ A = B :=
  Results.switching_observation k A B

/-- Congruences are exactly kernels of admissible closures and fixed families. -/
theorem congruence_classification [Finite Role] [Nonempty Role] (three : Fin 3 ↪ Role) :
    (∀ θ : WinnerSet.Congruence Role, ∃! c : ClosureOperator (WinnerSet Role),
      WinnerSet.AtomClosure c ∧ ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ c : ClosureOperator (WinnerSet Role), WinnerSet.AtomClosure c →
      ∃ θ : WinnerSet.Congruence Role, ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ θ : WinnerSet.Congruence Role, ∃! F : Set (WinnerSet Role), WinnerSet.AdmissibleFamily F ∧
      ∀ A B, θ.r A B ↔ WinnerSet.familyClosureValue F A = WinnerSet.familyClosureValue F B) ∧
    (∀ F : Set (WinnerSet Role), WinnerSet.AdmissibleFamily F → ∃ θ : WinnerSet.Congruence Role,
      ∀ A B, θ.r A B ↔ WinnerSet.familyClosureValue F A = WinnerSet.familyClosureValue F B) :=
  Results.congruence_classification three

/-- Switching-compatible congruences form the ambiguity-threshold chain. -/
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
  Results.symmetric_congruence_chain three

/-- Permutation provenance on a status cell, sym:lem:provenance. -/
theorem status_cell_provenance (t : Term Role Var) (base : Var → WinnerSet Role) :
    ∃ (C : Set Role) (P : Var → Finset (Equiv.Perm Role)), C.Finite ∧
      (∀ j, ∀ p ∈ P j, (base j).Ambiguous) ∧ ∀ valuation : Var → WinnerSet Role,
        (∀ j r, base j = WinnerSet.singleton r ↔ valuation j = WinnerSet.singleton r) →
        (t.eval valuation).val = C ∪ ⋃ j, ⋃ p ∈ P j, p '' (valuation j).val :=
  Results.status_cell_provenance t base

/-- Every failed full-signature equation has an atom/pair countervaluation. -/
theorem pair_countervaluations (s t : Term Role Var) (failure : ¬s.Equivalent t) :
    ∃ valuation : Var → WinnerSet Role,
      (∀ x, ∃ a b : Role, (valuation x).val = {a,b}) ∧ s.eval valuation ≠ t.eval valuation :=
  by
    classical
    exact Results.pair_countervaluations s t (not_forall.mp failure)

/-- The unique least full-signature input test domain has K(K+1)/2 values. -/
theorem optimal_test_domain [Fintype Role] (three : Fin 3 ↪ Role) :
    (∀ D : Set (WinnerSet Role), CompleteTestDomain D ↔
      ∀ a b, (WinnerSet.singleton a).union (WinnerSet.singleton b) ∈ D) ∧
    IsLeast {D : Set (WinnerSet Role) | CompleteTestDomain D} {A | ∃ a b : Role, A.val = {a,b}} ∧
    Nat.card {A : WinnerSet Role // ∃ a b : Role, A.val = {a,b}} =
      Fintype.card Role * (Fintype.card Role + 1) / 2 :=
  Results.optimal_test_domain three

/-- Public-reduct test domains contain all atoms and omit each role ambiguously. -/
theorem reduct_test_domains [Fintype Role] (three : Fin 3 ↪ Role) (D : Set (WinnerSet Role)) :
    CompletePublicTestDomain D ↔ (∀ r, WinnerSet.singleton r ∈ D) ∧
      ∀ k, ∃ A ∈ D, A.Ambiguous ∧ k ∉ A.val :=
  Results.reduct_test_domains three D

/-- The sharp public-reduct test-domain size is six or K+2. -/
theorem minimum_reduct_test_domain [Fintype Role] (three : Fin 3 ↪ Role) :
    IsLeast {m : ℕ | ∃ D : Finset (WinnerSet Role), CompletePublicTestDomain (D : Set (WinnerSet Role)) ∧ D.card = m}
      (if Fintype.card Role = 3 then 6 else Fintype.card Role + 2) :=
  (Results.minimum_reduct_test_domain three).1

/-- Idempotency is exactly clean syntax and core expressibility. -/
theorem idempotent_elimination (three : Fin 3 ↪ Role) (t : Term Role Var) :
    (t.Idempotent ↔ ¬t.HasWinner ∧ ∀ x p, (x,p) ∈ t.inputOccurrences → p = 1) ∧
    (t.Idempotent ↔ ∃ c : Term Role Var, c.IsCore ∧ c.Equivalent t) :=
  by
    have h := Results.idempotent_elimination three t
    exact ⟨h.1,h.2.1⟩

/-- Every idempotent operation descends to the irredundant player quotients. -/
theorem intrinsic_player_views [Fintype Role] (three : Fin 3 ↪ Role) :
    (∀ t : Term Role Var, t.Idempotent → ∀ k valuation,
      WinnerSet.view k (t.eval valuation) = PlayerView.eval three k t (fun x => WinnerSet.view k (valuation x))) ∧
    Function.Injective (fun A : WinnerSet Role => fun k => WinnerSet.view k A) ∧
    (∀ k : Role, Function.Surjective (WinnerSet.view k) ∧ Nat.card (PlayerView k) = Fintype.card Role + 1) ∧
    ∀ k, ∃ A B : WinnerSet Role, A ≠ B ∧
      (∀ j, j ≠ k → WinnerSet.view j A = WinnerSet.view j B) ∧ WinnerSet.view k A ≠ WinnerSet.view k B :=
  by
    have h := Results.intrinsic_player_views three
    exact ⟨h.1 Var,h.2⟩

/-- The ambiguous trace is a nonempty join; it excludes NU and Malcev terms and forces regular identities. -/
theorem semilattice_trace (three : Fin 3 ↪ Role) :
    (∀ n (t : Term Role (Fin n)), t.Idempotent → ∃ S : Finset (Fin n), S.Nonempty ∧
      ∀ valuation : Fin n → WinnerSet Role, (∀ x, (valuation x).Ambiguous) →
        ∀ r, r ∈ (t.eval valuation).val ↔ ∃ x ∈ S, r ∈ (valuation x).val) ∧
    (∀ n, 0 < n → ∀ t : Term Role (Fin n),
      ¬∀ A B : WinnerSet Role, ∀ i, t.eval (Function.update (fun _ => A) i B) = A) ∧
    (∀ t : Term Role (Fin 3), ¬((∀ A B : WinnerSet Role, t.eval (fun i => if i = 0 then A else B) = A) ∧
      (∀ A B : WinnerSet Role, t.eval (fun i => if i = 2 then B else A) = B))) ∧
    ∀ n (s t : Term Role (Fin n)), s.IsCore → t.IsCore → s.Equivalent t → s.vars = t.vars :=
  by
    have h := Results.semilattice_trace three
    exact ⟨fun n t ht => ⟨t.vars,h.1 n t ht⟩,h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2.2⟩

/-- One source occurrence meets all pairwise disjoint output requirements. -/
theorem common_source {Index : Type w} (t : Term Role Var) (valuation : Index → Var → WinnerSet Role)
    (regions : Index → Set Role) (hd : Pairwise fun i j => Disjoint (regions i) (regions j))
    (hf : ∀ i, (t.eval (valuation i)).val ⊆ regions i) :
    ∃ (leaf : Role ⊕ Var) (p : Equiv.Perm Role), (leaf,p) ∈ t.sourceOccurrences ∧
      (∀ i, (WinnerSet.rename p (leaf.elim WinnerSet.singleton (valuation i))).val ⊆ regions i) ∧
      ((∃ i j : Index, i ≠ j) → ∃ x, leaf = .inr x ∧ (x,p) ∈ t.inputOccurrences) :=
  Results.common_source t valuation regions hd hf

/-- Repeated atomic input triples cannot yield three distinct atomic outputs. -/
theorem atomic_repeated_triples (t : Term Role Var) (valuation : Fin 3 → Var → Role)
    (hrepeat : ∀ x, Atomic.Repeat (valuation 0 x) (valuation 1 x) (valuation 2 x))
    (out : Fin 3 → Role)
    (heval : ∀ i, t.eval (fun x => WinnerSet.singleton (valuation i x)) = WinnerSet.singleton (out i)) :
    Atomic.Repeat (out 0) (out 1) (out 2) :=
  Results.atomic_repeated_triples t valuation hrepeat out heval

/-- No full-signature term implements atomic if-then-else. -/
theorem no_atomic_if_then_else (three : Fin 3 ↪ Role) (a b : Role) (hab : a ≠ b) (t : Term Role (Fin 3)) :
    ¬((∀ y z : Role, t.eval (fun i => WinnerSet.singleton (if i = 0 then a else if i = 1 then y else z)) = WinnerSet.singleton y) ∧
      (∀ y z : Role, t.eval (fun i => WinnerSet.singleton (if i = 0 then b else if i = 1 then y else z)) = WinnerSet.singleton z)) :=
  Results.no_atomic_if_then_else three a b hab t

/-- The atomic clone consists exactly of essentially unary or two-valued functions. -/
theorem atomic_functions [Finite Role] (three : Fin 3 ↪ Role) [Finite Var] (f : (Var → Role) → Role) :
    (∃ t : Term Role Var, t.AtomicRealizes f) ↔ Atomic.EssentiallyUnary f ∨ Atomic.AtMostTwo f :=
  by
    let _ : Nonempty Role := ⟨three 0⟩
    exact Term.atomic_function_classification f

/-- An idempotent atom-preserving operation projects one atomic input. -/
theorem determinacy (three : Fin 3 ↪ Role) [Finite Var] (t : Term Role Var)
    (ha : t.AtomPreserving) (hd : t.Idempotent) :
    ∃ i : Var, ∀ x : Var → Role, t.eval (fun j => WinnerSet.singleton (x j)) = WinnerSet.singleton (x i) :=
  Results.determinacy three t ha hd

/-- Exactly four binary operations are realized by atom-preserving core terms. -/
theorem binary_atom_preserving_iff [Finite Role] (three : Fin 3 ↪ Role) (f : (Fin 2 → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role (Fin 2), t.IsCore ∧ t.AtomPreserving ∧ t.Idempotent ∧ ∀ v, t.eval v = f v) ↔
      (∀ v, f v = v 0) ∨ (∀ v, f v = v 1) ∨
      (∀ v, f v = (v 0).reset (v 1)) ∨ (∀ v, f v = (v 1).reset (v 0)) :=
  Results.binary_atom_preserving_iff three f

/-- A unary owned-choice expression with one fixed atom is constant or inflationary; a distinct atomic test detects constancy. -/
theorem one_constant_rigidity (t : Term Role Var) (ht : t.IsCore) (active : Var → Bool) (r : Role) :
    ((∀ X : WinnerSet Role, t.eval (fun x => if active x then X else WinnerSet.singleton r) = WinnerSet.singleton r) ∨
      ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun x => if active x then X else WinnerSet.singleton r)).val) ∧
    ∀ q, q ≠ r → t.eval (fun x => if active x then WinnerSet.singleton q else WinnerSet.singleton r) = WinnerSet.singleton r →
      ∀ X : WinnerSet Role, t.eval (fun x => if active x then X else WinnerSet.singleton r) = WinnerSet.singleton r :=
  ⟨ht.one_constant_dichotomy active r,fun q hq h => ht.one_constant_rigidity active r q hq h⟩

/-- Reset is an actual core term operation, without constants or role switches. -/
theorem reset_definability [Finite Role] (three : Fin 3 ↪ Role) :
    ∃ t : Term Role (Fin 2), t.IsCore ∧
      ∀ valuation : Fin 2 → WinnerSet Role, t.eval valuation = (valuation 0).reset (valuation 1) :=
  by
    let _ := Fintype.ofFinite Role
    exact (Results.reset_definability three).2 (Reset.Term.step (.var 0) (.var 1))

/-- Guarded choice is the stated reset composition, idempotent and atom-preserving. -/
theorem owner_definability (a : Role) :
    (∀ X Y Z : WinnerSet Role, WinnerSet.guardedChoice a X Y Z = (WinnerSet.choice a Y Z).reset X) ∧
    (∀ X : WinnerSet Role, WinnerSet.guardedChoice a X X X = X) ∧
    ∀ i (Y Z : WinnerSet Role), WinnerSet.guardedChoice a (WinnerSet.singleton i) Y Z = WinnerSet.singleton i :=
  ⟨fun _ _ _ => rfl,WinnerSet.guardedChoice_self a,WinnerSet.guardedChoice_singleton a⟩

/-- Guarded choice sees its owner on atomic side inputs. -/
theorem guarded_choice_example (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c ∉ (WinnerSet.guardedChoice a ((WinnerSet.singleton a).union (WinnerSet.singleton b))
      (WinnerSet.singleton a) (WinnerSet.singleton c)).val ∧
    c ∈ (WinnerSet.guardedChoice a ((WinnerSet.singleton a).union (WinnerSet.singleton b))
      (WinnerSet.singleton b) (WinnerSet.singleton c)).val :=
  Results.guarded_choice_example a b c hab hac hbc

/-- Reset keeps precisely the inputs selected by their ambiguity statuses. -/
theorem reset_selection (t : Reset.Term Var) (valuation : Var → WinnerSet Role) :
    ((t.eval valuation).Ambiguous ↔ (valuation t.root).Ambiguous) ∧
    ∀ r, r ∈ (t.eval valuation).val ↔
      ∃ j, t.Selected {i | (valuation i).Ambiguous} j ∧ r ∈ (valuation j).val :=
  ⟨Reset.Term.ambiguous_eval t valuation,Reset.Term.mem_eval t valuation⟩

/-- Canonical tables are the minimal semantic ambiguity prerequisites. -/
theorem reset_table_semantic_definition [DecidableEq Var] (three : Fin 3 ↪ Role) (t : Reset.Term Var) :
    (∀ valuation : Var → WinnerSet Role, ∀ r, r ∈ (t.eval valuation).val ↔
      ∃ j, ∃ A ∈ t.table j, (∀ k ∈ A, (valuation k).Ambiguous) ∧ r ∈ (valuation j).val) ∧
    ∀ j (A : Finset Var), A ∈ t.table j ↔
      three 2 ∈ (t.eval (Reset.markerValuation three j A)).val ∧
      ∀ B ⊆ A, three 2 ∈ (t.eval (Reset.markerValuation three j B)).val → A ⊆ B :=
  by
    exact Results.reset_table_semantic_definition three t

/-- Reset tables, the fixed chain test and the common identity theory agree. -/
theorem reset_tables_semantics [DecidableEq Var] (three : Fin 3 ↪ Role) (s t : Reset.Term Var) :
    (s.Equivalent Role t ↔ s.table = t.table) ∧
    (s.Equivalent Role t ↔ ∀ valuation : Var → WinnerSet Role,
      (∀ i, ∃ k : Fin 3, valuation i = Reset.chainValue three k) → s.eval valuation = t.eval valuation) ∧
    ∀ {Role' : Type w} (_three' : Fin 3 ↪ Role'), s.Equivalent Role t ↔ s.Equivalent Role' t :=
  by
    have h := Results.reset_tables_semantics three s t
    exact ⟨h.1,h.2.1,h.2.2.1⟩

/-- The fixed three-element reset chain is a smallest generator. -/
theorem reset_minimum_generator (three : Fin 3 ↪ Role) :
    letI := Reset.structureOf (WinnerSet.reset (Role := Role))
    letI := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    (∀ e : Equational.Identity Reset.Symbol, e.Holds (WinnerSet Role) ↔ e.Holds (Fin 3)) ∧
    ∀ (M : Type v) [Fintype M] [(Equational.language Reset.Symbol).Structure M],
      (∀ e : Equational.Identity Reset.Symbol, e.Holds (WinnerSet Role) ↔ e.Holds M) → 3 ≤ Fintype.card M :=
  (Results.reset_minimum_generator three).2

/-- The six displayed reset laws are a complete equational basis. -/
theorem reset_basis (three : Fin 3 ↪ Role) (s t : Reset.Term Var) :
    (s.Equivalent Role t ↔ Equational.Derives Reset.basis s t) ∧ Nat.card Reset.basis = 6 :=
  Results.reset_basis three s t

/-- Reset term functions correspond bijectively to uniquely rooted antimatroids. -/
theorem reset_antimatroids [DecidableEq Var] (three : Fin 3 ↪ Role) :
    ∃ e : {f : (Var → WinnerSet Role) → WinnerSet Role // ∃ t : Reset.Term Var, ∀ v, f v = t.eval v} ≃
      Reset.RootedAntimatroid Var, ∀ t : Reset.Term Var,
      let F := e ⟨t.eval,⟨t,fun _ => rfl⟩⟩
      F.ground = t.varFinset ∧ F.root = t.root ∧
      (∀ A : Finset Var, A ∈ F.feasible ↔ A ⊆ t.varFinset ∧ ∀ j ∈ A, t.Selected (A : Set Var) j) ∧
      ∀ (B : Set Var) j, F.Ready B j ↔ t.Selected B j :=
  Results.reset_antimatroids three

/-- Reset-table recognition is exact and realizing primitive terms have size O(nM). -/
theorem reset_table_synthesis [DecidableEq Var] [Fintype Var] (G : Reset.GuardTable Var) :
    (G.check = true ↔ ∃ t : Reset.Term Var, t.root = G.root ∧ t.table = G.guards) ∧
    (G.WellFormed ↔ ∃ t : Reset.Term Var, t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * (∑ j, (G.guards j).card)) :=
  ⟨(Results.reset_table_recognition G).1,Results.reset_table_realizability G⟩

/-- Guarded-owner terms preserve the atomic and ambiguous status of their root. -/
theorem owner_root_status (t : Owner.Term Role Var) (valuation : Var → WinnerSet Role) :
    ((t.eval valuation).Ambiguous ↔ (valuation t.root).Ambiguous) ∧
    ∀ r, t.eval valuation = WinnerSet.singleton r ↔ valuation t.root = WinnerSet.singleton r :=
  Results.owner_root_status t valuation

/-- Guard coverage exactly decides observational implication, with three-role pair countervaluations. -/
theorem owner_guard_completeness [DecidableEq Role] [DecidableEq Var] (s t : Owner.Term Role Var)
    (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hs : s.OwnersIn (fun r => r = k ∨ r = a)) (ht : t.OwnersIn (fun r => r = k ∨ r = a)) :
    (Owner.Covers (s.guards k) (t.guards k) ↔
      ∀ valuation : Var → WinnerSet Role, k ∈ (s.eval valuation).val → k ∈ (t.eval valuation).val) ∧
    (¬Owner.Covers (s.guards k) (t.guards k) → ∃ valuation : Var → WinnerSet Role,
      k ∈ (s.eval valuation).val ∧ k ∉ (t.eval valuation).val ∧ ∀ j,
        ∃ r ∈ ({k,a,b} : Set Role), ∃ q ∈ ({k,a,b} : Set Role), (valuation j).val = {r,q}) :=
  by
    constructor
    · exact s.observation_implication_iff t k a b hka hkb hab hs ht
    · intro h
      obtain ⟨g,_,hl,hr,hpairs⟩ := s.observation_countervaluation t k a b hka hkb hab hs ht h
      refine ⟨Owner.minimalVal k a b g,hl,hr,?_⟩
      intro j
      obtain ⟨r,hr,q,hq,he⟩ := hpairs j
      exact ⟨r,hr,q,hq,congrArg Subtype.val he⟩

/-- One outsider table completely determines a one-owner operation. -/
theorem owner_one_table [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (a k : Role) (hka : k ≠ a) (s t : Owner.Term Role Var)
    (hs : s.OwnersIn (fun r => r = a)) (ht : t.OwnersIn (fun r => r = a)) :
    s.Equivalent t ↔ Owner.Covers (s.guards k) (t.guards k) ∧ Owner.Covers (t.guards k) (s.guards k) :=
  (Results.owner_one_table three a k hka s t hs ht).1

/-- The one-owner theory is generated by the displayed four-element algebra and by no smaller algebra. -/
theorem owner_minimum_generator [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role) (a k : Role) (hka : k ≠ a) :
    Fintype.card Owner.Four = 4 ∧
    (∀ s t : Owner.Term Role Var, s.OwnersIn (fun r => r = a) → t.OwnersIn (fun r => r = a) →
      (s.Equivalent t ↔ ∀ valuation : Var → Owner.Four, s.evalFour valuation = t.evalFour valuation)) ∧
    ∀ (M : Type w) [Fintype M] [(Equational.language (Owner.Symbol Unit)).Structure M],
      letI := Owner.fourStructure (Role := Unit)
      (∀ e : Equational.Identity (Owner.Symbol Unit), e.Holds Owner.Four ↔ e.Holds M) → 4 ≤ Fintype.card M :=
  Results.owner_minimum_generator three a k hka

/-- Owner-table realizability is decidable, with explicit O(nM) primitive terms. -/
theorem owner_table_synthesis [DecidableEq Role] [DecidableEq Var] (T : Owner.GuardTable Var)
    (a k b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (positions : List Var) (hcan : T.Canonical) (hlisted : T.Listed positions) :
    (T.check positions = true ↔ ∃ t : Owner.Term Role Var, T.Realizes a t) ∧
    ((T.synthesize a positions).isSome = true ↔ T.check positions = true) ∧
    ∀ t, T.synthesize a positions = some t → T.Realizes a t ∧
      t.size ≤ 1 + T.entries.length * (10 * positions.length + 7) :=
  by
    have h := Results.owner_table_synthesis T a k b hka hkb hab positions hcan hlisted
    exact ⟨h.1,h.2.1,fun t ht => by
      have hh := h.2.2.1 t ht
      exact ⟨⟨hh.1,hh.2.1,hh.2.2.1⟩,hh.2.2.2⟩⟩

/-- Thirty-six equations on five variables suffice; every basis needs five variables. -/
theorem owner_thirty_six_equation_basis (three : Fin 3 ↪ Role) (a k : Role) (hka : k ≠ a) :
    letI := Owner.oneOwnerStructure a
    (Set.range Owner.FiniteBasis.fiveVariableAxiom).ncard = 36 ∧
    (∀ i : Fin 36, (Owner.FiniteBasis.fiveVariableAxiom i).variableCount ≤ 5) ∧
    Equational.IsBasis (WinnerSet Role) (Set.range Owner.FiniteBasis.fiveVariableAxiom) ∧
    ∀ (T : Equational.Theory (Owner.Symbol Unit)) n,
      Equational.IsBasis (WinnerSet Role) T → Equational.HasVariableBound T n → 5 ≤ n :=
  ⟨Owner.FiniteBasis.FiveVariables.theory_ncard,
    fun i => Owner.FiniteBasis.FiveVariables.variable_bound _ ⟨i, rfl⟩,
    Owner.FiniteBasis.FiveVariables.isBasis_winnerSet three a k hka,
    Owner.FourVariableObstruction.variableBound_ge_five_winnerSet three a k hka⟩

/-- The six-element witness satisfies the entire four-variable theory and
fails a valid five-variable action law. -/
theorem owner_four_variable_obstruction :
    letI := Owner.fourStructure (Role := Unit)
    Fintype.card Owner.FourVariableObstruction.Carrier = 6 ∧
    (∀ e : Equational.Identity (Owner.Symbol Unit), e.variableCount ≤ 4 →
      e.Holds Owner.Four → e.Holds Owner.FourVariableObstruction.Carrier) ∧
    Owner.FourVariableObstruction.actionBand.Holds Owner.Four ∧
    ¬Owner.FourVariableObstruction.actionBand.Holds Owner.FourVariableObstruction.Carrier ∧
    Owner.FourVariableObstruction.actionBand.variableCount = 5 :=
  ⟨by decide, Owner.FourVariableObstruction.holds_of_variableCount_le,
    Owner.FourVariableObstruction.actionBand_holds, Owner.FourVariableObstruction.actionBand_fails,
    by decide⟩

/-- Two owners can agree on every observation while the complete operations differ. -/
theorem joint_owner_observation_failure (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ s t : Owner.Term Role (Fin 4), s.OwnersIn (fun r => r = a ∨ r = b) ∧
      t.OwnersIn (fun r => r = a ∨ r = b) ∧
      (∀ valuation : Fin 4 → WinnerSet Role,
        (a ∈ (s.eval valuation).val ↔ a ∈ (t.eval valuation).val) ∧
        (b ∈ (s.eval valuation).val ↔ b ∈ (t.eval valuation).val)) ∧ ¬s.Equivalent t :=
  by
    obtain ⟨s,t,hs,ht,ho,v,hfail⟩ := Results.joint_owner_observation_failure a b c hab hac hbc
    exact ⟨s,t,hs,ht,ho,fun he => hfail (he v)⟩

/-- The two-owner selective operation strictly extends the reset clone. -/
theorem strict_two_owner_policy (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∃ t : Reset.Term (Fin 3), ∀ v : Fin 3 → WinnerSet Role,
      t.eval v = (WinnerSet.choice a (WinnerSet.choice b (v 1) (v 2)) (v 1)).reset (v 0) :=
  Results.strict_two_owner_policy a b c hab hac hbc

/-- Owned choice and union generate the seven-law meet-distributive bisemilattice variety. -/
theorem choice_union_basis (three : Fin 3 ↪ Role) (owner : Role) :
    letI := Dissemilattice.winnerStructure owner
    Dissemilattice.theory.ncard = 7 ∧ Dissemilattice.theory.Finite ∧
    Equational.IsBasis (WinnerSet Role) Dissemilattice.theory ∧
    ∀ (M : Type v) [(Equational.language Dissemilattice.Symbol).Structure M],
      Equational.InVariety Dissemilattice.Symbol (WinnerSet Role) M ↔
        Nonempty M ∧ Dissemilattice.Laws (Dissemilattice.add (M := M)) Dissemilattice.mul :=
  by
    let _ := Dissemilattice.winnerStructure owner
    exact ⟨Dissemilattice.theory_ncard,Dissemilattice.theory_finite,
      Dissemilattice.basis_winner three owner,fun M _ => Dissemilattice.inVariety_winner_iff_laws three owner M⟩

/-- The core has no finite basis; every variable bound has a finite countermodel. -/
theorem core_nonfinite_basis [DecidableEq Role] [Finite Role] (three : Fin 3 ↪ Role) :
    letI := Equational.coreStructure Role
    ¬Equational.HasFiniteBasis (Equational.CoreSymbol Role) (WinnerSet Role) ∧
    ∀ n : ℕ, ∃ (B : Type u) (_str : (Equational.language (Equational.CoreSymbol Role)).Structure B),
      Nonempty B ∧ Finite B ∧
      (∀ e : Equational.Identity (Equational.CoreSymbol Role),
        e.variableCount ≤ n → e.Holds (WinnerSet Role) → e.Holds B) ∧
      ∃ e : Equational.Identity (Equational.CoreSymbol Role), e.Holds (WinnerSet Role) ∧ ¬e.Holds B :=
  by
    let _ := Equational.coreStructure Role
    refine ⟨Core.not_hasFiniteBasis three,?_⟩
    intro n
    obtain ⟨B,str,hne,hf,_,_,hfail,hsmall,_⟩ := (Results.core_nonfinite_basis three).1 n
    exact ⟨B,str,hne,hf,hsmall,hfail⟩

/-- Canonical reset tables have at most one prerequisite per source occurrence,
and a primitive binary term has size twice its leaf count minus one. -/
theorem reset_table_size [DecidableEq Var] (t : Reset.Term Var) :
    (∀ j, (t.table j).card ≤ t.occurrences j) ∧
    (∑ j ∈ t.varFinset, (t.table j).card) ≤ t.leafCount ∧
    t.size + 1 = 2 * t.leafCount :=
  ⟨t.card_table_le_occurrences,t.sum_card_table_le,t.size_add_one⟩

/-- Mathematical realizability and size, without exposing the Boolean checker. -/
theorem reset_table_realization [DecidableEq Var] [Fintype Var] (G : Reset.GuardTable Var) :
    G.WellFormed ↔ ∃ t : Reset.Term Var, t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * (∑ j, (G.guards j).card) :=
  (reset_table_synthesis G).2

/-- A realizable owner table has the stated compact primitive realization. -/
theorem owner_table_realization [DecidableEq Role] [DecidableEq Var] (T : Owner.GuardTable Var)
    (a k b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (positions : List Var) (hcan : T.Canonical) (hlisted : T.Listed positions)
    (realizable : ∃ t : Owner.Term Role Var, T.Realizes a t) :
    ∃ t : Owner.Term Role Var, T.Realizes a t ∧
      t.size ≤ 1 + T.entries.length * (10 * positions.length + 7) := by
  obtain ⟨recognizes,constructs,correct⟩ := owner_table_synthesis T a k b hka hkb hab positions hcan hlisted
  have success := constructs.mpr (recognizes.mpr realizable)
  cases output : T.synthesize a positions with
  | none => simp only [output,Option.isSome_none,Bool.false_eq_true] at success
  | some t => exact ⟨t,correct t output⟩

/-- Named winners and internal role permutations retain the unbounded
variable obstruction, witnessed by finite algebras in the actual signatures. -/
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
  ⟨FullBasis.not_hasFiniteBasis_public three, FullBasis.not_hasFiniteBasis_full three,
    FullBasis.finite_countermodels three⟩

/-- A general semantic connection between the core and its flat permutation
 envelope, in both public signatures. -/
theorem expanded_variety_envelope (three : Fin 3 ↪ Role) (M : Type v)
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
  Envelope.variety_iff three

theorem permutation_envelope_cardinality [DecidableEq Role] [Fintype Role] (M : Type v) [Fintype M] :
    Fintype.card (Envelope.Carrier Role M) =
      1 + (Fintype.card Role).factorial * Fintype.card M :=
  Envelope.card_carrier

end KFOL.Results.Algebra
