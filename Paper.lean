module

public import KFOL.Algebra
public import KFOL.Reductions.Circuits.LargeTables.Succinctness
public import KFOL.Strategic.ChoiceSupport
public import KFOL.Rounds.Scalar.Security
public import KFOL.Complexity.FullCompleteness
public import KFOL.Complexity.ResetSynthesisMachine
public import KFOL.Complexity.OwnerCountCompleteness
public import KFOL.Complexity.CircuitHardness
public import KFOL.Complexity.Canonicalization
public import KFOL.Complexity.OwnerObservationFrontend
public import KFOL.Complexity.CoreExtractionWord
public import KFOL.Rounds.Scalar.BooleanInfinite
public import KFOL.Rounds.Scalar.PairFullAbstraction
public import KFOL.Rounds.Scalar.Fragment
public import KFOL.Rounds.TwoPlayers.Support
public import KFOL.Rounds.TwoPlayers.Values
public import KFOL.Complexity.RawResetFrontend
public import KFOL.Complexity.RawSubsignatureCompleteness
public import KFOL.Reductions.Circuits
public import KFOL.Complexity.RawPairCompleteness
public import KFOL.Complexity.PolicyWordFrontend
public import KFOL.Complexity.PolicyCompleteness
public import KFOL.Rounds.Public.Nonconvex
public import KFOL.Rounds.Scalar.Reciprocal
public import KFOL.Rounds.Correspondence
public import KFOL.Reductions.RawPairs
public import KFOL.Reductions.Colouring
public import KFOL.Rounds.Values
public import KFOL.Rounds.TerminalErasure
public import KFOL.Rounds.ProductBeliefs
public import KFOL.Reductions.GuardedPair
public import KFOL.Complexity.GuardedPairCompleteness
public import KFOL.Complexity.OwnerWordFrontend
public import KFOL.Algebra.TwoPlayers.Kleene.Syntax
public import KFOL.Algebra.ViewOrders.Order
public import KFOL.Algebra.Semilattice
public import KFOL.Algebra.UnaryReset
public import KFOL.Algebra.PublicContexts
public import KFOL.Algebra.NoBooleanProduct
public import KFOL.Algebra.Atomic.Classification
public import KFOL.Algebra.Atomic.Binary
public import KFOL.Algebra.TwoPlayers.Coordinates
public import KFOL.Policies.Public
public import KFOL.Rounds.SequentialExistence
public import KFOL.Rounds.InformationFibers
public import KFOL.Complexity.OwnerSynthesisBridge
public import KFOL.Complexity.OwnerCheckMachine
public import KFOL.Algorithms.GuardWords
public import KFOL.Complexity.GuardSubset
public import KFOL.Algorithms.GuardRecord
public import KFOL.Algorithms.TermCode
public import KFOL.Algorithms.GuardDescriptor
public import KFOL.Algorithms.Normalization
public import KFOL.Algorithms.ResetEquation
public import KFOL.Owner
public import KFOL.Owner.Four
public import KFOL.Owner.Minimum
public import KFOL.Core
public import KFOL.Core.ChoiceUnion
public import KFOL.Complexity.Framing
public import KFOL.Complexity.BlockScan
public import KFOL.Complexity.DescriptorValidation
public import KFOL.Complexity.NormalizeMachine
public import KFOL.Complexity.RecognitionMachine
public import KFOL.Reset.Generator
public import KFOL.Strategic
public import KFOL.Complexity.ResetEquality
public import KFOL.Complexity.ResetUnionHardness
public import KFOL.Complexity.ResetUnionCompleteness
public import KFOL.Complexity.ResetUnionWordCompleteness
public import KFOL.Reductions.ResetUnionSize
public import KFOL.Congruences
public import KFOL.Congruences.UniformMatroid

/-!
# Kernel-checked paper claims

Each declaration repeats its complete mathematical proposition. The claim
inventory maps paper labels and prose to these statements and records any
clauses still missing from a partially migrated result.

Independent algebraic, equational and representation definitions are collected
under `KFOL/Definitions`. The separate Strategic definition module supplies
full profiles, whole-player deviations and subtree SPE; its canonical Nash
bridge does not enter the pure algebra. The Rounds module isolates the
commitment/disclosure protocol. `notes/formalization-definitions.md` indexes
both the project definitions and the small imported semantic interfaces.

Proof modules construct witnesses and algorithms below this file. Every public
statement has a guarded transitive axiom report; the whole-source audit also
checks private proof helpers and the independent algebra import boundary.
-/

@[expose] public section

namespace KFOL.Paper

universe u v w

/-- `sym:thm:pairs` (pair countervaluations). If an equation in the full public
signature, including winner constants and internal role permutations, fails,
then it fails with each variable assigned a singleton or a two-element set.
The two displayed winners may coincide. The result needs no finiteness or
three-role hypothesis, so in particular applies to the paper's finite roles. -/
theorem pair_countervaluations {Role : Type u} {Var : Type v} (s t : Term Role Var)
    (failure : ∃ valuation : Var → WinnerSet Role, s.eval valuation ≠ t.eval valuation) :
    ∃ valuation : Var → WinnerSet Role,
      (∀ x, ∃ a b : Role, (valuation x).val = {a, b}) ∧
      s.eval valuation ≠ t.eval valuation :=
  s.exists_pair_countervaluation t failure

/-- info: 'KFOL.Paper.pair_countervaluations' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.pair_countervaluations

/-- `sym:thm:optimal` (sharp full-language test domains). A fixed input domain
checks every equation at every finite arity exactly when it contains every
singleton and pair. These values form the unique least domain, of size
`K * (K + 1) / 2`. The embedding supplies three distinct roles; no global
lower bound on the role type is imposed on definitions or other theorems. -/
theorem optimal_test_domain {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
    (∀ D : Set (WinnerSet Role),
      (∀ (n : ℕ) (s t : Term Role (Fin n)),
        (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
          s.eval valuation = t.eval valuation) →
        ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
        ∀ a b : Role, WinnerSet.union (WinnerSet.singleton a) (WinnerSet.singleton b) ∈ D) ∧
    IsLeast {D : Set (WinnerSet Role) |
      ∀ (n : ℕ) (s t : Term Role (Fin n)),
        (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
          s.eval valuation = t.eval valuation) →
        ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation}
      {A | ∃ a b : Role, A.val = {a, b}} ∧
    Nat.card {A : WinnerSet Role // ∃ a b : Role, A.val = {a, b}} =
      Fintype.card Role * (Fintype.card Role + 1) / 2 :=
  ⟨KFOL.completeTestDomain_iff three, KFOL.isLeast_completeTestDomain three,
    KFOL.card_pairValues Role⟩

/-- info: 'KFOL.Paper.optimal_test_domain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.optimal_test_domain

/-- `gen:thm:core`, algebraic clauses. Idempotency is exactly the absence of
winner leaves and identity accumulated permutation at every input occurrence;
it is also exactly expressibility in the core. Extraction agrees at every
valuation and does not increase syntax size. `uniform_core_extraction_runtime`
certifies the original-input polynomial machine bound. -/
theorem idempotent_elimination {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (t : Term Role Var) :
    ((∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ↔
      ¬t.HasWinner ∧ ∀ x p, (x, p) ∈ t.inputOccurrences → p = 1) ∧
    ((∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ↔
      ∃ c : Term Role Var, c.IsCore ∧ ∀ valuation, c.eval valuation = t.eval valuation) ∧
    ((∀ A : WinnerSet Role, t.eval (fun _ => A) = A) →
      (t.pushRenames 1).IsCore ∧
      (∀ valuation : Var → WinnerSet Role, (t.pushRenames 1).eval valuation = t.eval valuation) ∧
      (t.pushRenames 1).size ≤ t.size) :=
  ⟨t.idempotent_iff_clean three, t.idempotent_iff_core three, t.idempotent_extraction three⟩

/-- info: 'KFOL.Paper.idempotent_elimination' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.idempotent_elimination

/-- The executable part of `gen:thm:core`: checked extraction succeeds exactly
on idempotent terms, and every successful output is a core expression with
equal semantics at every valuation and no larger syntax tree. The original-word
runtime is certified by `uniform_core_extraction_runtime`. -/
theorem checked_core_extraction {Role : Type u} {Var : Type v}
    [Fintype Role] [DecidableEq Role] (three : Fin 3 ↪ Role) (t : Term Role Var) :
    ((∃ c : Term Role Var, t.extractCore? 1 = some c) ↔
      ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧
    (∀ c : Term Role Var, t.extractCore? 1 = some c →
      c.IsCore ∧ (∀ valuation : Var → WinnerSet Role, c.eval valuation = t.eval valuation) ∧
        c.size ≤ t.size) :=
  ⟨t.extractCore?_isSome_iff three, t.extractCore?_correct⟩

/-- info: 'KFOL.Paper.checked_core_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.checked_core_extraction

/-- `view:thm:view`. Contexts in the public signature identify exactly the
values with the same membership bit and other-player singleton tests. These
are exactly the fibers of the concrete view, whose quotient has `K + 1` classes. -/
theorem player_views {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) (k : Role) :
    (∀ A B : WinnerSet Role,
      (∀ (n : ℕ) (t : Term Role (Option (Fin n))), t.IsPublic →
        ∀ parameters : Fin n → WinnerSet Role,
        (k ∈ (t.eval (fun x => x.elim A parameters)).val ↔
          k ∈ (t.eval (fun x => x.elim B parameters)).val)) ↔
      ((k ∈ A.val ↔ k ∈ B.val) ∧
        ∀ r, r ≠ k → (A = WinnerSet.singleton r ↔ B = WinnerSet.singleton r))) ∧
    (∀ A B : WinnerSet Role, WinnerSet.view k A = WinnerSet.view k B ↔
      ((k ∈ A.val ↔ k ∈ B.val) ∧
        ∀ r, r ≠ k → (A = WinnerSet.singleton r ↔ B = WinnerSet.singleton r))) ∧
    Function.Surjective (WinnerSet.view k) ∧
    Nat.card (Quotient (Setoid.ker (WinnerSet.view k))) = Fintype.card Role + 1 :=
  ⟨Term.polynomial_contextual_iff_sameView k, WinnerSet.view_eq_view_iff k,
    WinnerSet.view_surjective three k, WinnerSet.card_quotient_view three k⟩

/-- info: 'KFOL.Paper.player_views' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.player_views

/-- `view:cor:product`. The canonical coordinate map is an injective
homomorphism, onto each factor, from the `2^K - 1` winner sets into `K` factors
of size `K + 1`. The homomorphism equation covers every public reduct term. -/
theorem public_subdirect_representation {Role : Type u} [Fintype Role]
    (three : Fin 3 ↪ Role) :
    Nat.card (WinnerSet Role) = 2 ^ Fintype.card Role - 1 ∧
    Function.Injective (fun A : WinnerSet Role => fun k => WinnerSet.view k A) ∧
    (∀ k : Role, Function.Surjective (WinnerSet.view k) ∧
      Nat.card (PlayerView k) = Fintype.card Role + 1) ∧
    (∀ (Var : Type v) (t : Term Role Var), t.IsPublic → ∀ (k : Role)
      (valuation : Var → WinnerSet Role),
      WinnerSet.view k (t.eval valuation) =
        PlayerView.eval three k t (fun x => WinnerSet.view k (valuation x))) :=
  ⟨WinnerSet.card_winnerSet, WinnerSet.views_injective,
    fun k => ⟨WinnerSet.view_surjective three k, PlayerView.card k⟩,
    fun _ _ ht => ht.view_eval three⟩

/-- info: 'KFOL.Paper.public_subdirect_representation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_subdirect_representation

/-- `gen:cor:views`. Every idempotent full-language operation descends to each
player view. The views give an irredundant subdirect representation: the joint
map is injective, each factor is onto and has `K + 1` states, and omitting any
one coordinate loses a distinction visible precisely there. -/
theorem intrinsic_player_views {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
    (∀ (Var : Type v) (t : Term Role Var),
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) → ∀ (k : Role)
      (valuation : Var → WinnerSet Role),
      WinnerSet.view k (t.eval valuation) =
        PlayerView.eval three k t (fun x => WinnerSet.view k (valuation x))) ∧
    Function.Injective (fun A : WinnerSet Role => fun k => WinnerSet.view k A) ∧
    (∀ k : Role, Function.Surjective (WinnerSet.view k) ∧
      Nat.card (PlayerView k) = Fintype.card Role + 1) ∧
    (∀ k : Role, ∃ A B : WinnerSet Role, A ≠ B ∧
      (∀ j, j ≠ k → WinnerSet.view j A = WinnerSet.view j B) ∧
        WinnerSet.view k A ≠ WinnerSet.view k B) :=
  ⟨fun _ t hd => t.view_eval_of_idempotent three hd,
    WinnerSet.views_injective,
    fun k => ⟨WinnerSet.view_surjective three k, PlayerView.card k⟩,
    WinnerSet.views_irredundant three⟩

/-- info: 'KFOL.Paper.intrinsic_player_views' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.intrinsic_player_views

/-- `gen:cor:trace`. On ambiguous inputs, idempotent operations are exactly
nonempty finite joins of arguments. Supports classify these restrictions,
realize every join, and preserve projections and substitution: these are the
explicit laws of the surjective clone homomorphism. The remaining conjuncts
exclude NU and Mal'cev terms and assert essentiality and regular identities. -/
theorem semilattice_trace {Role : Type u} (three : Fin 3 ↪ Role) :
    (∀ (n : ℕ) (t : Term Role (Fin n)),
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) →
      t.vars.Nonempty ∧ ∀ valuation : Fin n → WinnerSet Role,
        (∀ x, WinnerSet.Ambiguous (valuation x)) → ∀ r,
        (r ∈ (t.eval valuation).val ↔ ∃ x ∈ t.vars, r ∈ (valuation x).val)) ∧
    (∀ (n : ℕ) (s t : Term Role (Fin n)),
      (∀ A : WinnerSet Role, s.eval (fun _ => A) = A) →
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) →
      ((∀ valuation : Fin n → WinnerSet Role,
        (∀ x, WinnerSet.Ambiguous (valuation x)) → s.eval valuation = t.eval valuation) ↔
        s.vars = t.vars)) ∧
    (∀ (n : ℕ) (S : Finset (Fin n)), S.Nonempty →
      ∃ t : Term Role (Fin n), t.IsCore ∧ t.vars = S ∧
        ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧
    (∀ (n : ℕ) (i : Fin n),
      (Term.var i : Term Role (Fin n)).vars = {i} ∧
      ∀ valuation : Fin n → WinnerSet Role, (Term.var i).eval valuation = valuation i) ∧
    (∀ (m n : ℕ) (t : Term Role (Fin m)) (replacement : Fin m → Term Role (Fin n)),
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) →
      (∀ x (A : WinnerSet Role), (replacement x).eval (fun _ => A) = A) →
      ((∀ A : WinnerSet Role, (t.subst replacement).eval (fun _ => A) = A) ∧
        (t.subst replacement).vars = t.vars.biUnion (fun x => (replacement x).vars) ∧
        ∀ valuation : Fin n → WinnerSet Role,
          (t.subst replacement).eval valuation =
            t.eval (fun x => (replacement x).eval valuation))) ∧
    (∀ (n : ℕ), 0 < n → ∀ t : Term Role (Fin n),
      ¬(∀ A B : WinnerSet Role, ∀ i : Fin n,
        t.eval (Function.update (fun _ => A) i B) = A)) ∧
    (∀ t : Term Role (Fin 3),
      ¬((∀ A B : WinnerSet Role, t.eval (fun i => if i = 0 then A else B) = A) ∧
        (∀ A B : WinnerSet Role, t.eval (fun i => if i = 2 then B else A) = B))) ∧
    (∀ (n : ℕ) (t : Term Role (Fin n)), t.IsCore → ∀ x ∈ t.vars,
      ∃ v w : Fin n → WinnerSet Role,
        (∀ y, y ≠ x → v y = w y) ∧ t.eval v ≠ t.eval w) ∧
    (∀ (n : ℕ) (s t : Term Role (Fin n)), s.IsCore → t.IsCore →
      (∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation) →
      s.vars = t.vars) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, Term.not_nearUnanimity three, Term.not_malcev three, ?_, ?_⟩
  · intro n t ht
    exact ⟨t.vars_nonempty_of_idempotent three ht, t.eval_mem_iff_of_idempotent three ht⟩
  · intro n s t hs ht
    exact Term.equal_on_ambiguous_iff_vars_eq_of_idempotent three s t hs ht
  · intro n S hS
    obtain ⟨t, ht, he⟩ := Term.exists_core_vars three S hS
    exact ⟨t, ht, he, ht.eval_diagonal⟩
  · intro n i
    exact ⟨rfl, fun _ => rfl⟩
  · intro m n t replacement ht hr
    exact ⟨t.idempotent_subst replacement ht hr, t.vars_subst replacement,
      t.eval_subst replacement⟩
  · intro n t ht x hx
    exact ht.essential three x hx
  · intro n s t hs ht he
    exact Term.vars_eq_of_core_identity three hs ht he

/-- info: 'KFOL.Paper.semilattice_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.semilattice_trace

/-- `gen:thm:source`. Disjoint output requirements are witnessed simultaneously
by one actual leaf and its accumulated permutation. If the family has two
distinct indices, that same leaf is a variable occurrence. No finiteness or
three-role assumption is needed. -/
theorem common_source {Role : Type u} {Var : Type v} {Index : Type w}
    (t : Term Role Var) (valuation : Index → Var → WinnerSet Role)
    (regions : Index → Set Role)
    (hdisjoint : Pairwise fun i j => Disjoint (regions i) (regions j))
    (hfits : ∀ i, (t.eval (valuation i)).val ⊆ regions i) :
    ∃ (leaf : Role ⊕ Var) (p : Equiv.Perm Role), (leaf, p) ∈ t.sourceOccurrences ∧
      (∀ i, (WinnerSet.rename p (leaf.elim WinnerSet.singleton (valuation i))).val ⊆ regions i) ∧
      ((∃ i j : Index, i ≠ j) →
        ∃ x : Var, leaf = .inr x ∧ (x, p) ∈ t.inputOccurrences) :=
  t.exists_common_source_with_input_clause valuation regions hdisjoint hfits

/-- info: 'KFOL.Paper.common_source' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.common_source

/-- Main prose following `gen:thm:source`: repeated entries in every input
triple force a repeated atomic output. Atomicity is assumed only for the three
evaluations in question, not globally for the term. -/
theorem atomic_repeated_triples {Role : Type u} {Var : Type v} (t : Term Role Var)
    (valuation : Fin 3 → Var → Role)
    (hrepeat : ∀ x, valuation 0 x = valuation 1 x ∨ valuation 0 x = valuation 2 x ∨
      valuation 1 x = valuation 2 x)
    (out : Fin 3 → Role)
    (houtputs : ∀ i, t.eval (fun x => WinnerSet.singleton (valuation i x)) =
      WinnerSet.singleton (out i)) :
    out 0 = out 1 ∨ out 0 = out 2 ∨ out 1 = out 2 :=
  t.atomic_preserves_repeat_triple valuation hrepeat out houtputs

/-- info: 'KFOL.Paper.atomic_repeated_triples' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.atomic_repeated_triples

/-- Main prose following `gen:thm:source`: no full-language term returns the
second argument for control atom a and the third for control atom b, for all
atomic arguments, when a and b are distinct. -/
theorem no_atomic_if_then_else {Role : Type u} (three : Fin 3 ↪ Role)
    (a b : Role) (hab : a ≠ b) (t : Term Role (Fin 3)) :
    ¬((∀ y z : Role, t.eval (fun i => WinnerSet.singleton
        (if i = 0 then a else if i = 1 then y else z)) = WinnerSet.singleton y) ∧
      (∀ y z : Role, t.eval (fun i => WinnerSet.singleton
        (if i = 0 then b else if i = 1 then y else z)) = WinnerSet.singleton z)) :=
  t.not_atom_ifThenElse three a b hab

/-- info: 'KFOL.Paper.no_atomic_if_then_else' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.no_atomic_if_then_else

/-- `view:thm:tests`. The public reduct is tested at every finite arity exactly
by domains containing every atom and an ambiguous value omitting each role. -/
theorem reduct_test_domains {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role)
    (D : Set (WinnerSet Role)) :
    (∀ (n : ℕ) (s t : Term Role (Fin n)), s.IsPublic → t.IsPublic →
      (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
        s.eval valuation = t.eval valuation) →
      ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
    (∀ r, WinnerSet.singleton r ∈ D) ∧
      (∀ k, ∃ F ∈ D, WinnerSet.Ambiguous F ∧ k ∉ F.val) :=
  completePublicTestDomain_iff three D

/-- info: 'KFOL.Paper.reduct_test_domains' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reduct_test_domains

/-- `view:cor:optimal`. The sharp minimum is six with three roles, and K+2
with at least four. Leastness states both the bound and an attaining domain. -/
theorem minimum_reduct_test_domain {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
    IsLeast {m : ℕ | ∃ D : Finset (WinnerSet Role),
      (∀ (n : ℕ) (s t : Term Role (Fin n)), s.IsPublic → t.IsPublic →
        (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
          s.eval valuation = t.eval valuation) →
        ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation) ∧ D.card = m}
      (if Fintype.card Role = 3 then 6 else Fintype.card Role + 2) ∧
    (Fintype.card Role = 3 → ∃ D : Finset (WinnerSet Role),
      (∀ (n : ℕ) (s t : Term Role (Fin n)), s.IsPublic → t.IsPublic →
        (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
          s.eval valuation = t.eval valuation) →
        ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation) ∧
      D.card = 6 ∧ ∀ A, A ∈ D ↔ ∃ a b, A.val = {a, b}) ∧
    (∀ four : Fin 4 ↪ Role, ∃ D : Finset (WinnerSet Role),
      (∀ (n : ℕ) (s t : Term Role (Fin n)), s.IsPublic → t.IsPublic →
        (∀ valuation : Fin n → WinnerSet Role, (∀ x, valuation x ∈ D) →
          s.eval valuation = t.eval valuation) →
        ∀ valuation : Fin n → WinnerSet Role, s.eval valuation = t.eval valuation) ∧
      D.card = Fintype.card Role + 2 ∧ ∀ A, A ∈ D ↔
        (∃ r, A = WinnerSet.singleton r) ∨ A.val = {four 0, four 1} ∨ A.val = {four 2, four 3}) := by
  refine ⟨public_domain_minimum three, ?_, exists_public_domain_card_add_two three⟩
  intro hc
  exact ⟨pairDomain Role, completePublicTestDomain_pairDomain three,
    by simp [card_pairDomain, hc], mem_pairDomain⟩

/-- info: 'KFOL.Paper.minimum_reduct_test_domain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.minimum_reduct_test_domain

/-- `gen:thm:idem-domain`. For ambiguous domains, diagonal certification is
exactly omission of every role and separation of all incidence vectors. The
minimum among all domains, including mixed ones, is three for K=3 and
ceil(log₂(K+1)) otherwise, attained with ambiguous values alone. -/
theorem idempotency_certificates {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role) :
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
  ⟨certifiesIdempotency_iff three, card_optimal_idempotency_domain_lower three,
    exists_optimal_idempotency_domain three⟩

/-- info: 'KFOL.Paper.idempotency_certificates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.idempotency_certificates

/-- `reset:lem:selection` in full. Selection is defined independently by the
positive recursion displayed here; it computes the exact union of contributions
on mixed inputs, is monotone, always includes the root, and ignores an input's
own status when deciding whether that input contributes. -/
theorem reset_selection {Role : Type u} {Var : Type v} :
    (∀ (t : Reset.Term Var) (valuation : Var → WinnerSet Role),
      (t.eval valuation).Ambiguous ↔ (valuation t.root).Ambiguous) ∧
    (∀ (i j : Var) (B : Set Var), Reset.Term.Selected (.var i) B j ↔ j = i) ∧
    (∀ (s t : Reset.Term Var) (B : Set Var) (j : Var),
      (Reset.Term.step s t).Selected B j ↔
        t.Selected B j ∨ (t.root ∈ B ∧ s.Selected B j)) ∧
    (∀ (t : Reset.Term Var) (valuation : Var → WinnerSet Role) (r : Role),
      r ∈ (t.eval valuation).val ↔
        ∃ j, t.Selected {i | (valuation i).Ambiguous} j ∧ r ∈ (valuation j).val) ∧
    (∀ (t : Reset.Term Var) (B C : Set Var), B ⊆ C →
      ∀ j, t.Selected B j → t.Selected C j) ∧
    (∀ (t : Reset.Term Var) (B : Set Var), t.Selected B t.root) ∧
    (∀ (t : Reset.Term Var) (B C : Set Var) (j : Var),
      (∀ i, i ≠ j → (i ∈ B ↔ i ∈ C)) → (t.Selected B j ↔ t.Selected C j)) :=
  ⟨Reset.Term.ambiguous_eval, Reset.Term.selected_var, Reset.Term.selected_step,
    Reset.Term.mem_eval, fun t _ _ h => t.selected_mono h,
    Reset.Term.selected_root, Reset.Term.selected_self_independent⟩

/-- info: 'KFOL.Paper.reset_selection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_selection

/-- Reset's main-text definition and its expansion into actual owned choices.
The expansion works for every term and every mixed valuation. -/
theorem reset_definability {Role : Type u} [Fintype Role] (three : Fin 3 ↪ Role)
    {Var : Type v} :
    (∀ A B : WinnerSet Role,
      (B.Ambiguous → A.reset B = A.union B) ∧
      (∀ r, B = WinnerSet.singleton r → A.reset B = B)) ∧
    (∀ t : Reset.Term Var, ∃ s : Term Role Var, s.IsCore ∧
      ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) := by
  classical
  refine ⟨fun A B => ⟨WinnerSet.reset_of_ambiguous A B, ?_⟩, ?_⟩
  · rintro r rfl
    exact WinnerSet.reset_singleton A r
  · intro t
    let roles : List Role := Finset.univ.toList
    exact ⟨t.compile three roles, t.isCore_compile three roles,
      t.eval_compile three roles (by simp [roles])⟩

/-- info: 'KFOL.Paper.reset_definability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_definability

/-- `reset:thm:three`, semantic clauses: canonical table equality, the fixed
three-value chain test, and the common identity theory for every role set with
three distinct roles. `reset_binary_equation_checker` supplies the complete
original-word polynomial checker. -/
theorem reset_tables_semantics {Role : Type u} {Var : Type v} [DecidableEq Var]
    (three : Fin 3 ↪ Role) (s t : Reset.Term Var) :
    ((∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
      s.table = t.table) ∧
    ((∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
      ∀ valuation : Var → WinnerSet Role,
        (∀ i, ∃ k : Fin 3, valuation i = Reset.chainValue three k) →
          s.eval valuation = t.eval valuation) ∧
    (∀ {Role' : Type w} (_three' : Fin 3 ↪ Role'),
      (∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
        ∀ valuation : Var → WinnerSet Role', s.eval valuation = t.eval valuation) ∧
    (∀ i j : Fin 3, (Reset.chainValue three i).reset (Reset.chainValue three j) =
      Reset.chainValue three (if j = 0 then 0 else max i j)) :=
  ⟨s.eval_eq_iff_table t three, s.eval_eq_iff_chain t three,
    (fun three' => s.eval_eq_iff_roles t three three'), Reset.reset_chainValue three⟩

/-- info: 'KFOL.Paper.reset_tables_semantics' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_tables_semantics

/-- Actual term substitution obeys the root, evaluation and explicit canonical
minimal-guard composition laws (`reset:eq:substitution`). This certifies the
formula's semantics; complexity bounds belong to the machine branch. -/
theorem reset_substitution {Var : Type v} {Var' : Type w} [DecidableEq Var] [DecidableEq Var']
    (t : Reset.Term Var) (inner : Var → Reset.Term Var') :
    Reset.Term.root (t.subst inner) = (inner t.root).root ∧
    (∀ {Role : Type u} (valuation : Var' → WinnerSet Role),
      Reset.Term.eval (t.subst inner) valuation =
        t.eval (fun i => (inner i).eval valuation)) ∧
    (∀ j, Reset.Term.table (t.subst inner) j = Reset.Term.minimize
      (t.varFinset.biUnion (fun i => (t.table i).biUnion (fun A =>
        ((inner i).table j).image (fun C => A.image (fun k => (inner k).root) ∪ C))))) :=
  ⟨t.root_subst inner, t.eval_subst inner, t.table_subst inner⟩

/-- info: 'KFOL.Paper.reset_substitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_substitution

/-- `reset:thm:basis` in full: validity is exactly equational derivability from
R1--R6, spelled out as identities below. The family has exactly six members.
The proof includes arbitrary-model completeness; no outside basis theorem is
assumed. Variables and role types need not be finite. -/
theorem reset_basis {Role : Type u} {Var : Type v} (three : Fin 3 ↪ Role)
    (s t : Reset.Term Var) :
    let x : Reset.Term (Fin 3) := .var 0
    let y : Reset.Term (Fin 3) := .var 1
    let z : Reset.Term (Fin 3) := .var 2
    let ax : Fin 6 → Equational.Identity Reset.Symbol := fun i =>
      if i = 0 then ⟨3, Reset.Term.step x x, x⟩
      else if i = 1 then ⟨3, Reset.Term.step (Reset.Term.step x y) x, Reset.Term.step y x⟩
      else if i = 2 then ⟨3, Reset.Term.step (Reset.Term.step x y) y, Reset.Term.step x y⟩
      else if i = 3 then
        ⟨3, Reset.Term.step x (Reset.Term.step (Reset.Term.step x y) z),
          Reset.Term.step x (Reset.Term.step y z)⟩
      else if i = 4 then
        ⟨3, Reset.Term.step (Reset.Term.step (Reset.Term.step x y) z) y,
          Reset.Term.step (Reset.Term.step x z) y⟩
      else ⟨3, Reset.Term.step x (Reset.Term.step y z),
        Reset.Term.step y (Reset.Term.step x z)⟩
    ((∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
      Equational.Derives (Set.range ax) s t) ∧ Nat.card (Set.range ax) = 6 := by
  change ((∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
    Equational.Derives Reset.basis s t) ∧ Nat.card Reset.basis = 6
  exact ⟨(Reset.derives_iff_eval_eq three s t).symm, Reset.card_basis⟩

/-- info: 'KFOL.Paper.reset_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_basis

/-- `reset:thm:anti` in full. The bijection is on actual semantic term
functions, with arbitrary unused ambient positions. Its canonical family is
exactly the sets selected in their entirety on their own ambiguity status.
The finite ground and unique root are recovered as part of the correspondence. -/
theorem reset_antimatroids {Role : Type u} {Var : Type v} [DecidableEq Var]
    (three : Fin 3 ↪ Role) :
    ∃ e : {f : (Var → WinnerSet Role) → WinnerSet Role //
        ∃ t : Reset.Term Var, ∀ valuation, f valuation = t.eval valuation} ≃
      Reset.RootedAntimatroid Var,
      ∀ t : Reset.Term Var,
        let F := e ⟨t.eval, ⟨t, fun _ => rfl⟩⟩
        F.ground = t.varFinset ∧ F.root = t.root ∧
        (∀ A : Finset Var, A ∈ F.feasible ↔
          A ⊆ t.varFinset ∧ ∀ j ∈ A, t.Selected (A : Set Var) j) ∧
        (∀ (B : Set Var) j, F.Ready B j ↔ t.Selected B j) := by
  refine ⟨Reset.termFunctionEquiv three, ?_⟩
  intro t
  dsimp only
  rw [Reset.termFunctionEquiv_apply]
  exact ⟨t.antimatroid_ground, t.antimatroid_root,
    fun A => by rw [t.feasible_antimatroid]; rfl, t.ready_antimatroid⟩

/-- info: 'KFOL.Paper.reset_antimatroids' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_antimatroids

/-- `reset:eq:family-product`: the induced family operation for a reset node.
Grounds may overlap and the same variable may occur repeatedly in both terms. -/
theorem reset_family_product {Var : Type v} [DecidableEq Var] (s t : Reset.Term Var) :
    (Reset.Term.step s t).feasible =
      {D : Finset Var | D = ∅ ∨ ∃ A ∈ s.feasible, ∃ C ∈ t.feasible,
        C.Nonempty ∧ D = A ∪ C} := by
  change (Reset.Term.step s t).feasible = Reset.familyProduct s.feasible t.feasible
  rw [← s.feasible_antimatroid, ← t.feasible_antimatroid,
    ← Reset.Term.feasible_antimatroid, Reset.Term.antimatroid_step]
  rfl

/-- info: 'KFOL.Paper.reset_family_product' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_family_product

/-- The mathematical realizability and primitive-tree size clauses of
`reset:thm:synthesis`. Every candidate-table condition is repeated here.
Constructibility is independently defined by fresh enabled additions.
The native polynomial synthesis bound is proved in `reset_synthesis_runtime`. -/
theorem reset_table_realizability {Var : Type v} [DecidableEq Var] [Fintype Var]
    (G : Reset.GuardTable Var) :
    ((∀ j, ∀ A ∈ G.guards j, ∀ B ∈ G.guards j, A ⊆ B → A = B) ∧
      G.guards G.root = {∅} ∧
      (∀ j, ∅ ∈ G.guards j → j = G.root) ∧
      (∀ j, ∀ A ∈ G.guards j, j ∉ A) ∧
      (∀ j, ∀ A ∈ G.guards j, G.Constructible A)) ↔
    ∃ t : Reset.Term Var, t.root = G.root ∧ t.table = G.guards ∧
      t.size ≤ 1 + 2 * Fintype.card Var * (∑ j, (G.guards j).card) := by
  change G.WellFormed ↔ _
  exact ⟨G.exists_term_bounded, fun ⟨t, hr, ht, _⟩ =>
    G.wellFormed_iff_realizable.mpr ⟨t, hr, ht⟩⟩

/-- info: 'KFOL.Paper.reset_table_realizability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_table_realizability

/-- The executable table recognizer accepts exactly actual realizable
canonical tables. Its greedy prerequisite test is complete after at most
one round per target position, including the empty target. -/
theorem reset_table_recognition {Var : Type v} [DecidableEq Var] [Fintype Var]
    (G : Reset.GuardTable Var) :
    (G.check = true ↔ ∃ t : Reset.Term Var, t.root = G.root ∧ t.table = G.guards) ∧
    (∀ A : Finset Var, G.reached A A.card = A ↔ G.Constructible A) := by
  refine ⟨G.check_eq_true.trans G.wellFormed_iff_realizable, ?_⟩
  intro A
  simpa only [Reset.GuardTable.constructibleCheck, decide_eq_true_eq] using
    G.constructibleCheck_eq_true A

/-- info: 'KFOL.Paper.reset_table_recognition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_table_recognition

/-- The local prerequisite condition `reset:eq:complete`, with precisely its
self-exclusion hypothesis and no assumed realizability certificate. -/
theorem reset_table_local_completeness {Var : Type v} [DecidableEq Var]
    (G : Reset.GuardTable Var) (hself : ∀ j, ∀ A ∈ G.guards j, j ∉ A) :
    (∀ j, ∀ A ∈ G.guards j, G.Constructible A) ↔
      ∀ j, ∀ A ∈ G.guards j, ∀ k ∈ A, ∃ B ∈ G.guards k, B ⊆ A :=
  G.all_constructible_iff_local hself

/-- info: 'KFOL.Paper.reset_table_local_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_table_local_completeness

/-- Executable compact synthesis: success is equivalent to the existence of
an actual realizing term, and every returned term has the requested root and
canonical tables with the stated bound on primitive syntax occurrences.
Only this algorithm requires an ordering of the finite input positions. -/
theorem reset_table_synthesis {Var : Type v} [LinearOrder Var] [Fintype Var]
    (G : Reset.GuardTable Var) :
    (G.synthesize.isSome = true ↔
      ∃ t : Reset.Term Var, t.root = G.root ∧ t.table = G.guards) ∧
    (∀ t : Reset.Term Var, G.synthesize = some t →
      t.root = G.root ∧ t.table = G.guards ∧
        t.size ≤ 1 + 2 * Fintype.card Var * (∑ j, (G.guards j).card)) :=
  ⟨G.synthesize_isSome_iff.trans G.wellFormed_iff_realizable,
    fun _ ht => G.synthesize_spec ht⟩

/-- info: 'KFOL.Paper.reset_table_synthesis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_table_synthesis

/-- The traversal claimed in the canonical-table prose: one raw entry per
actual variable occurrence, with independently correct root and guards.
Normalization gives exactly the previously defined canonical tables. -/
theorem reset_guard_extraction {Var : Type v} [DecidableEq Var] (t : Reset.Term Var) :
    t.collectGuards.1 = t.root ∧ t.guardEntries.length = t.leafCount ∧
    t.size + 1 = 2 * t.leafCount ∧
    (∀ j, (t.guardEntries.filter (fun p => p.1 = j)).length = t.occurrences j ∧
      t.guards j = ((t.guardEntries.filter (fun p => p.1 = j)).map Prod.snd).toFinset ∧
      t.table j = Reset.Term.minimize
        (((t.guardEntries.filter (fun p => p.1 = j)).map Prod.snd).toFinset)) ∧
    (∀ j A, (j, A) ∈ t.guardEntries →
      j ∈ t.varFinset ∧ A ⊆ t.varFinset ∧ A.card + 1 ≤ t.leafCount) := by
  refine ⟨t.collectGuards_root, t.length_guardEntries, t.size_add_one, ?_, ?_⟩
  · intro j
    refine ⟨?_, t.guards_eq_entries j, t.table_eq_entries j⟩
    simpa only [List.countP_eq_length_filter] using t.countP_guardEntries j
  · intro j A hA
    have hg := (t.mem_guardEntries j A).mp hA
    exact ⟨t.mem_varFinset_of_mem_guards j hg,
      t.subset_varFinset_of_mem_guards j hg, t.card_guard_add_one_le j hg⟩

/-- info: 'KFOL.Paper.reset_guard_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_guard_extraction

/-- Table-size clauses of the main reset prose, before and after minimization.
The description counts one root label, each output label and its prerequisite
labels. `reset_synthesis_runtime` and `reset_synthesis_output` certify the
complete machine runtime and original primitive-tree output.
All sums range over actual support; unused ambient positions have empty tables. -/
theorem reset_table_size {Var : Type v} [DecidableEq Var] (t : Reset.Term Var) :
    (∀ j, (t.table j).card ≤ (t.guards j).card ∧
      (t.guards j).card ≤ t.occurrences j) ∧
    (∀ j, j ∉ t.varFinset → t.table j = ∅) ∧
    (∑ j ∈ t.varFinset, (t.guards j).card) ≤ t.leafCount ∧
    (∑ j ∈ t.varFinset, (t.table j).card) ≤ t.leafCount ∧
    (1 + (t.guardEntries.map (fun p => p.2.card + 1)).sum ≤ 1 + t.leafCount ^ 2) ∧
    (1 + ∑ j ∈ t.varFinset, ∑ A ∈ t.table j, (A.card + 1) ≤
      1 + t.varFinset.card * t.leafCount) ∧
    (1 + ∑ j ∈ t.varFinset, ∑ A ∈ t.table j, (A.card + 1) ≤ 1 + t.leafCount ^ 2) ∧
    t.varFinset.card ≤ t.leafCount := by
  refine ⟨?_, t.table_eq_empty_of_not_mem, t.sum_card_guards_le, t.sum_card_table_le,
    t.guardEntries_description_le, t.table_description_le, t.table_description_quadratic,
    t.card_varFinset_le_leafCount⟩
  intro j
  exact ⟨Finset.card_le_card (Finset.filter_subset _ _), t.card_guards_le_occurrences j⟩

/-- info: 'KFOL.Paper.reset_table_size' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_table_size

/-- The first machine component of the reset table algorithms: the actual
word program is polynomial-time in ComplexityLib's Turing-machine model,
uniformly in input width. Its exact bitset codec and its connection to the
independent guard-enabling predicate are repeated here. This does not assert
polynomial time for the whole table recognizer or synthesizer. -/
theorem reset_guard_subset_machine :
    Turing.MultiTapeTM.ComputableInPolyTime (fun v : Fin 2 → List Bool =>
      Algorithms.GuardWords.subsetWord (v 0) (v 1))
        (Turing.MultiTapeTM.encPi Turing.MultiTapeTM.encBits) Turing.MultiTapeTM.encBits ∧
    (∀ (n : ℕ) (A : Finset (Fin n)),
      (Algorithms.Bitset.encode A).length = n ∧
      ∀ word : List Bool, Algorithms.Bitset.decode n word = some A ↔
        word = Algorithms.Bitset.encode A) ∧
    (∀ (n : ℕ) (A B : Finset (Fin n)),
      Algorithms.GuardWords.subsetWord (Algorithms.Bitset.encode A)
        (Algorithms.Bitset.encode B) = [true] ↔ A ⊆ B) ∧
    (∀ a b : List Bool, Algorithms.GuardWords.subsetWord a b = [true] ↔
      a.length = b.length ∧ ∀ i < a.length,
        Algorithms.GuardWords.readBit a i = true → Algorithms.GuardWords.readBit b i = true) ∧
    (∀ (n : ℕ) (G : Reset.GuardTable (Fin n)) (A : Finset (Fin n)) (j : Fin n),
      G.Enabled (A : Set (Fin n)) j ↔ ∃ C ∈ G.guards j,
        Algorithms.GuardWords.subsetWord (Algorithms.Bitset.encode C)
          (Algorithms.Bitset.encode A) = [true]) :=
  ⟨Complexity.GuardSubset.subsetFn_polyTime,
    fun _ A => ⟨Algorithms.Bitset.length_encode A, fun w => Algorithms.Bitset.decode_eq_some_iff w A⟩,
    fun _ A B => Algorithms.GuardWords.subsetWord_encode A B,
    Algorithms.GuardWords.subsetWord_correct, fun _ G A j => Algorithms.enabled_iff_subsetWord G A j⟩

/-- info: 'KFOL.Paper.reset_guard_subset_machine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_guard_subset_machine

/-- Compact indexing uses exactly the actual support. No bound on the values
or ambient range of variable names is assumed. Compression and expansion are
inverse on covered sets and preserve the prerequisite-subset word test. -/
theorem reset_support_indexing {Var : Type v} [DecidableEq Var] (t : Reset.Term Var) :
    let D := Algorithms.SupportIndex.labels t
    D.Nodup ∧ D.toFinset = t.varFinset ∧ D.length = t.varFinset.card ∧
    D.length ≤ t.leafCount ∧
    (∃ e : Fin D.length ≃ {j // j ∈ t.varFinset}, ∀ i, (e i).val = D.get i) ∧
    (∀ j (i : Fin D.length), Algorithms.SupportIndex.locate D j = some i ↔ D.get i = j) ∧
    (∀ A : Finset Var, A ⊆ t.varFinset →
      Algorithms.SupportIndex.expand D (Algorithms.SupportIndex.compress D A) = A) ∧
    (∀ A : Finset (Fin D.length),
      Algorithms.SupportIndex.compress D (Algorithms.SupportIndex.expand D A) = A) ∧
    (∀ A B : Finset Var, A ⊆ t.varFinset → (
      Algorithms.GuardWords.subsetWord
        (Algorithms.Bitset.encode (Algorithms.SupportIndex.compress D A))
        (Algorithms.Bitset.encode (Algorithms.SupportIndex.compress D B)) = [true] ↔ A ⊆ B)) := by
  dsimp only
  refine ⟨Algorithms.SupportIndex.labels_nodup t, Algorithms.SupportIndex.labels_toFinset t,
    Algorithms.SupportIndex.length_labels t, Algorithms.SupportIndex.length_labels_le t,
    Algorithms.SupportIndex.exists_support_equiv t, ?_, ?_, ?_, ?_⟩
  · exact fun j i => Algorithms.SupportIndex.locate_eq_some_iff _
      (Algorithms.SupportIndex.labels_nodup t) j i
  · intro A hA
    exact Algorithms.SupportIndex.expand_compress _ A (by
      simpa only [Algorithms.SupportIndex.labels_toFinset] using hA)
  · exact Algorithms.SupportIndex.compress_expand _ (Algorithms.SupportIndex.labels_nodup t)
  · intro A B hA
    exact Algorithms.SupportIndex.subsetWord_compress _ A B (by
      simpa only [Algorithms.SupportIndex.labels_toFinset] using hA)

/-- info: 'KFOL.Paper.reset_support_indexing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_support_indexing

/-- Strict binary record and stream codecs, including exact bit lengths.
Output indices use canonical binary naturals and prerequisite words have
exactly the dictionary width. These are representation and size results. -/
theorem reset_guard_record_codec :
    (∀ (n : ℕ) (r : Fin n × Finset (Fin n)) (word : List Bool),
      (Algorithms.GuardRecord.decode n word = some r ↔ word = Algorithms.GuardRecord.encode r) ∧
      (Algorithms.GuardRecord.encode r).length = 2 * r.1.val.size + 2 + n) ∧
    (∀ (n : ℕ) (records : List (Fin n × Finset (Fin n))) (word : List Bool),
      (Algorithms.GuardRecord.decodeList n word = some records ↔
        word = Algorithms.GuardRecord.encodeList records) ∧
      (Algorithms.GuardRecord.encodeList records).length ≤ 6 * records.length * (n + 1)) ∧
    (∀ (D : List ℕ) (word : List Bool),
      (Algorithms.LabelDictionary.decode word = some D ↔ word = Algorithms.LabelDictionary.encode D) ∧
      (Algorithms.LabelDictionary.encode D).length = 2 * (D.map Nat.size).sum + 2 * D.length) :=
  ⟨fun _ r w => ⟨Algorithms.GuardRecord.decode_eq_some_iff w r, Algorithms.GuardRecord.length_encode r⟩,
    fun _ rs w => ⟨Algorithms.GuardRecord.decodeList_eq_some_iff w rs,
      Algorithms.GuardRecord.length_encodeList_linear rs⟩,
    fun D w => ⟨Algorithms.LabelDictionary.decode_eq_some_iff w D, Algorithms.LabelDictionary.length_encode D⟩⟩

/-- info: 'KFOL.Paper.reset_guard_record_codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_guard_record_codec

/-- The actual term supplies its dictionary and all serializable records.
Decoded expansion recovers the original occurrence list and therefore the
canonical tables. Encoded sizes count bits, including sparse binary names. -/
theorem reset_binary_guard_records (t : Reset.Term ℕ) :
    let D := Algorithms.SupportIndex.labels t
    (Algorithms.LabelDictionary.encode D).length ≤
      2 * (t.guardEntries.map (fun p => p.1.size)).sum + 2 * t.leafCount ∧
    ∃ records : List (Fin D.length × Finset (Fin D.length)),
      t.guardEntries.mapM (Algorithms.SupportIndex.compressEntry D) = some records ∧
      records.length = t.leafCount ∧
      records.map (fun r => (D.get r.1, Algorithms.SupportIndex.expand D r.2)) = t.guardEntries ∧
      Algorithms.GuardRecord.decodeList D.length (Algorithms.GuardRecord.encodeList records) =
        some records ∧
      (Algorithms.GuardRecord.encodeList records).length ≤ 6 * t.leafCount * (t.leafCount + 1) ∧
      (∀ j, Reset.Term.minimize
        ((((records.map (fun r => (D.get r.1, Algorithms.SupportIndex.expand D r.2))).filter
          (fun p => p.1 = j)).map Prod.snd).toFinset) = t.table j) := by
  dsimp only
  refine ⟨Algorithms.LabelDictionary.length_encode_support_le t, ?_⟩
  obtain ⟨records, hr, hlen, he, hd, hb⟩ := Algorithms.indexed_guard_records t
  refine ⟨records, hr, hlen, he, hd, hb, ?_⟩
  intro j
  rw [he]
  exact (t.table_eq_entries j).symm

/-- info: 'KFOL.Paper.reset_binary_guard_records' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_binary_guard_records

/-- Ordinary binary tree inputs use one constructor bit per occurrence and
canonical framed binary names at leaves. Decoding is exact; the input bit
length bounds both syntax occurrences and the partial parser's consumption. -/
theorem reset_binary_input_codec :
    (∀ (word : List Bool) (t : Reset.Term ℕ),
      Algorithms.TermCode.decode word = some t ↔ word = Algorithms.TermCode.encode t) ∧
    Function.Injective Algorithms.TermCode.encode ∧
    (∀ (t : Reset.Term ℕ) (rest : List Bool),
      Algorithms.TermCode.decode (Algorithms.TermCode.encode t ++ rest) =
        if rest.isEmpty then some t else none) ∧
    (∀ t : Reset.Term ℕ,
      (Algorithms.TermCode.encode t).length = t.size + 2 * t.leafCount +
        2 * (t.guardEntries.map (fun p => p.1.size)).sum ∧
      t.size ≤ (Algorithms.TermCode.encode t).length ∧
      t.leafCount ≤ (Algorithms.TermCode.encode t).length) ∧
    (∀ (t : Reset.Term ℕ) (rest : List Bool) (fuel : ℕ), t.size ≤ fuel →
      Algorithms.TermCode.parse fuel (Algorithms.TermCode.encode t ++ rest) = some (t, rest)) ∧
    (∀ (fuel : ℕ) (word rest : List Bool) (t : Reset.Term ℕ),
      Algorithms.TermCode.parse fuel word = some (t, rest) →
        Algorithms.TermCode.encode t ++ rest = word ∧ t.size + rest.length ≤ word.length) :=
  ⟨Algorithms.TermCode.decode_eq_some_iff, Algorithms.TermCode.encode_injective,
    Algorithms.TermCode.decode_encode_append,
    fun t => ⟨Algorithms.TermCode.length_encode t, Algorithms.TermCode.size_le_length_encode t,
      Algorithms.TermCode.leafCount_le_length_encode t⟩,
    Algorithms.TermCode.parse_encode, fun _ _ _ _ h =>
      ⟨Algorithms.TermCode.encode_append_of_parse h, Algorithms.TermCode.size_add_length_rest_le h⟩⟩

/-- info: 'KFOL.Paper.reset_binary_input_codec' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_binary_input_codec

/-- The executable binary frontend accepts exactly valid syntax, builds the
actual occurrence records and recovers the canonical tables. All lengths
count bits of the original input and output; running time is a separate claim. -/
theorem reset_binary_extraction :
    (∀ word : List Bool, Algorithms.TermCode.extract word = none ↔
      Algorithms.TermCode.decode word = none) ∧
    (∀ (word : List Bool) (t : Reset.Term ℕ), Algorithms.TermCode.decode word = some t →
      let D := Algorithms.SupportIndex.labels t
      ∃ records : List (Fin D.length × Finset (Fin D.length)),
        Algorithms.TermCode.extract word = some (_root_.KFOL.Words.pair
          (Algorithms.LabelDictionary.encode D) (Algorithms.GuardRecord.encodeList records)) ∧
        records.length = t.leafCount ∧
        records.map (fun r => (D.get r.1, Algorithms.SupportIndex.expand D r.2)) = t.guardEntries ∧
        Algorithms.LabelDictionary.decode (Algorithms.LabelDictionary.encode D) = some D ∧
        Algorithms.GuardRecord.decodeList D.length (Algorithms.GuardRecord.encodeList records) =
          some records ∧
        (Algorithms.LabelDictionary.encode D).length ≤ word.length ∧
        (Algorithms.GuardRecord.encodeList records).length ≤ 6 * word.length * (word.length + 1) ∧
        (_root_.KFOL.Words.pair (Algorithms.LabelDictionary.encode D)
          (Algorithms.GuardRecord.encodeList records)).length ≤
            6 * word.length * (word.length + 1) + 2 * word.length + 2 ∧
        (∀ j, Reset.Term.minimize
          ((((records.map (fun r => (D.get r.1, Algorithms.SupportIndex.expand D r.2))).filter
            (fun p => p.1 = j)).map Prod.snd).toFinset) = t.table j)) := by
  refine ⟨Algorithms.TermCode.extract_eq_none_iff, ?_⟩
  intro word t h
  dsimp only
  obtain ⟨records, he, hl, hr, hd, hb, hp⟩ := Algorithms.TermCode.extract_spec h
  refine ⟨records, he, hl, hr, Algorithms.LabelDictionary.decode_encode _,
    Algorithms.GuardRecord.decodeList_encodeList records, hd, hb, hp, ?_⟩
  intro j
  rw [hr]
  exact (t.table_eq_entries j).symm

/-- info: 'KFOL.Paper.reset_binary_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_binary_extraction

/-- A complete descriptor has distinct binary names and well-ranged,
fixed-width records. Its exact codec preserves order and duplicate records;
expansion and recompression are inverse, and original extraction always
produces valid descriptors recovering the actual occurrence list. -/
theorem reset_binary_descriptor_codec :
    (∀ (word : List Bool) (d : Algorithms.GuardDescriptor),
      Algorithms.GuardDescriptor.decode word = some d ↔
        word = Algorithms.GuardDescriptor.encode d) ∧
    Function.Injective Algorithms.GuardDescriptor.encode ∧
    (∀ d : Algorithms.GuardDescriptor,
      d.labels.Nodup ∧
      (Algorithms.GuardDescriptor.encode d).length = 4 * (d.labels.map Nat.size).sum +
        4 * d.labels.length + 2 + (Algorithms.GuardRecord.encodeList d.records).length ∧
      d.labels.length ≤ (Algorithms.GuardDescriptor.encode d).length ∧
      d.records.length ≤ (Algorithms.GuardDescriptor.encode d).length ∧
      (d.records.map (fun r => (d.labels.get r.1,
        Algorithms.SupportIndex.expand d.labels r.2))).mapM
          (Algorithms.SupportIndex.compressEntry d.labels) = some d.records ∧
      (∀ (j : Fin d.labels.length) (A : Finset (Fin d.labels.length)),
        A ∈ d.guards j ↔ (j, A) ∈ d.records) ∧
      (∀ (r j : Fin d.labels.length) (B : Finset (Fin d.labels.length)),
        (d.table r).Enabled (B : Set (Fin d.labels.length)) j ↔
          ∃ A, (j, A) ∈ d.records ∧ Algorithms.GuardWords.subsetWord
            (Algorithms.Bitset.encode A) (Algorithms.Bitset.encode B) = [true])) ∧
    (∀ (word output : List Bool), Algorithms.TermCode.extract word = some output →
      ∃ (d : Algorithms.GuardDescriptor) (t : Reset.Term ℕ),
        Algorithms.GuardDescriptor.decode output = some d ∧
        Algorithms.TermCode.decode word = some t ∧ d.labels = Algorithms.SupportIndex.labels t ∧
        d.records.map (fun r => (d.labels.get r.1, Algorithms.SupportIndex.expand d.labels r.2)) =
          t.guardEntries) :=
  ⟨Algorithms.GuardDescriptor.decode_eq_some_iff, Algorithms.GuardDescriptor.encode_injective,
    fun d => ⟨d.distinct, d.length_encode, d.width_le_length_encode,
      d.records_le_length_encode, d.recompress_records, d.mem_guards, d.enabled_iff_subsetWord⟩,
    fun _ _ => Algorithms.GuardDescriptor.decode_extraction⟩

/-- info: 'KFOL.Paper.reset_binary_descriptor_codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_binary_descriptor_codec

/-- External canonical-table recognition, with all mathematical conditions
spelled out and a real primitive-tree witness. This checks executable
semantics, syntax-size bounds and native polynomial running time. -/
theorem reset_encoded_table_recognition :
    (∀ d : Algorithms.GuardDescriptor, d.check = true ↔
      ∃ r : Fin d.labels.length,
        (∀ j, ∀ A ∈ d.guards j, ∀ B ∈ d.guards j, A ⊆ B → A = B) ∧
        d.guards r = {∅} ∧ (∀ j, ∅ ∈ d.guards j → j = r) ∧
        (∀ j, ∀ A ∈ d.guards j, j ∉ A) ∧
        (∀ j, ∀ A ∈ d.guards j, (d.table r).Constructible A)) ∧
    (∀ d : Algorithms.GuardDescriptor, d.check = true ↔
      ∃ t : Reset.Term (Fin d.labels.length), t.table = d.guards ∧
        t.size ≤ 1 + 2 * d.labels.length * d.records.length) ∧
    (∀ word : List Bool, Algorithms.GuardDescriptor.recognize word = true ↔
      ∃ (d : Algorithms.GuardDescriptor) (t : Reset.Term (Fin d.labels.length)),
        word = Algorithms.GuardDescriptor.encode d ∧ t.table = d.guards ∧
        t.size ≤ 1 + 2 * word.length * word.length) ∧
    Turing.MultiTapeTM.ComputableInPolyTime Algorithms.GuardDescriptor.check
      Complexity.DescriptorValidation.descriptorEncoding Turing.MultiTapeTM.encBool ∧
    Turing.MultiTapeTM.ComputableInPolyTime Algorithms.GuardDescriptor.recognize
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBool :=
  ⟨fun d => d.check_eq_true, Algorithms.GuardDescriptor.check_iff_bounded_realization,
    Algorithms.GuardDescriptor.recognize_eq_true,
    Complexity.RecognitionMachine.check_polyTime, Complexity.RecognitionMachine.recognize_polyTime⟩

/-- info: 'KFOL.Paper.reset_encoded_table_recognition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_encoded_table_recognition

/-- Listed-record normalization is exactly minimal-guard normalization. It
preserves enabling, order and minimal duplicates, is idempotent, and cannot
increase binary descriptor size. Malformed external inputs are rejected. -/
theorem reset_record_normalization :
    (∀ d : Algorithms.GuardDescriptor,
      d.normalize.labels = d.labels ∧ d.normalize.records.Sublist d.records ∧
      d.normalize.normalize = d.normalize ∧
      (Algorithms.GuardDescriptor.encode d.normalize).length ≤
        (Algorithms.GuardDescriptor.encode d).length ∧
      (∀ j : Fin d.labels.length, d.normalize.guards j = Reset.Term.minimize (d.guards j)) ∧
      (∀ (r j : Fin d.labels.length) (B : Set (Fin d.labels.length)),
        (d.normalize.table r).Enabled B j ↔ (d.table r).Enabled B j)) ∧
    (∀ word : List Bool, Algorithms.GuardDescriptor.normalizeWord word = none ↔
      Algorithms.GuardDescriptor.decode word = none) ∧
    (∀ (word output : List Bool), Algorithms.GuardDescriptor.normalizeWord word = some output →
      ∃ d : Algorithms.GuardDescriptor, Algorithms.GuardDescriptor.decode word = some d ∧
        output = Algorithms.GuardDescriptor.encode d.normalize ∧
        Algorithms.GuardDescriptor.decode output = some d.normalize ∧ output.length ≤ word.length ∧
        Algorithms.GuardDescriptor.normalizeWord output = some output) ∧
    Turing.MultiTapeTM.ComputableInPolyTime Algorithms.GuardDescriptor.normalize
      Complexity.DescriptorValidation.descriptorEncoding
      Complexity.DescriptorValidation.descriptorEncoding ∧
    Turing.MultiTapeTM.ComputableInPolyTime Algorithms.GuardDescriptor.normalizeWord
      Turing.MultiTapeTM.encBits (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encBits) := by
  refine ⟨fun d => ⟨rfl, d.records_normalize_sublist, d.normalize_idempotent,
    d.length_normalize_le, d.guards_normalize, d.enabled_normalize⟩,
    Algorithms.GuardDescriptor.normalizeWord_eq_none_iff, ?_,
    Complexity.NormalizeMachine.normalize_polyTime, Complexity.NormalizeMachine.normalizeWord_polyTime⟩
  intro word output h
  obtain ⟨d, hd, he, ho, hb⟩ := Algorithms.GuardDescriptor.normalizeWord_spec h
  exact ⟨d, hd, he, ho, hb, Algorithms.GuardDescriptor.normalizeWord_idempotent h⟩

/-- info: 'KFOL.Paper.reset_record_normalization' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_record_normalization

/-- Normalizing the actual binary extraction output yields recognized
canonical tables. Expanding them recovers the independently defined tables
of the original term; no candidate or realizability hypothesis is supplied. -/
theorem reset_normalized_binary_extraction (word output : List Bool)
    (h : Algorithms.TermCode.extract word = some output) :
    ∃ (d : Algorithms.GuardDescriptor) (t : Reset.Term ℕ),
      Algorithms.GuardDescriptor.decode output = some d ∧
      Algorithms.TermCode.decode word = some t ∧ d.labels = Algorithms.SupportIndex.labels t ∧
      Algorithms.GuardDescriptor.normalizeWord output =
        some (Algorithms.GuardDescriptor.encode d.normalize) ∧
      Algorithms.GuardDescriptor.recognize (Algorithms.GuardDescriptor.encode d.normalize) = true ∧
      (∀ j : Fin d.labels.length, (d.normalize.guards j).image
        (Algorithms.SupportIndex.expand d.labels) = t.table (d.labels.get j)) := by
  obtain ⟨d, t, hd, ht, hl, hc, he⟩ := Algorithms.GuardDescriptor.normalized_extraction h
  refine ⟨d, t, hd, ht, hl, ?_, ?_, he⟩
  · rw [← Algorithms.GuardDescriptor.encode_of_decode hd]
    exact Algorithms.GuardDescriptor.normalizeWord_encode d
  · simp only [Algorithms.GuardDescriptor.recognize,
      Algorithms.GuardDescriptor.decode_encode]
    exact hc

/-- info: 'KFOL.Paper.reset_normalized_binary_extraction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_normalized_binary_extraction

/-- Equality of binary reset equations on shared support. The finite
checker is exact on all mixed winner-set valuations whenever three roles
exist. The word checker rejects every malformed pair or syntax tree. -/
theorem reset_binary_equation_checker {Role : Type u} (three : Fin 3 ↪ Role) :
    (∀ s t : Reset.Term ℕ,
      (Algorithms.ResetEquation.labels s t).Nodup ∧
      (Algorithms.ResetEquation.labels s t).toFinset = s.varFinset ∪ t.varFinset ∧
      (Algorithms.ResetEquation.labels s t).length ≤ s.leafCount + t.leafCount ∧
      (Algorithms.ResetEquation.labels s t).length ≤
        (Algorithms.TermCode.encode s).length + (Algorithms.TermCode.encode t).length ∧
      (Algorithms.ResetEquation.check s t = true ↔ s.table = t.table) ∧
      (Algorithms.ResetEquation.check s t = true ↔
        ∀ valuation : ℕ → WinnerSet Role, s.eval valuation = t.eval valuation)) ∧
    (∀ word : List Bool, Algorithms.ResetEquation.checkWord word = true ↔
      ∃ s t : Reset.Term ℕ,
        word = _root_.KFOL.Words.pair (Algorithms.TermCode.encode s) (Algorithms.TermCode.encode t) ∧
        ∀ valuation : ℕ → WinnerSet Role, s.eval valuation = t.eval valuation) ∧
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : Reset.Term ℕ × Reset.Term ℕ => Algorithms.ResetEquation.check p.1 p.2)
      (Turing.MultiTapeTM.encPair Complexity.TermMachine.termEncoding Complexity.TermMachine.termEncoding)
      Turing.MultiTapeTM.encBool ∧
    Turing.MultiTapeTM.ComputableInPolyTime Algorithms.ResetEquation.checkWord
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBool :=
  ⟨fun s t => ⟨Algorithms.ResetEquation.labels_nodup s t,
      Algorithms.ResetEquation.labels_toFinset s t, Algorithms.ResetEquation.length_labels_le s t,
      Algorithms.ResetEquation.length_labels_le_input s t, Algorithms.ResetEquation.check_eq_true s t,
      Algorithms.ResetEquation.check_iff_eval three s t⟩,
    Algorithms.ResetEquation.checkWord_eq_true three,
    Complexity.ResetEquality.check_polyTime, Complexity.ResetEquality.checkWord_polyTime⟩

/-- info: 'KFOL.Paper.reset_binary_equation_checker' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_binary_equation_checker

/-- `owner:lem:root`. Ambiguity and each atomic output are determined
exactly by the root variable, for the entire guarded-owner signature. -/
theorem owner_root_status {Role : Type u} {Var : Type v}
    (t : Owner.Term Role Var) (valuation : Var → WinnerSet Role) :
    ((t.eval valuation).Ambiguous ↔ (valuation t.root).Ambiguous) ∧
    (∀ r, t.eval valuation = WinnerSet.singleton r ↔
      valuation t.root = WinnerSet.singleton r) :=
  ⟨t.ambiguous_iff valuation, t.eq_singleton_iff valuation⟩

/-- info: 'KFOL.Paper.owner_root_status' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_root_status

/-- `owner:thm:guards`, including the exact occurrence semantics and the
explicit two-winner countervaluation using the same three distinct roles. -/
theorem owner_guard_completeness {Role : Type u} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (s t : Owner.Term Role Var)
    (k a b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (hs : s.OwnersIn (fun r => r = k ∨ r = a))
    (ht : t.OwnersIn (fun r => r = k ∨ r = a)) :
    (∀ valuation : Var → WinnerSet Role, k ∈ (s.eval valuation).val ↔
      ∃ g ∈ s.guards k, (∀ j ∈ g.many, (valuation j).Ambiguous) ∧
        (∀ j ∈ g.outside, valuation j ≠ WinnerSet.singleton a) ∧
          k ∈ (valuation g.source).val) ∧
    (∀ valuation : Var → WinnerSet Role, k ∈ (t.eval valuation).val ↔
      ∃ g ∈ t.guards k, (∀ j ∈ g.many, (valuation j).Ambiguous) ∧
        (∀ j ∈ g.outside, valuation j ≠ WinnerSet.singleton a) ∧
          k ∈ (valuation g.source).val) ∧
    (s.guards k).length = s.leafCount ∧ (t.guards k).length = t.leafCount ∧
    ((∀ g ∈ s.guards k, ∃ h ∈ t.guards k, h.source = g.source ∧
      (∀ j ∈ h.many, j ∈ g.many) ∧
      (∀ j ∈ h.outside, j ∈ g.many ∨ j ∈ g.outside ∨ j = g.source)) ↔
        ∀ valuation : Var → WinnerSet Role,
          k ∈ (s.eval valuation).val → k ∈ (t.eval valuation).val) ∧
    (¬(∀ g ∈ s.guards k, ∃ h ∈ t.guards k, h.source = g.source ∧
      (∀ j ∈ h.many, j ∈ g.many) ∧
      (∀ j ∈ h.outside, j ∈ g.many ∨ j ∈ g.outside ∨ j = g.source)) →
      ∃ g ∈ s.guards k,
        k ∈ (s.eval (Owner.minimalVal k a b g)).val ∧
        k ∉ (t.eval (Owner.minimalVal k a b g)).val ∧
        ∀ j, ∃ r ∈ ({k, a, b} : Set Role), ∃ q ∈ ({k, a, b} : Set Role),
          Owner.minimalVal k a b g j = (WinnerSet.singleton r).union (WinnerSet.singleton q)) :=
  ⟨s.guard_semantics k a hs, t.guard_semantics k a ht, s.guards_length k, t.guards_length k,
    s.observation_implication_iff t k a b hka hkb hab hs ht,
    s.observation_countervaluation t k a b hka hkb hab hs ht⟩

/-- info: 'KFOL.Paper.owner_guard_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_guard_completeness

/-- The semantic and executable-checker clauses of `owner:thm:one-table`.
`owner_original_word_checker` supplies the uniform original-word polynomial bound. -/
theorem owner_one_table {Role : Type u} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (a k : Role) (hka : k ≠ a) (s t : Owner.Term Role Var)
    (hs : s.OwnersIn (fun r => r = a)) (ht : t.OwnersIn (fun r => r = a)) :
    ((∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
      Owner.Covers (s.guards k) (t.guards k) ∧ Owner.Covers (t.guards k) (s.guards k)) ∧
    (Owner.Term.equationB k s t = true ↔
      ∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) :=
  ⟨s.single_table_equation_iff three t a k hka hs ht,
    Owner.Term.equationB_correct three a k hka s t hs ht⟩

/-- info: 'KFOL.Paper.owner_one_table' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_one_table

/-- Guarded choice is idempotent and preserves every atomic root. Its
actual expansion into owned choices preserves all valuations and is core. -/
theorem owner_definability {Role : Type u} {Var : Type v} (three : Fin 3 ↪ Role)
    (roles : List Role) (covers : ∀ r, r ∈ roles) :
    (∀ (a : Role) (A : WinnerSet Role), WinnerSet.guardedChoice a A A A = A) ∧
    (∀ (a i : Role) (A B : WinnerSet Role),
      WinnerSet.guardedChoice a (WinnerSet.singleton i) A B = WinnerSet.singleton i) ∧
    (∀ (t : Owner.Term Role Var) (valuation : Var → WinnerSet Role),
      (t.compile three roles).eval valuation = t.eval valuation ∧
        (t.compile three roles).IsCore) :=
  ⟨WinnerSet.guardedChoice_self, WinnerSet.guardedChoice_singleton,
    fun t valuation => ⟨t.eval_compile three roles covers valuation, t.isCore_compile three roles⟩⟩

/-- info: 'KFOL.Paper.owner_definability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_definability

/-- Complete binary framing and block-stream parsers have native
polynomial-time machines, including malformed inputs and all returned data.
Paper-word framing and native machine tuple encodings remain distinct. -/
theorem binary_framing_machines :
    Turing.MultiTapeTM.ComputableInPolyTime Words.unpair? Turing.MultiTapeTM.encBits
      (Turing.MultiTapeTM.encOption (Turing.MultiTapeTM.encPair
        Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)) ∧
    Turing.MultiTapeTM.ComputableInPolyTime Words.undelimitBlocks Turing.MultiTapeTM.encBits
      (Turing.MultiTapeTM.encOption (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBits)) ∧
    Turing.MultiTapeTM.ComputableInPolyTime Words.delimit
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits ∧
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun p : List Bool × List Bool => Words.pair p.1 p.2)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBits ∧
    (∀ word left right : List Bool,
      Words.unpair? word = some (left, right) ↔ word = Words.pair left right) ∧
    (∀ (word : List Bool) (blocks : List (List Bool)),
      Words.undelimitBlocks word = some blocks ↔ word = (blocks.map Words.delimit).flatten) := by
  refine ⟨Complexity.Framing.unpair_polyTime, Complexity.BlockScan.undelimitBlocks_polyTime,
    Complexity.Framing.delimit_polyTime, Complexity.Framing.pair_polyTime,
    fun _ _ _ => Words.unpair?_eq_some_iff, ?_⟩
  intro word blocks
  exact ⟨fun h => (Algorithms.Framing.undelimitBlocks_sound h).symm,
    fun h => h ▸ Words.undelimitBlocks_flatten_delimit blocks⟩

/-- info: 'KFOL.Paper.binary_framing_machines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.binary_framing_machines

/-- The semantic-equivalence part of `owner:thm:four`, with the concrete
four displayed winner sets closed under both operations. The exclusion of
smaller generators is proved in `owner_minimum_generator`. -/
theorem owner_four_element_theory {Role : Type u} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (a k b : Role) (hka : k ≠ a) (hkb : k ≠ b) (hab : a ≠ b)
    (s t : Owner.Term Role Var)
    (hs : s.OwnersIn (fun r => r = a)) (ht : t.OwnersIn (fun r => r = a)) :
    Fintype.card Owner.Four = 4 ∧
    (∀ x : Owner.Four, Owner.Four.project a k (Owner.Four.embed a k b x) = x) ∧
    (∀ x y : Owner.Four, Owner.Four.embed a k b (Owner.Four.reset x y) =
      (Owner.Four.embed a k b x).reset (Owner.Four.embed a k b y)) ∧
    (∀ x y z : Owner.Four, Owner.Four.embed a k b (Owner.Four.guarded x y z) =
      WinnerSet.guardedChoice a (Owner.Four.embed a k b x) (Owner.Four.embed a k b y)
        (Owner.Four.embed a k b z)) ∧
    ((∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
      ∀ valuation : Var → Owner.Four, s.evalFour valuation = t.evalFour valuation) :=
  ⟨Owner.Four.card, Owner.Four.project_embed a k b hka hkb hab,
    Owner.Four.embed_reset a k b hab,
    Owner.Four.embed_guarded a k b hab,
    s.four_element_complete three t a k hka hs ht⟩

/-- info: 'KFOL.Paper.owner_four_element_theory' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_four_element_theory

/-- Required `core:prop:basis-arity`: a uniform K+2-element obstruction to
every basis restricted to K actual variables, with an explicit separating
K+1-variable core identity. This is a bounded-variable obstruction; the
unbounded nonfinite-basis theorem needs the subsequent grid construction. -/
theorem core_variable_bound_obstruction {Role : Type u} [DecidableEq Role] [Fintype Role]
    (three : Fin 3 ↪ Role) :
    letI := Equational.coreStructure Role
    letI := Core.Native.structureOf (Role := Role)
    Fintype.card (Core.Native Role) = Fintype.card Role + 2 ∧
    (∀ e : Equational.Identity (Equational.CoreSymbol Role),
      e.variableCount ≤ Fintype.card Role → e.Holds (WinnerSet Role) →
        e.Holds (Core.Native Role)) ∧
    (Core.exhaustionIdentity three).Holds (WinnerSet Role) ∧
    ¬(Core.exhaustionIdentity three).Holds (Core.Native Role) ∧
    (Core.exhaustionIdentity three).variableCount = Fintype.card Role + 1 ∧
    ¬Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Core.Native Role) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role),
      (∀ e ∈ T, e.variableCount ≤ Fintype.card Role) → ¬Equational.IsBasis (WinnerSet Role) T) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role),
      Equational.IsBasis (WinnerSet Role) T → ∃ e ∈ T, Fintype.card Role + 1 ≤ e.variableCount) := by
  let _ := Equational.coreStructure Role
  let _ := Core.Native.structureOf (Role := Role)
  exact ⟨Core.Native.card_native, Core.Native.holds_of_variableCount_le three,
    Core.exhaustion_valid three, Core.exhaustion_not_valid three,
    Core.exhaustion_variableCount three, Core.native_not_inVariety three,
    Core.no_basis_with_role_bound three, Core.exists_large_identity_of_basis three⟩

/-- info: 'KFOL.Paper.core_variable_bound_obstruction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.core_variable_bound_obstruction

/-- Canonical sparse binary names, dictionaries and complete dependent
descriptor decoding have native polynomial-time machines. The output
descriptor embedding is exactly its independently defined paper encoding. -/
theorem binary_descriptor_machines :
    Turing.MultiTapeTM.ComputableInPolyTime Words.BinaryNatCode.value
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encNat ∧
    Turing.MultiTapeTM.ComputableInPolyTime Words.BinaryNatCode.encode
      Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encBits ∧
    Turing.MultiTapeTM.ComputableInPolyTime Words.BinaryNatCode.decode?
      Turing.MultiTapeTM.encBits (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encNat) ∧
    Turing.MultiTapeTM.ComputableInPolyTime Algorithms.LabelDictionary.decode
      Turing.MultiTapeTM.encBits
      (Turing.MultiTapeTM.encOption (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat)) ∧
    Turing.MultiTapeTM.ComputableInPolyTime (fun labels : List ℕ => decide labels.Nodup)
      (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat) Turing.MultiTapeTM.encBool ∧
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun word => (Algorithms.GuardDescriptor.decode word).isSome)
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBool ∧
    Turing.MultiTapeTM.ComputableInPolyTime Algorithms.GuardDescriptor.decode
      Turing.MultiTapeTM.encBits
      (Turing.MultiTapeTM.encOption Complexity.DescriptorValidation.descriptorEncoding) ∧
    (∀ d : Algorithms.GuardDescriptor,
      Complexity.DescriptorValidation.descriptorEncoding d = Algorithms.GuardDescriptor.encode d) :=
  ⟨Complexity.Dictionary.value_polyTime, Complexity.Dictionary.encode_polyTime,
    Complexity.Dictionary.decode_polyTime, Complexity.Dictionary.dictionary_decode_polyTime,
    Complexity.Dictionary.dictionary_nodup_polyTime, Complexity.DescriptorValidation.decode_isSome_polyTime,
    Complexity.DescriptorValidation.decode_polyTime, fun _ => rfl⟩

/-- info: 'KFOL.Paper.binary_descriptor_machines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.binary_descriptor_machines

/-- The explicit guarded-choice example in the reset section: changing an
atomic side input changes whether the third role is a possible winner. -/
theorem guarded_choice_example {Role : Type u} (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    c ∉ (WinnerSet.guardedChoice a ((WinnerSet.singleton a).union (WinnerSet.singleton b))
      (WinnerSet.singleton a) (WinnerSet.singleton c)).val ∧
    c ∈ (WinnerSet.guardedChoice a ((WinnerSet.singleton a).union (WinnerSet.singleton b))
      (WinnerSet.singleton b) (WinnerSet.singleton c)).val :=
  WinnerSet.guardedChoice_separates a b c hab hac hbc

/-- info: 'KFOL.Paper.guarded_choice_example' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.guarded_choice_example

/-- `owner:thm:four`: the four-element algebra has exactly the one-owner
identities, and every finite algebra with that complete identity theory has
at least four elements. Unit labels the single H operation in the generator
comparison; arbitrary concrete owner labels are covered by the first clause. -/
theorem owner_minimum_generator {Role : Type u} {Var : Type v}
    [DecidableEq Role] [DecidableEq Var] (three : Fin 3 ↪ Role)
    (a k : Role) (hka : k ≠ a) :
    Fintype.card Owner.Four = 4 ∧
    (∀ s t : Owner.Term Role Var,
      s.OwnersIn (fun r => r = a) → t.OwnersIn (fun r => r = a) →
        ((∀ valuation : Var → WinnerSet Role, s.eval valuation = t.eval valuation) ↔
          ∀ valuation : Var → Owner.Four, s.evalFour valuation = t.evalFour valuation)) ∧
    (∀ (M : Type w) [Fintype M]
      [(Equational.language (Owner.Symbol Unit)).Structure M],
      letI := Owner.fourStructure (Role := Unit)
      (∀ e : Equational.Identity (Owner.Symbol Unit), e.Holds Owner.Four ↔ e.Holds M) →
        4 ≤ Fintype.card M) :=
  ⟨Owner.Four.card, fun s t hs ht => s.four_element_complete three t a k hka hs ht,
    fun _ _ _ => Owner.four_minimum_generator⟩

/-- info: 'KFOL.Paper.owner_minimum_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_minimum_generator

/-- `reset:cor:generator`: the explicit three-element multiplication table
has exactly the reset identities and is smallest among all finite generators. -/
theorem reset_minimum_generator {Role : Type u} (three : Fin 3 ↪ Role) :
    letI := Reset.structureOf (WinnerSet.reset (Role := Role))
    letI := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    Fintype.card (Fin 3) = 3 ∧
    (∀ e : Equational.Identity Reset.Symbol, e.Holds (WinnerSet Role) ↔ e.Holds (Fin 3)) ∧
    (∀ (M : Type v) [Fintype M] [(Equational.language Reset.Symbol).Structure M],
      (∀ e : Equational.Identity Reset.Symbol, e.Holds (WinnerSet Role) ↔ e.Holds M) →
        3 ≤ Fintype.card M) := by
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  refine ⟨Fintype.card_fin 3, Reset.identity_iff_chain three, ?_⟩
  intro M _ _ h
  apply Reset.chain_minimum_generator
  intro e
  exact (Reset.identity_iff_chain three e).symm.trans (h e)

/-- info: 'KFOL.Paper.reset_minimum_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_minimum_generator

open FirstOrder

/-- `core:lem:typed-upper-clone-cover`: the reflecting-ideal typing and the
compatible surjective cover imply that the upper clone belongs to the core
variety. The ideal and native atomic restriction carry their actual induced
operations; the conclusion requires no supplied presentation certificate. -/
theorem core_typed_upper_clone_cover {Role : Type u} [DecidableEq Role]
    {C : Type v} [(Equational.language (Equational.CoreSymbol Role)).Structure C]
    {P : Type w} [(Equational.language (Equational.CoreSymbol Role)).Structure P]
    (three : Fin 3 ↪ Role)
    (hC : letI := Equational.coreStructure Role
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) C)
    (e : C)
    (reflecting : ∀ (r : Role) (c : C),
      Core.join three (Core.operation r e c) e = e → Core.join three c e = e)
    (R : Set Role) (proper : R ≠ Set.univ)
    (η : Core.ideal hC three e →[Equational.language (Equational.CoreSymbol Role)]
      Core.Native.atomicRestriction R)
    (typed : ∀ (c : Core.ideal hC three e) (r : Role),
      (η c).val = Core.Native.atom r ↔ Core.operation r e c.val ≠ e)
    (hP : letI := Equational.coreStructure Role
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) P)
    (q : P →[Equational.language (Equational.CoreSymbol Role)] C)
    (onto : Function.Surjective q)
    (label : P →[Equational.language (Equational.CoreSymbol Role)] Core.Native.atomicRestriction R)
    (compatible : ∀ (u : P) (hu : Core.join three (q u) e = e), label u = η ⟨q u, hu⟩) :
    letI := Equational.coreStructure Role
    letI := Core.upperStructure (Role := Role) e
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (Option C) :=
  Core.typed_upper_clone_cover three hC e reflecting R proper η typed hP q onto label compatible

/-- info: 'KFOL.Paper.core_typed_upper_clone_cover' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.core_typed_upper_clone_cover

/-- `game:thm:adequacy`: every finite public tree has a full pure equilibrium,
and the equilibrium-defined value obeys the leaf and owned-choice equations. -/
theorem public_backward_induction {Role : Type u} :
    (∀ g : Strategic.Tree Role, ∃ p : Strategic.Profile g, Strategic.IsSubgamePerfect p) ∧
    (∀ i : Role, Strategic.value (.leaf i) = WinnerSet.singleton i) ∧
    (∀ (r : Role) (g h : Strategic.Tree Role),
      Strategic.value (.node r g h) = WinnerSet.choice r (Strategic.value g) (Strategic.value h)) :=
  ⟨Strategic.exists_spe, Strategic.value_leaf, Strategic.value_node⟩

/-- info: 'KFOL.Paper.public_backward_induction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_backward_induction

/-- Whole-player optimality in every public subtree equals canonical
GameTheory Nash optimality of the corresponding complete contingent plans. -/
theorem public_equilibrium_strategic_form {Role : Type u} [DecidableEq Role]
    {g : Strategic.Tree Role} (p : Strategic.Profile g) :
    (Strategic.IsNash p ↔ GameTheory.IsNash (Strategic.gameForm g)
      (Strategic.winningPreference Role) (fun _ => p)) ∧
    (Strategic.IsSubgamePerfect p ↔
      ∀ {h : Strategic.Tree Role} (q : Strategic.Profile h), Strategic.Restriction p q →
        GameTheory.IsNash (Strategic.gameForm h) (Strategic.winningPreference Role) (fun _ => q)) :=
  ⟨Strategic.nash_iff_gameTheory p, Strategic.spe_iff_gameTheory p⟩

/-- info: 'KFOL.Paper.public_equilibrium_strategic_form' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_equilibrium_strategic_form

/-- `game:thm:union`: three distinct public owners realize neutral union;
every nonempty subset of a finite role set is the value of a closed game. -/
theorem public_neutral_union {Role : Type u} [Finite Role]
    (r s t : Role) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (∀ g h : Strategic.Tree Role,
      Strategic.value (.node t (.node r g h) (.node s g h)) =
        WinnerSet.union (Strategic.value g) (Strategic.value h)) ∧
    (∀ A : WinnerSet Role, ∃ g : Strategic.Tree Role, Strategic.value g = A) := by
  refine ⟨Strategic.value_neutralTree r s t hrs hrt hst, ?_⟩
  let three : Fin 3 ↪ Role :=
    ⟨![r, s, t], by intro i j he; fin_cases i <;> fin_cases j <;> simp_all⟩
  exact fun A => Strategic.exists_value_of_finite three A (Set.toFinite A.val)

/-- info: 'KFOL.Paper.public_neutral_union' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_neutral_union

/-- A role has a strategy winning against all joint opponent replacements
exactly when it is the only possible pure subgame-perfect winner. -/
theorem public_forcing {Role : Type u} (g : Strategic.Tree Role) (i : Role) :
    (∃ p : Strategic.Profile g, ∀ q : Strategic.Profile g,
      Strategic.OpponentDeviation i p q → Strategic.winner q = i) ↔
        Strategic.value g = WinnerSet.singleton i :=
  Strategic.canForce_iff_value_singleton g i

/-- info: 'KFOL.Paper.public_forcing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_forcing

/-- Full public syntax, including internal permutations and independently
solved repeated occurrences, has exactly the algebraic interpretation. -/
theorem public_term_interpretation {Role : Type u} {Var : Type v}
    (components : Var → Strategic.Tree Role) (t : Term Role Var) :
    Strategic.value (Strategic.compile components t) =
      t.eval (fun x => Strategic.value (components x)) :=
  Strategic.value_compile components t

/-- info: 'KFOL.Paper.public_term_interpretation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_term_interpretation

/-- The semantic and expanded-tree clauses of `owner:thm:synthesis`, together
with actual constructor success and saturation order independence. Native
polynomial machine time is recorded as a separate unfinished obligation. -/
theorem owner_table_synthesis {Role : Type u} [DecidableEq Role]
    {Var : Type v} [DecidableEq Var] (T : Owner.GuardTable Var)
    (owner observer background : Role) (hko : observer ≠ owner) (hkb : observer ≠ background)
    (hob : owner ≠ background) (positions : List Var) (hcan : T.Canonical) (hlisted : T.Listed positions) :
    (T.check positions = true ↔ ∃ t : Owner.Term Role Var,
      t.root = T.root ∧ t.OwnersIn (fun a => a = owner) ∧
      ∀ k, k ≠ owner → ∀ valuation : Var → WinnerSet Role,
        k ∈ (t.eval valuation).val ↔
          T.Enabled {i | (valuation i).Ambiguous} {i | valuation i ≠ WinnerSet.singleton owner}
            {i | k ∈ (valuation i).val}) ∧
    ((T.synthesize owner positions).isSome = true ↔ T.check positions = true) ∧
    (∀ t : Owner.Term Role Var, T.synthesize owner positions = some t →
      t.root = T.root ∧ t.OwnersIn (fun a => a = owner) ∧
      (∀ k, k ≠ owner → ∀ valuation : Var → WinnerSet Role,
        k ∈ (t.eval valuation).val ↔
          T.Enabled {i | (valuation i).Ambiguous} {i | valuation i ≠ WinnerSet.singleton owner}
            {i | k ∈ (valuation i).val}) ∧
      t.size ≤ 1 + T.entries.length * (10 * positions.length + 7)) ∧
    (∀ (left right : List Var) (j : Var) (g : Owner.GuardPair Var),
      T.root ∈ g.many → Owner.GuardTable.target j g ⊆ left.toFinset →
      Owner.GuardTable.target j g ⊆ right.toFinset →
      (T.run left j g (2 * left.length)).1 = (T.run right j g (2 * right.length)).1) :=
  ⟨T.check_iff_realizable owner observer background hko hkb hob positions hcan hlisted,
    T.synthesize_isSome owner positions,
    fun _ ht => let h := T.synthesize_spec owner positions ht
                ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩,
    T.run_order_independent⟩

/-- info: 'KFOL.Paper.owner_table_synthesis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_table_synthesis

/-- `owner:prop:four-variables`: a concrete four-element witness transfers
all identities with at most three actual variables, but fails the displayed
valid four-variable identity. Every basis, even infinite, needs four variables. -/
theorem owner_basis_variable_bound :
    letI := Owner.fourStructure (Role := Unit)
    let u : Owner.Term Unit (Fin 4) := .var 0
    let r : Owner.Term Unit (Fin 4) := .var 1
    let y : Owner.Term Unit (Fin 4) := .var 2
    let z : Owner.Term Unit (Fin 4) := .var 3
    let e : Equational.Identity (Owner.Symbol Unit) :=
      ⟨4, Owner.Term.guarded () (Owner.Term.step u r) y z,
        Owner.Term.step (Owner.Term.step u r) (Owner.Term.guarded () r y z)⟩
    Fintype.card Owner.BasisObstruction.Carrier = 4 ∧
    (∀ f : Equational.Identity (Owner.Symbol Unit), f.variableCount ≤ 3 →
      f.Holds Owner.Four → f.Holds Owner.BasisObstruction.Carrier) ∧
    e.Holds Owner.Four ∧ ¬e.Holds Owner.BasisObstruction.Carrier ∧ e.variableCount = 4 ∧
    (∀ (T : Equational.Theory (Owner.Symbol Unit)) (n : ℕ),
      Equational.IsBasis Owner.Four T → (∀ f ∈ T, f.variableCount ≤ n) → 4 ≤ n) := by
  let _ := Owner.fourStructure (Role := Unit)
  exact ⟨by decide, Owner.BasisObstruction.holds_of_variableCount_le,
    Owner.BasisObstruction.rootExpansion_holds, Owner.BasisObstruction.rootExpansion_fails,
    by decide, Owner.BasisObstruction.variableBound_ge_four⟩

/-- info: 'KFOL.Paper.owner_basis_variable_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_basis_variable_bound

/-- `core:thm:no-basis` and `core:thm:core-nfb`: for every finite role set
with three distinct roles and every actual-variable bound there is a finite
countermodel with all small generated subalgebras in the core variety. No
bounded-variable theory, even infinite, is a basis; in particular no finite
basis exists. -/
theorem core_nonfinite_basis {Role : Type u} [DecidableEq Role] [Finite Role]
    (three : Fin 3 ↪ Role) :
    letI := Equational.coreStructure Role
    letI := Core.Native.structureOf (Role := Role)
    (∀ d : ℕ,
      ∃ (B : Type u) (_str : (Equational.language (Equational.CoreSymbol Role)).Structure B),
        Nonempty B ∧ Finite B ∧
        ¬ Equational.InVariety (Equational.CoreSymbol Role) (Core.Native Role) B ∧
        ¬ Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) B ∧
        (∃ e : Equational.Identity (Equational.CoreSymbol Role),
          e.Holds (WinnerSet Role) ∧ ¬ e.Holds B) ∧
        (∀ e : Equational.Identity (Equational.CoreSymbol Role),
          e.variableCount ≤ d → e.Holds (WinnerSet Role) → e.Holds B) ∧
        (∀ X : Finset B, X.card ≤ d →
          Nonempty (FirstOrder.Language.Substructure.closure
            (Equational.language (Equational.CoreSymbol Role)) (X : Set B)) →
          Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role)
            (FirstOrder.Language.Substructure.closure
              (Equational.language (Equational.CoreSymbol Role)) (X : Set B)))) ∧
    (∀ (d : ℕ) (T : Equational.Theory (Equational.CoreSymbol Role)),
      (∀ e ∈ T, e.variableCount ≤ d) →
        ¬(∀ e : Equational.Identity (Equational.CoreSymbol Role),
          e.Holds (WinnerSet Role) ↔ Equational.Derives T e.lhs e.rhs)) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role), T.Finite →
      ¬(∀ e : Equational.Identity (Equational.CoreSymbol Role),
        e.Holds (WinnerSet Role) ↔ Equational.Derives T e.lhs e.rhs)) := by
  let _ := Equational.coreStructure Role
  let _ := Core.Native.structureOf (Role := Role)
  refine ⟨?_, Core.no_basis_with_variable_bound three, ?_⟩
  · intro d
    obtain ⟨B, str, hne, hfinite, hnative, hcore, hlocal⟩ := Core.Grid.finite_local_countermodel three d
    let _ := str
    let _ := hne
    have hfail : ∃ e : Equational.Identity (Equational.CoreSymbol Role),
        e.Holds (WinnerSet Role) ∧ ¬e.Holds B := by
      classical
      by_contra! h
      exact hcore ⟨hne, h⟩
    exact ⟨B, str, hne, hfinite, hnative, hcore, hfail,
      fun e he hv => e.holds_of_local_variety d he hv hlocal, hlocal⟩
  · intro T hfinite hcomplete
    exact Core.not_hasFiniteBasis three ⟨T, hfinite, hcomplete⟩

/-- info: 'KFOL.Paper.core_nonfinite_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.core_nonfinite_basis

/-- `core:cor:ambient-nfb`: the ambient native algebra also has no
bounded-variable basis, even infinite, and consequently no finite basis. -/
theorem native_nonfinite_basis {Role : Type u} [DecidableEq Role] [Finite Role]
    (three : Fin 3 ↪ Role) :
    letI := Core.Native.structureOf (Role := Role)
    (∀ (d : ℕ) (T : Equational.Theory (Equational.CoreSymbol Role)),
      (∀ e ∈ T, e.variableCount ≤ d) →
        ¬(∀ e : Equational.Identity (Equational.CoreSymbol Role),
          e.Holds (Core.Native Role) ↔ Equational.Derives T e.lhs e.rhs)) ∧
    (∀ T : Equational.Theory (Equational.CoreSymbol Role), T.Finite →
      ¬(∀ e : Equational.Identity (Equational.CoreSymbol Role),
        e.Holds (Core.Native Role) ↔ Equational.Derives T e.lhs e.rhs)) := by
  let _ := Core.Native.structureOf (Role := Role)
  refine ⟨Core.native_no_basis_with_variable_bound three, ?_⟩
  intro T hfinite hcomplete
  exact Core.native_not_hasFiniteBasis three ⟨T, hfinite, hcomplete⟩

/-- info: 'KFOL.Paper.native_nonfinite_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.native_nonfinite_basis

/-- `owner:thm:basis-main` and `owner:thm:finite-basis`: the explicitly
indexed thirty-six distinct native identities form a complete basis on the intended
winner-set carrier. Six variables suffice and every basis needs at least four.
The data family in Definitions/Owner is independent of semantic validity. -/
theorem owner_thirty_six_equation_basis {Role : Type u} (three : Fin 3 ↪ Role)
    (owner observer : Role) (ho : observer ≠ owner) :
    letI := Owner.oneOwnerStructure owner
    (Set.range Owner.FiniteBasis.basisAxiom).ncard = 36 ∧
    (Set.range Owner.FiniteBasis.basisAxiom).Finite ∧
    (∀ i : Fin 36, (Owner.FiniteBasis.basisAxiom i).variableCount ≤ 6) ∧
    (∀ e : Equational.Identity (Owner.Symbol Unit), e.Holds (WinnerSet Role) ↔
      Equational.Derives (Set.range Owner.FiniteBasis.basisAxiom) e.lhs e.rhs) ∧
    (∀ (T : Equational.Theory (Owner.Symbol Unit)) (n : ℕ),
      (∀ e : Equational.Identity (Owner.Symbol Unit),
        e.Holds (WinnerSet Role) ↔ Equational.Derives T e.lhs e.rhs) →
      (∀ e ∈ T, e.variableCount ≤ n) → 4 ≤ n) := by
  let _ := Owner.oneOwnerStructure owner
  exact ⟨Owner.FiniteBasis.theory_ncard, Owner.FiniteBasis.theory_finite,
    (fun i => Owner.FiniteBasis.variable_bound _ ⟨i, rfl⟩),
    Owner.FiniteBasis.isBasis_winnerSet three owner observer ho,
    Owner.FiniteBasis.variableBound_ge_four_winnerSet three owner observer ho⟩

/-- info: 'KFOL.Paper.owner_thirty_six_equation_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_thirty_six_equation_basis

/-- The actual native reset/union CNF reduction is correct, has linear
expanded-tree size, is computed in native polynomial time, and establishes
machine-level coNP-hardness of the complete original binary equation language.
The separate coNP upper bound is not included in this component statement. -/
theorem reset_union_reduction {Role : Type u} (three : Fin 3 ↪ Role) :
    (∀ formula : Reductions.CNF,
      ResetUnion.Valid Role (Reductions.ResetUnion.equation formula) ↔
        ¬Reductions.Satisfiable formula) ∧
    (∀ formula : Reductions.CNF,
      (Reductions.ResetUnion.equation formula).1.size +
        (Reductions.ResetUnion.equation formula).2.size ≤
          30 * (formula.length + formula.flatten.length) + 36) ∧
    Turing.MultiTapeTM.ComputableInPolyTime Reductions.ResetUnion.equation
      Complexity.ResetUnionReduction.cnfEncoding Complexity.ResetUnionMachines.equationEncoding ∧
    Cslib.Complexity.coNPHard Turing.MultiTapeTM.encBits (ResetUnion.Language Role) :=
  ⟨Reductions.ResetUnion.valid_equation_iff three, Reductions.ResetUnion.size_equation_linear,
    Complexity.ResetUnionReduction.reduction_polyTime, Complexity.ResetUnionHardness.language_coNPHard three⟩

/-- info: 'KFOL.Paper.reset_union_reduction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_union_reduction

/-- `sym:lem:provenance`: on every fixed singleton/ambiguity status cell,
a term is a finite constant set union finitely permuted ambiguous inputs. -/
theorem status_cell_provenance {Role : Type u} {Var : Type v} (t : Term Role Var)
    (base : Var → WinnerSet Role) :
    ∃ (C : Set Role) (P : Var → Finset (Equiv.Perm Role)), C.Finite ∧
      (∀ j, ∀ p ∈ P j, (base j).Ambiguous) ∧
      ∀ valuation : Var → WinnerSet Role,
        (∀ j r, base j = WinnerSet.singleton r ↔ valuation j = WinnerSet.singleton r) →
        (t.eval valuation).val = C ∪ ⋃ j, ⋃ p ∈ P j, p '' (valuation j).val :=
  t.exists_cell_provenance base

/-- info: 'KFOL.Paper.status_cell_provenance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.status_cell_provenance

open WinnerSet


/-- `view:thm:congruences`: every owned-choice congruence is exactly the kernel of a unique admissible closure, equivalently a unique admissible fixed family, with both converse constructions. -/
theorem congruence_classification {Role : Type u} [Finite Role] [Nonempty Role]
    (three : Fin 3 ↪ Role) :
    (∀ θ : WinnerSet.Congruence Role,
      ∃! c : ClosureOperator (WinnerSet Role),
        (∀ owner, c (singleton owner) = singleton owner ∨ c (singleton owner) = full) ∧
        ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ c : ClosureOperator (WinnerSet Role),
      (∀ owner, c (singleton owner) = singleton owner ∨ c (singleton owner) = full) →
      ∃ θ : WinnerSet.Congruence Role, ∀ A B, θ.r A B ↔ c A = c B) ∧
    (∀ θ : WinnerSet.Congruence Role,
      ∃! F : Set (WinnerSet Role), AdmissibleFamily F ∧
        ∀ A B, θ.r A B ↔ familyClosureValue F A = familyClosureValue F B) ∧
    (∀ F : Set (WinnerSet Role), AdmissibleFamily F →
      ∃ θ : WinnerSet.Congruence Role, ∀ A B,
        θ.r A B ↔ familyClosureValue F A = familyClosureValue F B) := by
  refine ⟨WinnerSet.Congruence.exists_unique_closure three,?_,
    WinnerSet.Congruence.exists_unique_family three,?_⟩
  · intro c hc
    exact ⟨WinnerSet.ClosureOperator.kernel c hc,fun _ _ => Iff.rfl⟩
  · intro F hF
    exact ⟨WinnerSet.ClosureOperator.kernel (familyClosure F) (familyClosure_atom F hF),
      fun _ _ => Iff.rfl⟩

/-- info: 'KFOL.Paper.congruence_classification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.congruence_classification

/-- `view:thm:sym`: the symmetric congruences are precisely the K ambiguity thresholds, with their chain, endpoints and exact quotient cardinalities. -/
theorem symmetric_congruence_chain {Role : Type u} [Finite Role] [Nonempty Role]
    (three : Fin 3 ↪ Role) :
    (∀ θ : SymmetricCongruence Role,
      ∃! m : Fin (Nat.card Role), ∀ A B : WinnerSet Role,
        θ.r A B ↔ threshold m.val A = threshold m.val B) ∧
    (∀ m : Fin (Nat.card Role), ∃ θ : SymmetricCongruence Role, ∀ A B : WinnerSet Role,
      θ.r A B ↔ threshold m.val A = threshold m.val B) ∧
    Nat.card (SymmetricCongruence Role) = Nat.card Role ∧
    (∀ (m n : ℕ), m ≤ n → ∀ A B : WinnerSet Role,
      threshold n A = threshold n B → threshold m A = threshold m B) ∧
    (∀ A : WinnerSet Role, threshold 0 A = full) ∧
    (∀ A : WinnerSet Role, threshold (Nat.card Role - 1) A = A) ∧
    (∀ m : ℕ, m < Nat.card Role →
      Nat.card (Quotient (Setoid.ker (threshold (Role := Role) m))) =
        1 + ∑ j ∈ Finset.Icc 1 m, (Nat.card Role).choose j) := by
  refine ⟨SymmetricCongruence.exists_unique_threshold three,?_,
    SymmetricCongruence.card three,?_,threshold_zero,threshold_last,?_⟩
  · intro m
    exact ⟨WinnerSet.ClosureOperator.symmetricKernel (thresholdClosure m.val)
      (thresholdClosure_atom m.val) (thresholdClosure_invariant m.val),fun _ _ => Iff.rfl⟩
  · intro m n h A B he
    exact threshold_kernel_antitone h A B he
  · intro m hm
    exact card_thresholdQuotient hm

/-- info: 'KFOL.Paper.symmetric_congruence_chain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.symmetric_congruence_chain

/-- The threshold closures are the restrictions of actual uniform matroids: ground, independent sets, rank and closure are all identified. -/
theorem uniform_matroid_identification {Role : Type u} [Finite Role] [Nonempty Role]
    (m : ℕ) (hm : m < Nat.card Role) :
    ∃ M : Matroid Role,
      M.E = Set.univ ∧
      (∀ I : Set Role, M.Indep I ↔ I.ncard ≤ m+1) ∧
      M.eRank = (m+1 : ℕ) ∧
      ∀ A : WinnerSet Role, (WinnerSet.threshold m A).val = M.closure A.val :=
  WinnerSet.uniform_matroid_identification m hm

/-- info: 'KFOL.Paper.uniform_matroid_identification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.uniform_matroid_identification

/-- Native equation validity for reset and union is coNP-complete at every
fixed finite role set with at least three roles, under the original tree codec. -/
theorem reset_union_complexity {Role : Type} [Fintype Role] (three : Fin 3 ↪ Role) :
    Cslib.Complexity.coNPComplete Complexity.ResetUnionMachines.equationEncoding
      {equation : ResetUnion.Equation | ∀ valuation : ℕ → WinnerSet Role,
        equation.1.eval valuation = equation.2.eval valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits (ResetUnion.Language Role) :=
  ⟨Complexity.ResetUnionCompleteness.coNPComplete three,
    Complexity.ResetUnionWordCompleteness.coNPComplete three⟩

/-- info: 'KFOL.Paper.reset_union_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_union_complexity

/-- Internal role switches make every one-player polynomial observation
faithful, including contexts with arbitrary nonempty ground parameters. -/
theorem switching_observation {Role : Type u} (k : Role) (A B : WinnerSet Role) :
    (∀ (n : ℕ) (t : Term Role (Option (Fin n))) (parameters : Fin n → WinnerSet Role),
      (k ∈ (t.eval (fun x => x.elim A parameters)).val ↔
        k ∈ (t.eval (fun x => x.elim B parameters)).val)) ↔ A = B :=
  Term.full_polynomial_contextual_iff_eq k A B

/-- info: 'KFOL.Paper.switching_observation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.switching_observation

open Dissemilattice in
/-- All seven laws and their exact generating variety are repeated here;
the two semilattice orders are not identified by absorption. -/
theorem choice_union_basis {Role : Type v} (three : Fin 3 ↪ Role) (owner : Role) :
    letI := winnerStructure owner
    theory.ncard = 7 ∧ theory.Finite ∧ Equational.IsBasis (WinnerSet Role) theory ∧
    (∀ (M : Type u) [_str : (Equational.language Symbol).Structure M],
      Equational.InVariety Symbol (WinnerSet Role) M ↔
        Nonempty M ∧
        (∀ x : M, add x x = x) ∧
        (∀ x y : M, add x y = add y x) ∧
        (∀ x y z : M, add (add x y) z = add x (add y z)) ∧
        (∀ x : M, mul x x = x) ∧
        (∀ x y : M, mul x y = mul y x) ∧
        (∀ x y z : M, mul (mul x y) z = mul x (mul y z)) ∧
        (∀ x y z : M, mul x (add y z) = add (mul x y) (mul x z))) := by
  let _ := winnerStructure owner
  refine ⟨theory_ncard,theory_finite,basis_winner three owner,?_⟩
  intro M _
  constructor
  · intro hM
    obtain ⟨hne,hL⟩ := (inVariety_winner_iff_laws three owner M).mp hM
    exact ⟨hne,hL.add_idem,hL.add_comm,hL.add_assoc,hL.mul_idem,hL.mul_comm,hL.mul_assoc,hL.mul_add⟩
  · rintro ⟨hne,h1,h2,h3,h4,h5,h6,h7⟩
    exact (inVariety_winner_iff_laws three owner M).mpr ⟨hne,⟨h1,h2,h3,h4,h5,h6,h7⟩⟩

/-- info: 'KFOL.Paper.choice_union_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.choice_union_basis

/-- Complete paper-facing S2 statement, including actual term realization. -/
theorem atomic_functions {Role : Type u} [Finite Role] (three : Fin 3 ↪ Role)
    {Var : Type v} [Finite Var] [Nonempty Var] (f : (Var → Role) → Role) :
    (∃ t : Term Role Var,
      (∀ x : Var → Role, ∃ r,
        t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r) ∧
      (∀ x : Var → Role,
        t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton (f x))) ↔
      (∃ i : Var, ∃ g : Role → Role, ∀ x, f x = g (x i)) ∨
      (∃ a b : Role, ∀ x, f x = a ∨ f x = b) := by
  let _ : Nonempty Role := ⟨three 0⟩
  exact Term.atomic_function_classification_with_preservation f

/-- info: 'KFOL.Paper.atomic_functions' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.atomic_functions

/-- Complete determinacy corollary; no finite label hypothesis is needed. -/
theorem determinacy {Role : Type u} (three : Fin 3 ↪ Role)
    {Var : Type v} [Finite Var] (t : Term Role Var)
    (ha : ∀ x : Var → Role, ∃ r,
      t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    ∃ i : Var, ∀ x : Var → Role,
      t.eval (fun j => WinnerSet.singleton (x j)) = WinnerSet.singleton (x i) :=
  t.atomic_determinacy three ha (fun r => hd (WinnerSet.singleton r))

/-- info: 'KFOL.Paper.determinacy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.determinacy

/-- Complete binary classification with explicit public-language hypotheses. -/
theorem binary_atom_preserving {Role : Type u} (three : Fin 3 ↪ Role) (t : Term Role (Fin 2))
    (ha : ∀ x : Fin 2 → Role, ∃ r,
      t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r)
    (hd : ∀ A : WinnerSet Role, t.eval (fun _ => A) = A) :
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = v 0) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = v 1) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = (v 0).reset (v 1)) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = (v 1).reset (v 0)) :=
  t.binary_atom_preserving three ha hd

/-- info: 'KFOL.Paper.binary_atom_preserving' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.binary_atom_preserving

/-- Complete converse: all four and only these have a realizing idempotent,
atom-preserving core term. -/
theorem binary_atom_preserving_iff {Role : Type u} [Finite Role] (three : Fin 3 ↪ Role)
    (f : (Fin 2 → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role (Fin 2), t.IsCore ∧
      (∀ x : Fin 2 → Role, ∃ r,
        t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r) ∧
      (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧ (∀ v, t.eval v = f v)) ↔
    (∀ v : Fin 2 → WinnerSet Role, f v = v 0) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = v 1) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = (v 0).reset (v 1)) ∨
    (∀ v : Fin 2 → WinnerSet Role, f v = (v 1).reset (v 0)) :=
  Term.binary_operation_classification three f

/-- info: 'KFOL.Paper.binary_atom_preserving_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.binary_atom_preserving_iff

open Classical in
/-- Complete two-player strong-Kleene identification. -/
theorem two_player_identification {Role : Type u} (labels : Fin 2 ≃ Role) :
    ∃ q : WinnerSet Role ≃ Fin 3,
      (∀ i, q (TwoPlayers.value labels i) = i) ∧
      (∀ A B, q (WinnerSet.choice (labels 0) A B) = max (q A) (q B)) ∧
      (∀ A B, q (WinnerSet.choice (labels 1) A B) = min (q A) (q B)) ∧
      (∀ A, q (WinnerSet.rename (Equiv.swap (labels 0) (labels 1)) A) = (q A).rev) :=
  TwoPlayers.strong_kleene_identification labels


/-- info: 'KFOL.Paper.two_player_identification' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.two_player_identification

/-- Exact two-player degeneracies, atomicity and failure of the three-player
idempotent-core characterization, using the same winner carrier and syntax. -/
theorem two_player_degeneracies {Role : Type u} (labels : Fin 2 ≃ Role) :
    (∀ A B : WinnerSet Role, A.reset B = B) ∧
    (∀ (r : Role) (X Y Z : WinnerSet Role), WinnerSet.guardedChoice r X Y Z = X) ∧
    (∀ (D : Set Role) (X Y Z : WinnerSet Role), WinnerSet.policyReset D X Y Z = X) ∧
    (∀ (Var : Type v) (t : Term Role Var), ∀ x : Var → Role, ∃ r,
      t.eval (fun i => WinnerSet.singleton (x i)) = WinnerSet.singleton r) ∧
    (∀ t : Term Role Empty, ∃ r, t.eval Empty.elim = WinnerSet.singleton r) ∧
    (¬∃ t : Term Role (Fin 2), ∀ x : Fin 2 → WinnerSet Role,
      t.eval x = (x 0).union (x 1)) ∧
    (∃ t : Term Role (Fin 2), (∀ A : WinnerSet Role, t.eval (fun _ => A) = A) ∧
      ¬∃ s : Term Role (Fin 2), s.IsCore ∧ ∀ x, s.eval x = t.eval x) := by
  refine ⟨TwoPlayers.reset_projection labels,TwoPlayers.guardedChoice_projection labels,
    TwoPlayers.policyReset_projection labels,?_,?_,TwoPlayers.union_not_definable labels,
    TwoPlayers.idempotent_not_core labels⟩
  · intro Var t
    exact TwoPlayers.atom_preserving labels t
  · intro t
    exact TwoPlayers.closed_atomic labels t Empty.elim

/-- info: 'KFOL.Paper.two_player_degeneracies' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.two_player_degeneracies

/-- The fully expanded two-owner selective operation strictly extends reset:
no reset-only term of any depth defines it. -/
theorem strict_two_owner_policy {Role : Type u} (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬∃ t : Reset.Term (Fin 3), ∀ x : Fin 3 → WinnerSet Role,
      t.eval x = (WinnerSet.choice a (WinnerSet.choice b (x 1) (x 2)) (x 1)).reset (x 0) :=
  Policies.twoOwnerSelective_not_reset_definable a b c hab hac hbc

/-- info: 'KFOL.Paper.strict_two_owner_policy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.strict_two_owner_policy

/-- In both independently specified tractable family cases, the actual
native syntax checker decides full equality on every winner-set valuation. -/
theorem policy_family_checker {Role : Type u} {Label : Type v} {Var : Type w}
    [DecidableEq Role] [DecidableEq Label] [DecidableEq Var]
    (three : Fin 3 ↪ Role) (D : Label → Finset Role)
    (roles : List Role) (labels : List Label)
    (hroles : ∀ r, r ∈ roles) (hlabels : ∀ d, d ∈ labels)
    (heasy :
      (∀ r s,
        Policies.passingPattern (fun d => (D d : Set Role)) r ⊆
          Policies.passingPattern (fun d => (D d : Set Role)) s ∨
        Policies.passingPattern (fun d => (D d : Set Role)) s ⊆
          Policies.passingPattern (fun d => (D d : Set Role)) r) ∨
      ((∀ r s, ∃ t,
        Policies.passingPattern (fun d => (D d : Set Role)) t =
          Policies.passingPattern (fun d => (D d : Set Role)) r ∩
            Policies.passingPattern (fun d => (D d : Set Role)) s) ∧
        ∃ r s, r ≠ s ∧ Policies.passingPattern (fun d => (D d : Set Role)) r =
          Policies.passingPattern (fun d => (D d : Set Role)) s))
    (left right : Policies.Term Label Var) :
    Policies.Term.familyEquationB D roles labels left right = true ↔
      ∀ x : Var → WinnerSet Role,
        left.eval (fun d => (D d : Set Role)) x = right.eval (fun d => (D d : Set Role)) x :=
  Policies.Term.familyEquationB_correct three D roles labels hroles hlabels heasy left right

/-- info: 'KFOL.Paper.policy_family_checker' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.policy_family_checker

/-- Native polynomial time for the complete independent owner-table checker,
uniformly in the unary dimension and with no promise about canonicality. -/
theorem owner_table_runtime :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun input : (n : ℕ) × Owner.GuardTable (Fin n) =>
        input.2.check (List.finRange input.1))
      Complexity.OwnerRuntime.inputEncoding Turing.MultiTapeTM.encBool :=
  Complexity.OwnerRuntime.source_check_polyTime

/-- info: 'KFOL.Paper.owner_table_runtime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_table_runtime

/-- General finite-menu round execution has actual finite histories, public
recall, serial decision recall and canonical sequential equilibria. The
serial/observed equilibrium equivalence and value recursion are separate. -/
theorem round_protocol_foundations {Role : Type u} [Fintype Role] [DecidableEq Role]
    (game : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
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
  ⟨inferInstance,inferInstance,game.perfect_recall,game.serial_decision_recall order,
    game.reachable_position,game.every_history_subgame_root,game.exists_bounded_horizon,
    game.serial_exists_bounded_horizon order,game.serial_exists_sequential_equilibrium order⟩

/-- info: 'KFOL.Paper.round_protocol_foundations' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.round_protocol_foundations

/-- Native polynomial time for the actual owner-table synthesizer, including
rejection and the complete expanded output tree, for a fixed finite role alphabet. -/
theorem owner_synthesis_runtime {Role : Type} [Fintype Role] (owner : Role) :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun input : (n : ℕ) × Owner.GuardTable (Fin n) =>
        (input.2.synthesize owner (List.finRange input.1)).map
          (fun term => (⟨input.1,term⟩ : (n : ℕ) × Owner.Term Role (Fin n))))
      Complexity.OwnerRuntime.inputEncoding
      (Turing.MultiTapeTM.encOption (Complexity.OwnerRuntime.outputEncoding (Role := Role))) :=
  Complexity.OwnerRuntime.source_synthesize_polyTime owner

/-- info: 'KFOL.Paper.owner_synthesis_runtime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_synthesis_runtime

/-- Original Boolean-product statement, with arbitrary product index and
arbitrary coordinate choice of meet or join for every owned operation. -/
theorem no_boolean_product {Role : Type u} (three : Fin 3 ↪ Role)
    {Index : Type v} (M : Index → Type w) [∀ i, BooleanAlgebra (M i)]
    (select : Role → Index → Bool) :
    ¬∃ f : WinnerSet Role → ∀ i, M i, Function.Injective f ∧
      (∀ r A B i, f (WinnerSet.choice r A B) i =
        if select r i then f A i ⊔ f B i else f A i ⊓ f B i) := by
  rintro ⟨f,hinj,hf⟩
  exact WinnerSet.no_boolean_product_embedding three M select f hf hinj


/-- info: 'KFOL.Paper.no_boolean_product' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.no_boolean_product

/-- The full unique-winner observation assertion, with arbitrary parameters. -/
theorem unique_winner_observations {Role : Type u} {Var : Type v} (t : Term Role Var)
    (ht : t.IsPublic) (active : Var → Bool) (parameters : Var → WinnerSet Role) :
    ((∃ C : WinnerSet Role, ∀ X : WinnerSet Role,
      t.eval (fun x => if active x then X else parameters x) = C) ∨
      (∀ X : WinnerSet Role, X.val ⊆
        (t.eval (fun x => if active x then X else parameters x)).val)) ∧
    (∀ A B : WinnerSet Role, A.Ambiguous → B.Ambiguous → ∀ r,
      (t.eval (fun x => if active x then A else parameters x) = WinnerSet.singleton r) ↔
        (t.eval (fun x => if active x then B else parameters x) = WinnerSet.singleton r)) :=
  ⟨ht.unary_constant_or_extensive active parameters,
    fun A B hA hB r => ht.ambiguous_singleton_observation active parameters A B hA hB r⟩


/-- info: 'KFOL.Paper.unique_winner_observations' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.unique_winner_observations

/-- Membership observations at all roles distinguish every winner set already
through the identity context. -/
theorem membership_observations {Role : Type u} (A B : WinnerSet Role) :
    (∀ r : Role, r ∈ A.val ↔ r ∈ B.val) ↔ A = B := by
  constructor
  · intro h
    exact Subtype.ext (Set.ext h)
  · intro h
    subst B
    exact fun _ => Iff.rfl

/-- info: 'KFOL.Paper.membership_observations' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.membership_observations

/-- Every extensive unary term has an actual term reset fixing each atom and
preserving its complete behavior on ambiguous inputs. -/
theorem unary_atomic_reset {Role : Type u} [Finite Role] (t : Term Role (Fin 1))
    (hext : ∀ X : WinnerSet Role, X.val ⊆ (t.eval (fun _ => X)).val) :
    ∃ s : Term Role (Fin 1),
      (∀ r, s.eval (fun _ => WinnerSet.singleton r) = WinnerSet.singleton r) ∧
      (∀ X : WinnerSet Role, X.Ambiguous → s.eval (fun _ => X) = t.eval (fun _ => X)) ∧
      (∀ X : WinnerSet Role, X.val ⊆ (s.eval (fun _ => X)).val) :=
  t.exists_unary_reset hext

/-- info: 'KFOL.Paper.unary_atomic_reset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.unary_atomic_reset

/-- Every finite nonempty family of continuations folds to an actual binary
term; its owner-absorption and union cases hold for every valuation. -/
theorem finite_public_choices {Role : Type u} {Var : Type v} {Index : Type w}
    (r : Role) (S : Finset Index) (hS : S.Nonempty) (terms : Index → Term Role Var) :
    (∃ t : Term Role Var, ∀ v : Var → WinnerSet Role,
      t.eval v = WinnerSet.choiceFold r S hS (fun i => (terms i).eval v)) ∧
    (∀ v : Var → WinnerSet Role,
      WinnerSet.choiceFold r S hS (fun i => (terms i).eval v) = WinnerSet.singleton r ↔
        ∃ i ∈ S, (terms i).eval v = WinnerSet.singleton r) ∧
    (∀ v : Var → WinnerSet Role, (∀ i ∈ S, (terms i).eval v ≠ WinnerSet.singleton r) →
      ∀ a : Role, a ∈ (WinnerSet.choiceFold r S hS (fun i => (terms i).eval v)).val ↔
        ∃ i ∈ S, a ∈ ((terms i).eval v).val) :=
  ⟨Term.exists_choice_fold r S hS terms,
    fun v => WinnerSet.choiceFold_eq_owner_iff r S hS (fun i => (terms i).eval v),
    fun v hn a => WinnerSet.mem_choiceFold_of_no_owner r S hS (fun i => (terms i).eval v) hn a⟩


/-- info: 'KFOL.Paper.finite_public_choices' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.finite_public_choices

/-- Complete actual quotient table and explicit layered semilattice order. -/
theorem player_view_orders {Role : Type u} (three : Fin 3 ↪ Role) (k r : Role) :
    (∀ A B : WinnerSet Role, WinnerSet.view k (WinnerSet.choice r A B) =
      PlayerView.choice r (WinnerSet.view k A) (WinnerSet.view k B)) ∧
    ∃ order : SemilatticeSup (PlayerView k),
      (let _ := order
       (∀ p q : PlayerView k, p ⊔ q = PlayerView.choice r p q) ∧
       (∀ p q : PlayerView k, p ≤ q ↔ match p,q with
         | .possible,.possible => True
         | .possible,.impossible => False
         | .possible,.other j => j.val = r
         | .impossible,.possible | .impossible,.impossible => True
         | .impossible,.other j => j.val = r
         | .other i,.possible | .other i,.impossible => i.val ≠ r
         | .other i,.other j => i = j ∨ j.val = r)) := by
  refine ⟨WinnerSet.view_choice k r,PlayerView.semilatticeSup three k r,?_,?_⟩
  · exact fun _ _ => rfl
  · exact PlayerView.order_layers three k r


/-- info: 'KFOL.Paper.player_view_orders' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.player_view_orders

/-- A concrete finite basis for the full two-player signature, together with
complete equational derivability for every original public-language identity. -/
theorem two_player_finite_basis {Role : Type u} (labels : Fin 2 ≃ Role) :
    let _ := TwoPlayers.Kleene.winnerStructure labels
    TwoPlayers.Kleene.basis.Finite ∧
    (∀ e : Equational.Identity TwoPlayers.Kleene.Symbol,
      e.Holds (WinnerSet Role) ↔ Equational.Derives TwoPlayers.Kleene.basis e.lhs e.rhs) ∧
    (∀ (n : ℕ) (s t : Term Role (Fin n)),
      (∀ x : Fin n → WinnerSet Role, s.eval x = t.eval x) ↔
        Equational.Derives TwoPlayers.Kleene.basis
          (TwoPlayers.Kleene.ofPublic labels s) (TwoPlayers.Kleene.ofPublic labels t)) := by
  let _ := TwoPlayers.Kleene.winnerStructure labels
  exact ⟨TwoPlayers.Kleene.basis_finite,TwoPlayers.Kleene.basis_winner labels,
    TwoPlayers.Kleene.public_equational_completeness labels⟩

/-- info: 'KFOL.Paper.two_player_finite_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.two_player_finite_basis

/-- Complete original-word equality checking for one owner, with runtime
independent of the ambient role count. Malformed inner or outer words reject. -/
theorem owner_original_word_checker {Role : Type u} [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owner observer : Role) (hne : observer ≠ owner) :
    Turing.MultiTapeTM.ComputableInPolyTime Complexity.OwnerTermFrontend.checkWord
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBool ∧
    ∀ word : List Bool, Complexity.OwnerTermFrontend.checkWord word = true ↔
      ∃ left right : Owner.Term Unit ℕ,
        FiniteTermCode.encodeEquation (Owner.Symbol Unit) (left,right) = word ∧
        ∀ x : ℕ → WinnerSet Role,
          (left.withOwner owner).eval x = (right.withOwner owner).eval x :=
  ⟨Complexity.OwnerTermFrontend.checkWord_polyTime,
    Complexity.OwnerTermFrontend.checkWord_iff three owner observer hne⟩

/-- info: 'KFOL.Paper.owner_original_word_checker' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_original_word_checker

/-- Every finite policy family outside the tractable criterion has an actual
native CNF reduction, with sparse natural-number names and arbitrary valuations. -/
theorem policy_family_reduction {Role : Type u} {Label : Type v}
    [Fintype Role] [Fintype Label] (D : Label → Set Role) (three : Fin 3 ↪ Role)
    (code : Role ↪ ℕ) (hne : ¬Policies.FamilyEasy D) :
    ∃ plan : Policies.Hardness.Plan Role Label, ∀ formula : Reductions.CNF,
      (∀ x : ℕ → WinnerSet Role,
        Policies.Term.eval D ((plan.equation formula).1.relabel (Policies.Hardness.Variable.toNat code)) x =
          Policies.Term.eval D ((plan.equation formula).2.relabel (Policies.Hardness.Variable.toNat code)) x) ↔
        ¬Reductions.Satisfiable formula :=
  Policies.non_easy_family_nat_cnf_reduction D three code hne

/-- info: 'KFOL.Paper.policy_family_reduction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.policy_family_reduction

/-- Two guarded owners alone admit the exact native UNSAT reduction, also
for a third role's membership observation; no primitive reset is in the target. -/
theorem guarded_pair_reduction {Role : Type u} (a b d : Role)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) (formula : Reductions.CNF) :
    ((∀ x : ℕ → WinnerSet Role,
      (Reductions.GuardedPair.equation formula).1.eval a b x =
        (Reductions.GuardedPair.equation formula).2.eval a b x) ↔
      ¬Reductions.Satisfiable formula) ∧
    ((∀ x : ℕ → WinnerSet Role,
      d ∈ ((Reductions.GuardedPair.equation formula).1.eval a b x).val ↔
        d ∈ ((Reductions.GuardedPair.equation formula).2.eval a b x).val) ↔
      ¬Reductions.Satisfiable formula) ∧
    ((Reductions.GuardedPair.equation formula).1.size +
      (Reductions.GuardedPair.equation formula).2.size =
      5 + 6 * (Reductions.ResetUnion.support formula).length + 6 * formula.length +
        12 * (formula.map List.length).sum) :=
  ⟨Reductions.GuardedPair.equation_valid_iff_unsatisfiable a b d hab had hbd formula,
    Reductions.GuardedPair.third_role_observation_valid_iff_unsatisfiable a b d hab had hbd formula,
    Reductions.GuardedPair.equation_size formula⟩

/-- info: 'KFOL.Paper.guarded_pair_reduction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.guarded_pair_reduction

/-- The actual serial-SE winner values are nonempty and have the exact
Dirac leaf equation. Both statements use independent canonical SE semantics. -/
theorem round_sequential_values {Role : Type u} [Fintype Role] [DecidableEq Role]
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    (∀ game : Rounds.Game Role, (game.sequentialValues order).Nonempty) ∧
    (∀ r : Role, (Rounds.Game.leaf r).sequentialValues order = {PMF.pure r}) :=
  ⟨fun game => game.sequentialValues_nonempty order,
    fun r => Rounds.Game.sequentialValues_leaf r order⟩

/-- info: 'KFOL.Paper.round_sequential_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.round_sequential_values

/-- Arbitrary behavioral strategies admit consistent assessments. At every
actual serial decision their beliefs are the product of earlier current laws,
including public histories unreachable under the supplied strategy. -/
theorem round_profile_consistency {Role : Type u} [DecidableEq Role] [Finite Role]
    (game : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (strategy : (i : Role) → (game.serialized order).information.BehavioralPolicy i) :
    ∃ assessment : (game.serialized order).information.BehavioralAssessment,
      assessment.strategy = strategy ∧
      assessment.IsSequentiallyConsistent
        (game.serial_decision_recall order).decisionInformationAntichain ∧
      ∀ (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role),
        assessment.belief i (game.serialSite order h ht i) =
          game.productBelief order strategy h ht i :=
  game.exists_consistent_product_assessment order strategy

/-- info: 'KFOL.Paper.round_profile_consistency' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.round_profile_consistency

/-- Consistency uniquely determines the product belief at every public
history; no positive-reach condition occurs at the limit. -/
theorem round_product_beliefs {Role : Type u} [DecidableEq Role] [Finite Role]
    (game : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (assessment : (game.serialized order).information.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (game.serial_decision_recall order).decisionInformationAntichain) :
    ∀ (h : game.execution.History) (ht : ¬ game.execution.terminal h.state) (i : Role),
      assessment.belief i (game.serialSite order h ht i) =
        game.productBelief order assessment.strategy h ht i :=
  game.consistent_belief_eq_product order assessment consistent

/-- info: 'KFOL.Paper.round_product_beliefs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.round_product_beliefs

/-- Each owned operation is a mathlib semilattice join, with the owner's atom
as top and the exact underlying set-inclusion order on all other values. -/
theorem owned_choice_semilattices {Role : Type u} (r : Role) :
    ∃ s : SemilatticeSup (WinnerSet Role),
      (∀ A B : WinnerSet Role, @Max.max (WinnerSet Role) s.toMax A B = WinnerSet.choice r A B) ∧
      (∀ A B : WinnerSet Role, @LE.le (WinnerSet Role) s.toLE A B ↔
        B = WinnerSet.singleton r ∨ (A ≠ WinnerSet.singleton r ∧ A.val ⊆ B.val)) :=
  ⟨WinnerSet.choiceSemilattice r,fun _ _ => rfl,WinnerSet.choice_le_iff r⟩

/-- info: 'KFOL.Paper.owned_choice_semilattices' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owned_choice_semilattices

open Classical in
/-- The two forcing observations jointly embed the two-player carrier, with
both owned operations, the role switch and the exact Boolean-coordinate image. -/
theorem two_player_forcing_coordinates {Role : Type u} (labels : Fin 2 ≃ Role) :
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
  ⟨TwoPlayers.forcingCoordinates_injective labels,TwoPlayers.forcingCoordinates_choice_top labels,
    TwoPlayers.forcingCoordinates_choice_bottom labels,TwoPlayers.forcingCoordinates_swap labels,
    TwoPlayers.forcingCoordinates_range labels⟩

/-- info: 'KFOL.Paper.two_player_forcing_coordinates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.two_player_forcing_coordinates

/-- `se:thm:round`: independently defined serial sequential-equilibrium and
observed mixed-SPE winner values coincide. Leaves have their Dirac value;
every round selects a continuation equilibrium at every actual joint action
and a canonical independent mixed Nash equilibrium of the resulting stage. -/
theorem round_equilibrium_recursion {Role : Type u} [Fintype Role] [DecidableEq Role]
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    (∀ game : Rounds.Game Role, game.sequentialValues order = game.observedValues) ∧
    (∀ r : Role, (Rounds.Game.leaf r).sequentialValues order = {PMF.pure r}) ∧
    (∀ (sizes : Role → ℕ) (next : ((i : Role) → Fin (sizes i+1)) → Rounds.Game Role)
      (value : PMF Role),
      value ∈ (Rounds.Game.round sizes next).sequentialValues order ↔
        ∃ p : ((i : Role) → Fin (sizes i+1)) → PMF Role,
          (∀ a, p a ∈ (next a).sequentialValues order) ∧
          ∃ root : GameTheory.Profile (Rounds.Game.stageForm sizes p).sig.mixed,
            GameTheory.IsNash (Rounds.Game.stageForm sizes p).mixed
              (GameTheory.euPreference (fun winner i => Rounds.Game.winnerPayoff id i winner)) root ∧
            value = (Rounds.Game.stageForm sizes p).mixed.play root) :=
  ⟨fun game => game.sequentialValues_eq_observedValues order,
    fun r => Rounds.Game.sequentialValues_leaf r order,
    fun sizes next value => Rounds.Game.sequentialValues_round_iff sizes next order value⟩

/-- info: 'KFOL.Paper.round_equilibrium_recursion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.round_equilibrium_recursion

/-- The three hard raw pairs have actual native CNF reductions, valid on
all independent winner-set assignments exactly for unsatisfiable inputs.
The original binary trees have linear size, including empty-input gates. -/
theorem raw_pair_reductions {Role : Type u} (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (formula : Reductions.CNF) :
    ((∀ v : ℕ → WinnerSet Role,
      (Reductions.RawPair.equation formula).1.eval (WinnerSet.choice a) WinnerSet.union v =
        (Reductions.RawPair.equation formula).2.eval (WinnerSet.choice a) WinnerSet.union v) ↔
      ¬Reductions.Satisfiable formula) ∧
    ((∀ v : ℕ → WinnerSet Role,
      (Reductions.RawPair.twoOwnerEquation formula).1.eval (WinnerSet.choice a) (WinnerSet.choice b) v =
        (Reductions.RawPair.twoOwnerEquation formula).2.eval (WinnerSet.choice a) (WinnerSet.choice b) v) ↔
      ¬Reductions.Satisfiable formula) ∧
    ((∀ v : ℕ → WinnerSet Role,
      (Reductions.ResetChoice.equation formula).1.eval WinnerSet.reset (WinnerSet.choice a) v =
        (Reductions.ResetChoice.equation formula).2.eval WinnerSet.reset (WinnerSet.choice a) v) ↔
      ¬Reductions.Satisfiable formula) ∧
    (Reductions.RawPair.equation formula).1.size + (Reductions.RawPair.equation formula).2.size ≤
      4 + 20 * (Reductions.ResetUnion.support formula).length + 2 * (formula.map List.length).sum ∧
    (Reductions.RawPair.twoOwnerEquation formula).1.size + (Reductions.RawPair.twoOwnerEquation formula).2.size ≤
      4 + 20 * (Reductions.ResetUnion.support formula).length + 2 * (formula.map List.length).sum ∧
    (Reductions.ResetChoice.equation formula).1.size + (Reductions.ResetChoice.equation formula).2.size ≤
      28 * (Reductions.ResetUnion.support formula).length +
        2 * formula.length + 2 * formula.flatten.length + 8 := by
  exact ⟨Reductions.RawPair.union_equation_valid_iff_unsatisfiable a b c hab hac hbc.symm formula,
    Reductions.RawPair.twoOwners_equation_valid_iff_unsatisfiable a b c hab hac hbc.symm formula,
    Reductions.ResetChoice.equation_valid_iff_unsatisfiable a b c hab hac hbc formula,
    Reductions.RawPair.equation_size_le formula,
    Reductions.RawPair.twoOwnerEquation_size_le formula,
    Reductions.ResetChoice.equation_size_le formula⟩

/-- info: 'KFOL.Paper.raw_pair_reductions' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.raw_pair_reductions

/-- `thm:colouring-theories`: the complete reset/union identity theories
strictly decrease at every successive role count from three onward. -/
theorem role_count_identity_theories (n : ℕ) (hn : 3 ≤ n) :
    {e : Equational.Identity ResetUnion.Symbol |
      letI := ResetUnion.structureOf (Role := Fin (n+1))
      e.Holds (WinnerSet (Fin (n+1)))} ⊂
    {e : Equational.Identity ResetUnion.Symbol |
      letI := ResetUnion.structureOf (Role := Fin n)
      e.Holds (WinnerSet (Fin n))} :=
  Reductions.Colouring.theory_succ_ssubset n hn

/-- info: 'KFOL.Paper.role_count_identity_theories' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.role_count_identity_theories

/-- Two distinct guarded owners give coNP-complete native validity and the
same exact third-role observation problem. Both claims include the full
binary input languages, with malformed inputs rejected. The role set here
is fixed; uniform role-parameter complexity is a separate theorem. -/
theorem guarded_pair_complexity {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete Complexity.GuardedPairMachines.equationEncoding
      {equation : GuardedPair.Term ℕ × GuardedPair.Term ℕ |
        ∀ valuation : ℕ → WinnerSet Role,
          equation.1.eval a b valuation = equation.2.eval a b valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : GuardedPair.Term ℕ × GuardedPair.Term ℕ,
        FiniteTermCode.encodeEquation GuardedPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            equation.1.eval a b valuation = equation.2.eval a b valuation} ∧
    Cslib.Complexity.coNPComplete Complexity.GuardedPairMachines.equationEncoding
      {equation : GuardedPair.Term ℕ × GuardedPair.Term ℕ |
        ∀ valuation : ℕ → WinnerSet Role,
          d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : GuardedPair.Term ℕ × GuardedPair.Term ℕ,
        FiniteTermCode.encodeEquation GuardedPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            d ∈ (equation.1.eval a b valuation).val ↔ d ∈ (equation.2.eval a b valuation).val} :=
  ⟨Complexity.GuardedPairCompleteness.coNPComplete a b d hab had hbd,
    Complexity.GuardedPairCompleteness.language_coNPComplete a b d hab had hbd,
    Complexity.GuardedPairCompleteness.observation_coNPComplete a b d hab had hbd,
    Complexity.GuardedPairCompleteness.observation_language_coNPComplete a b d hab had hbd⟩

/-- info: 'KFOL.Paper.guarded_pair_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.guarded_pair_complexity

/-- `se:cor:public`: on every public tree, possible mixed sequential winners
are exactly the independently defined pure SPE winners. Every such winner
also remains attainable as its Dirac equilibrium distribution. -/
theorem public_mixed_support {Role : Type u} [Fintype Role] [DecidableEq Role]
    (tree : Strategic.Tree Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    Rounds.Game.possibleWinners ((Rounds.Game.publicTree tree).sequentialValues order) =
      (Strategic.value tree).val ∧
    ∀ i ∈ (Strategic.value tree).val,
      PMF.pure i ∈ (Rounds.Game.publicTree tree).sequentialValues order :=
  ⟨Rounds.Game.possibleWinners_publicTree tree order,
    (Rounds.Game.publicTree_support_and_dirac tree order).2⟩

/-- info: 'KFOL.Paper.public_mixed_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_mixed_support

/-- Exact nonconvexity and failure of distribution-level public idempotence.
The two occurrences in the repeated tree have independent continuation
policies, so the omitted midpoint becomes attainable there. -/
theorem public_nonconvexity {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    (Rounds.Game.publicChoice a
      (Rounds.Game.publicChoice c (.leaf a) (.leaf b)) (.leaf c)).sequentialValues order =
      {value | ∃ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1),
        value = GameTheory.Math.Probability.mix α h0 h1 (PMF.pure a) (PMF.pure b)} ∪
      {value | ∃ (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1),
        value = GameTheory.Math.Probability.mix α h0 h1 (PMF.pure b) (PMF.pure c)} ∧
    (let midpoint := GameTheory.Math.Probability.mix (1/2 : ℝ) (by norm_num) (by norm_num)
      (PMF.pure a) (PMF.pure c)
     midpoint ∉ (Rounds.Game.publicChoice a
       (Rounds.Game.publicChoice c (.leaf a) (.leaf b)) (.leaf c)).sequentialValues order ∧
     midpoint ∈ (Rounds.Game.publicChoice b
       (Rounds.Game.publicChoice a (Rounds.Game.publicChoice c (.leaf a) (.leaf b)) (.leaf c))
       (Rounds.Game.publicChoice a (Rounds.Game.publicChoice c (.leaf a) (.leaf b)) (.leaf c))).sequentialValues order) :=
  ⟨Rounds.Game.Public.example_values a b c hab hac hbc order,
    Rounds.Game.Public.midpoint_not_mem_example a b c hab hac hbc order,
    Rounds.Game.Public.midpoint_mem_repeated_example a b c hab hac hbc order⟩

/-- info: 'KFOL.Paper.public_nonconvexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_nonconvexity

/-- Constant-sum games with only the designated pair active have a unique
actual equilibrium winner law, even in a larger ambient role type. -/
theorem constant_sum_round_values {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (hab : a ≠ b) (game : Rounds.Game Role)
    (uses : game.UsesOnly a b)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    ∃ (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1),
      game.sequentialValues order =
        {GameTheory.Math.Probability.mix x h0 h1 (PMF.pure a) (PMF.pure b)} :=
  Rounds.Game.TwoPlayers.sequentialValues_scalar a b hab game uses order

/-- info: 'KFOL.Paper.constant_sum_round_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.constant_sum_round_values

/-- The actual diagonal commitment game has parallel-sum value, with the same
formula at either or both zero boundaries. -/
theorem scalar_diagonal_values {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (hab : a ≠ b) (left right : Rounds.Game Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (hleft : left.sequentialValues order =
      {GameTheory.Math.Probability.mix x hx0 hx1 (PMF.pure a) (PMF.pure b)})
    (hright : right.sequentialValues order =
      {GameTheory.Math.Probability.mix y hy0 hy1 (PMF.pure a) (PMF.pure b)}) :
    (Rounds.Game.diagonal a b left right).sequentialValues order =
      {GameTheory.Math.Probability.mix (x*y/(x+y))
        (Rounds.Game.Scalar.parallel_nonneg x y hx0 hy0)
        (Rounds.Game.Scalar.parallel_le_one x y hx0 hx1 hy0) (PMF.pure a) (PMF.pure b)} :=
  Rounds.Game.Scalar.sequentialValues_diagonal a b hab left right x y hx0 hx1 hy0 hy1 order hleft hright

/-- info: 'KFOL.Paper.scalar_diagonal_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.scalar_diagonal_values

/-- The complete parallel-sum laws on nonnegative values, hence on the unit
interval. Division by zero gives the required zero boundary. -/
theorem scalar_parallel_laws :
    (∀ x : ℝ, 0*x/(0+x) = 0 ∧ x*0/(x+0) = 0) ∧
    (∀ x y : ℝ, x*y/(x+y) = y*x/(y+x)) ∧
    (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      (x*y/(x+y))*z/(x*y/(x+y)+z) = x*(y*z/(y+z))/(x+y*z/(y+z))) ∧
    (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → x ≤ y → x*z/(x+z) ≤ y*z/(y+z)) ∧
    (∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      x*(min y z)/(x+min y z) = min (x*y/(x+y)) (x*z/(x+z)) ∧
      x*(max y z)/(x+max y z) = max (x*y/(x+y)) (x*z/(x+z))) :=
  ⟨fun x => ⟨Rounds.Game.Scalar.parallel_zero_left x,Rounds.Game.Scalar.parallel_zero_right x⟩,
    Rounds.Game.Scalar.parallel_comm,Rounds.Game.Scalar.parallel_assoc,
    Rounds.Game.Scalar.parallel_mono_left,fun x y z hx hy hz =>
      ⟨Rounds.Game.Scalar.parallel_min x y z hx hy hz,Rounds.Game.Scalar.parallel_max x y z hx hy hz⟩⟩

/-- info: 'KFOL.Paper.scalar_parallel_laws' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.scalar_parallel_laws

/-- The literal reciprocal games have their exact canonical SE law, including
n=0; their actual menus are all Boolean and only the named pair is active. -/
theorem reciprocal_round_values {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (hab : a ≠ b) (n : ℕ)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    (Rounds.Game.reciprocal a b n).sequentialValues order =
      {Rounds.Game.Scalar.distribution a b (1/((n:ℝ)+1)) (by positivity)
        (by apply (div_le_one (by positivity : (0:ℝ) < (n:ℝ)+1)).mpr
            nlinarith [Nat.cast_nonneg (α := ℝ) n])} ∧
    (Rounds.Game.reciprocal a b n).UsesOnly a b ∧
    (Rounds.Game.reciprocal a b n).BooleanMenus :=
  ⟨Rounds.Game.Scalar.sequentialValues_reciprocal a b hab n order,
    Rounds.Game.usesOnly_reciprocal a b n,Rounds.Game.booleanMenus_reciprocal a b n⟩

/-- info: 'KFOL.Paper.reciprocal_round_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reciprocal_round_values

/-- `se:thm:infinite`: exact possible winners in the actual threshold games.
No finite semantics whose domain is ONLY Boolean-menu games preserves the third
role's possible victory and public-choice composition. The contextual version
also restricts every context to Boolean menus. -/
theorem infinite_winner_algebra {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    (∀ n m : ℕ,
      Rounds.Game.possibleWinners ((Rounds.Game.threshold a b c n m).sequentialValues order) =
        if n < m then {a,b} else if n = m then {a,b,c} else {a,c}) ∧
    (∀ n m : ℕ, (Rounds.Game.threshold a b c n m).BooleanMenus) ∧
    (∀ (Summary : Type v) [Finite Summary]
      (encode : {game : Rounds.Game Role // game.BooleanMenus} → Summary),
      (∀ left right rival : {game : Rounds.Game Role // game.BooleanMenus},
        encode left = encode right →
        encode ⟨Rounds.Game.publicChoice a left.val rival.val,
          left.property.publicChoice rival.property⟩ =
        encode ⟨Rounds.Game.publicChoice a right.val rival.val,
          right.property.publicChoice rival.property⟩) →
      (∀ left right : {game : Rounds.Game Role // game.BooleanMenus},
        encode left = encode right →
        (c ∈ Rounds.Game.possibleWinners (left.val.sequentialValues order) ↔
          c ∈ Rounds.Game.possibleWinners (right.val.sequentialValues order))) → False) ∧
    (∀ (Summary : Type v) [Finite Summary]
      (encode : {game : Rounds.Game Role // game.BooleanMenus} → Summary),
      (∀ left right : {game : Rounds.Game Role // game.BooleanMenus},
        encode left = encode right →
        ∀ context : Rounds.Game.Context Role, context.BooleanMenus →
          (c ∈ Rounds.Game.possibleWinners ((context.fill left.val).sequentialValues order) ↔
            c ∈ Rounds.Game.possibleWinners ((context.fill right.val).sequentialValues order))) → False) :=
  ⟨fun n m => Rounds.Game.Scalar.possibleWinners_threshold a b c hab hac n m order,
    Rounds.Game.booleanMenus_threshold a b c,
    fun _ _ encode congr adequate =>
      Rounds.Game.Scalar.no_finite_boolean_winner_algebra a b c hab hac hbc order encode congr adequate,
    fun _ _ encode adequate =>
      Rounds.Game.Scalar.no_finite_boolean_contextual_summary a b c hab hac hbc order encode adequate⟩

/-- info: 'KFOL.Paper.infinite_winner_algebra' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.infinite_winner_algebra

/-- The scalar syntax has exactly the rational unit interval as its actual
canonical SE values; leaves, complement and the unary diagonal step suffice. -/
theorem scalar_rational_values {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b : Role) (hab : a ≠ b)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    (∀ term : Rounds.Game.ScalarTerm,
      (term.game a b).sequentialValues order =
        {Rounds.Game.Scalar.distribution a b (term.rate:ℝ) term.rate_nonneg_real term.rate_le_one_real}) ∧
    ({q : ℚ | ∃ term : Rounds.Game.ScalarTerm, term.UnaryGenerated ∧ term.rate = q} = Set.Icc 0 1) ∧
    (∀ (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1), ∃ term : Rounds.Game.ScalarTerm,
      term.UnaryGenerated ∧ (term.game a b).sequentialValues order =
        {Rounds.Game.Scalar.distribution a b (q:ℝ) (by exact_mod_cast h0) (by exact_mod_cast h1)}) :=
  ⟨fun term => Rounds.Game.Scalar.sequentialValues_scalarTerm term a b hab order,
    Rounds.Game.ScalarTerm.unaryGenerated_range,
    fun q h0 h1 => Rounds.Game.Scalar.exists_rational_game a b hab q h0 h1 order⟩

/-- info: 'KFOL.Paper.scalar_rational_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.scalar_rational_values

/-- `se:cor:scalar`: scalar value equality is exactly contextual equality of
possible winners; the third role alone suffices in every actual round context. -/
theorem scalar_contextual_equivalence {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (left right : Rounds.Game.ScalarTerm)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
    (left.rate = right.rate ↔ ∀ context : Rounds.Game.Context Role,
      Rounds.Game.possibleWinners ((context.fill (left.game a b)).sequentialValues order) =
        Rounds.Game.possibleWinners ((context.fill (right.game a b)).sequentialValues order)) ∧
    (left.rate = right.rate ↔ ∀ context : Rounds.Game.Context Role,
      (c ∈ Rounds.Game.possibleWinners ((context.fill (left.game a b)).sequentialValues order) ↔
        c ∈ Rounds.Game.possibleWinners ((context.fill (right.game a b)).sequentialValues order))) :=
  ⟨Rounds.Game.Scalar.scalar_full_abstraction left right a b c hab hac hbc order,
    Rounds.Game.Scalar.scalar_third_full_abstraction left right a b c hab hac hbc order⟩

/-- info: 'KFOL.Paper.scalar_contextual_equivalence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.scalar_contextual_equivalence

/-- The three hard raw binary pairs have coNP-complete validity, for native
ordinary syntax and for the complete malformed-rejecting binary languages.
This is the hard-pair part of the fixed-signature dichotomy. -/
theorem raw_pair_complexity {Role : Type} [Fintype Role]
    (a b d : Role) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPComplete Complexity.RawPairMachines.equationEncoding
      {equation : RawPair.Term ℕ × RawPair.Term ℕ | ∀ valuation : ℕ → WinnerSet Role,
        equation.1.eval (WinnerSet.choice a) (WinnerSet.union) valuation = equation.2.eval (WinnerSet.choice a) (WinnerSet.union) valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : RawPair.Term ℕ × RawPair.Term ℕ,
        FiniteTermCode.encodeEquation RawPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            equation.1.eval (WinnerSet.choice a) (WinnerSet.union) valuation = equation.2.eval (WinnerSet.choice a) (WinnerSet.union) valuation} ∧
    Cslib.Complexity.coNPComplete Complexity.RawPairMachines.equationEncoding
      {equation : RawPair.Term ℕ × RawPair.Term ℕ | ∀ valuation : ℕ → WinnerSet Role,
        equation.1.eval (WinnerSet.choice a) (WinnerSet.choice b) valuation = equation.2.eval (WinnerSet.choice a) (WinnerSet.choice b) valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : RawPair.Term ℕ × RawPair.Term ℕ,
        FiniteTermCode.encodeEquation RawPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            equation.1.eval (WinnerSet.choice a) (WinnerSet.choice b) valuation = equation.2.eval (WinnerSet.choice a) (WinnerSet.choice b) valuation} ∧
    Cslib.Complexity.coNPComplete Complexity.RawPairMachines.equationEncoding
      {equation : RawPair.Term ℕ × RawPair.Term ℕ | ∀ valuation : ℕ → WinnerSet Role,
        equation.1.eval (WinnerSet.reset) (WinnerSet.choice a) valuation = equation.2.eval (WinnerSet.reset) (WinnerSet.choice a) valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : RawPair.Term ℕ × RawPair.Term ℕ,
        FiniteTermCode.encodeEquation RawPair.Symbol equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            equation.1.eval (WinnerSet.reset) (WinnerSet.choice a) valuation = equation.2.eval (WinnerSet.reset) (WinnerSet.choice a) valuation} :=
  ⟨Complexity.RawPairCompleteness.union_coNPComplete a b d hab had hbd,
    Complexity.RawPairCompleteness.union_language_coNPComplete a b d hab had hbd,
    Complexity.RawPairCompleteness.twoOwners_coNPComplete a b d hab had hbd,
    Complexity.RawPairCompleteness.twoOwners_language_coNPComplete a b d hab had hbd,
    Complexity.RawPairCompleteness.resetChoice_coNPComplete a b d hab had hbd,
    Complexity.RawPairCompleteness.resetChoice_language_coNPComplete a b d hab had hbd⟩

/-- info: 'KFOL.Paper.raw_pair_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.raw_pair_complexity

/-- Every finite policy family outside the independent tractability criterion
has coNP-complete native and full binary-language equality. The positive
criterion's runtime is a separate clause of the family dichotomy. -/
theorem hard_policy_complexity {Role Label : Type} [Fintype Role] [Fintype Label]
    (D : Label → Set Role) (three : Fin 3 ↪ Role) (code : Role ↪ ℕ)
    (hard : ¬Policies.FamilyEasy D) :
    Cslib.Complexity.coNPComplete Complexity.PolicyReductionMachines.equationEncoding
      {equation : Policies.Term Label ℕ × Policies.Term Label ℕ |
        ∀ valuation : ℕ → WinnerSet Role, equation.1.eval D valuation = equation.2.eval D valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : Policies.Term Label ℕ × Policies.Term Label ℕ,
        FiniteTermCode.encodeEquation (Policies.Symbol Label) equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role, equation.1.eval D valuation = equation.2.eval D valuation} :=
  ⟨Complexity.PolicyCompleteness.coNPComplete D three code hard,
    Complexity.PolicyCompleteness.language_coNPComplete D three code hard⟩

/-- info: 'KFOL.Paper.hard_policy_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.hard_policy_complexity

/-- `two:prop:rounds`: for every two-player round, the exact possible SE
winners are the union of the two public serialization values. The latter
are literal finite owned-choice folds of the actual child winner sets. -/
theorem two_player_round_support (sizes : Fin 2 → ℕ)
    (next : ((i : Fin 2) → Fin (sizes i+1)) → Rounds.Game (Fin 2))
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder (Fin 2)) :
    ∃ g : ((i : Fin 2) → Fin (sizes i+1)) → WinnerSet (Fin 2),
      (∀ actions, (g actions).val =
        Rounds.Game.possibleWinners ((next actions).sequentialValues order)) ∧
      let Sa := WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
        WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
          g (Rounds.Game.TwoPlayers.matrixAction sizes row col)
      let Sb := WinnerSet.choiceFold 1 Finset.univ Finset.univ_nonempty fun col =>
        WinnerSet.choiceFold 0 Finset.univ Finset.univ_nonempty fun row =>
          g (Rounds.Game.TwoPlayers.matrixAction sizes row col)
      Rounds.Game.possibleWinners ((Rounds.Game.round sizes next).sequentialValues order) =
        (Sa.union Sb).val ∧
      Sa.union Sb = WinnerSet.choice 1 (WinnerSet.choice 0 Sa
        ((WinnerSet.singleton 0).union (WinnerSet.singleton 1))) Sb :=
  Rounds.Game.TwoPlayers.exists_round_support_folds sizes next order

/-- info: 'KFOL.Paper.two_player_round_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.two_player_round_support

/-- Two-role possible winners compose through every actual round context,
and the hidden two-bit matching-pennies round attains the ambiguous class. -/
theorem two_player_round_contexts
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder (Fin 2)) :
    (∀ (left right : Rounds.Game (Fin 2)),
      Rounds.Game.possibleWinners (left.sequentialValues order) =
        Rounds.Game.possibleWinners (right.sequentialValues order) →
      ∀ context : Rounds.Game.Context (Fin 2),
        Rounds.Game.possibleWinners ((context.fill left).sequentialValues order) =
          Rounds.Game.possibleWinners ((context.fill right).sequentialValues order)) ∧
    Rounds.Game.possibleWinners
      ((Rounds.Game.diagonal (0 : Fin 2) 1 (.leaf 0) (.leaf 0)).sequentialValues order) = {0,1} :=
  ⟨fun left right he context =>
    Rounds.Game.TwoPlayers.possibleWinners_context_congr context left right order he,
    Rounds.Game.Scalar.possibleWinners_reciprocal_succ (0 : Fin 2) 1 (by decide) 0 order⟩

/-- info: 'KFOL.Paper.two_player_round_contexts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.two_player_round_contexts

/-- The full finite policy-family dichotomy. Passing patterns are compared by
inclusion and intersection exactly as stated in the paper. Both branches
refer to the complete original binary input language and certified machines. -/
theorem policy_family_dichotomy {Role Label : Type}
    [Fintype Role] [Fintype Label] [DecidableEq Role] [DecidableEq Label]
    (D : Label → Finset Role) (three : Fin 3 ↪ Role) :
    let pattern := fun r : Role => {d : Label | r ∉ D d}
    let easy :=
      (∀ r s, pattern r ⊆ pattern s ∨ pattern s ⊆ pattern r) ∨
      ((∀ r s, ∃ t, pattern t = pattern r ∩ pattern s) ∧
        ∃ r s, r ≠ s ∧ pattern r = pattern s)
    let language : Set (List Bool) :=
      {word | ∃ equation : Policies.Term Label ℕ × Policies.Term Label ℕ,
        FiniteTermCode.encodeEquation (Policies.Symbol Label) equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role,
            equation.1.eval (fun d => (D d : Set Role)) valuation =
              equation.2.eval (fun d => (D d : Set Role)) valuation}
    (easy → language ∈ Cslib.Complexity.P Turing.MultiTapeTM.encBits) ∧
      (¬easy → Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits language) := by
  let code : Role ↪ ℕ :=
    ⟨fun r => (Fintype.equivFin Role r).val,
      fun _ _ he => (Fintype.equivFin Role).injective (Fin.ext he)⟩
  exact Complexity.PolicyTermFrontend.language_dichotomy three D code

/-- info: 'KFOL.Paper.policy_family_dichotomy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.policy_family_dichotomy

/-- The two owners can agree on every possible-victory observation while
an actual reset/H equation fails. Four ordinary independent input values
suffice, without winner constants or a primitive union in the terms. -/
theorem joint_owner_observation_failure {Role : Type u} (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ left right : Owner.Term Role (Fin 4),
      left.OwnersIn (fun r => r = a ∨ r = b) ∧
      right.OwnersIn (fun r => r = a ∨ r = b) ∧
      (∀ valuation : Fin 4 → WinnerSet Role,
        (a ∈ (left.eval valuation).val ↔ a ∈ (right.eval valuation).val) ∧
        (b ∈ (left.eval valuation).val ↔ b ∈ (right.eval valuation).val)) ∧
      ∃ valuation : Fin 4 → WinnerSet Role, left.eval valuation ≠ right.eval valuation := by
  refine ⟨(Owner.jointObservationEquation a b).1,(Owner.jointObservationEquation a b).2,
    ?_,?_,Owner.joint_observations_agree a b,Owner.jointObservationValuation a b c,
    Owner.joint_observations_separate a b c hab hac hbc⟩ <;>
    simp [Owner.jointObservationEquation]

/-- info: 'KFOL.Paper.joint_owner_observation_failure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.joint_owner_observation_failure

/-- `thm:raw-pairs`: the complete fixed raw-signature dichotomy. The language
contains exactly original selected-signature equations valid on every
winner-set valuation; malformed words are excluded in both branches. -/
theorem raw_signature_dichotomy {Role : Type} [Fintype Role]
    (three : Fin 3 ↪ Role) (selected : Finset (Raw.Operation Role)) :
    let language : Set (List Bool) :=
      {word | ∃ equation : Raw.Term selected ℕ × Raw.Term selected ℕ,
        FiniteTermCode.encodeEquation (Raw.Symbol selected) equation = word ∧
          ∀ valuation : ℕ → WinnerSet Role, equation.1.eval valuation = equation.2.eval valuation}
    (selected.card ≤ 1 → language ∈ Cslib.Complexity.P Turing.MultiTapeTM.encBits) ∧
      (1 < selected.card → Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits language) :=
  ⟨Complexity.RawResetFrontend.small_signature_language_mem_P selected three,
    Complexity.RawSubsignatureCompleteness.language_coNPComplete selected three⟩

/-- info: 'KFOL.Paper.raw_signature_dichotomy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.raw_signature_dichotomy

/-- The actual native shared reset graph has linear many gates and is valid
exactly for unsatisfiable source CNFs, including both empty-input cases.
`reset_circuit_complexity` also supplies the complete native machine/class endpoint. -/
theorem reset_circuit_reduction {Role : Type u} (three : Fin 3 ↪ Role)
    (formula : Reductions.CNF) :
    (Circuit.ResetCNF.equation formula).WellFormed ∧
    (Circuit.ResetCNF.equation formula).gates.length =
      7 * (Reductions.ResetUnion.support formula).length + 2 * formula.flatten.length + 3 ∧
    Circuit.operationCount (Circuit.ResetCNF.equation formula).gates =
      5 * (Reductions.ResetUnion.support formula).length + 2 * formula.flatten.length + 1 ∧
    (let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
     (Circuit.ResetCNF.equation formula).Holds (WinnerSet Role) ↔ ¬Reductions.Satisfiable formula) := by
  exact ⟨Circuit.ResetCNF.equation_wellFormed formula,
    Circuit.ResetCNF.equation_gate_count formula,Circuit.ResetCNF.equation_reset_gate_count formula,
    Circuit.ResetCNF.equation_holds_iff_unsatisfiable three formula⟩

/-- info: 'KFOL.Paper.reset_circuit_reduction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_circuit_reduction

/-- Every wellformed reset DAG has its entire identity theory tested by the
same actual three-element generator used for reset trees. -/
theorem reset_circuit_generator {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (equation : Circuit.Equation Reset.Symbol Var) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    equation.Holds (WinnerSet Role) ↔ equation.WellFormed ∧
      ∀ valuation : Var → WinnerSet Role,
        (∀ j, ∃ stage : Fin 3, valuation j = Reset.chainValue three stage) →
        ∃ value, equation.eval valuation = some (value,value) :=
  Circuit.Equation.reset_holds_iff_chain three equation

/-- info: 'KFOL.Paper.reset_circuit_generator' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_circuit_generator

/-- The original full-language core extractor has an actual polynomial-time
machine on every input word. On every typed source it returns exactly the
already proved checked extraction, preserving the original output format.
K and names are binary; permutations are explicit arrays. -/
theorem uniform_core_extraction_runtime :
    Turing.MultiTapeTM.ComputableInPolyTime FullTermCode.extractWord
      Turing.MultiTapeTM.encBits (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encBits) ∧
    ∀ (K : ℕ) (term : Term (Fin K) ℕ),
      FullTermCode.extractWord (FullTermCode.encodeInput ⟨K,term⟩) =
        (term.extractCore? 1).map (fun core => FullTermCode.encodeInput ⟨K,core⟩) :=
  ⟨Complexity.CoreExtraction.extractWord_polyTime,
    fun K term => FullTermCode.extractWord_encodeInput ⟨K,term⟩⟩

/-- info: 'KFOL.Paper.uniform_core_extraction_runtime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.uniform_core_extraction_runtime

/-- The tractable branches of the owner-count dichotomy use complete native
checkers on original words, including the selected-owner syntax restriction. -/
theorem owner_count_polynomial_branches {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owners : Finset Role) :
    let language (relation : WinnerSet Role → WinnerSet Role → Prop) : Set (List Bool) :=
      {word | ∃ equation : Owner.Term Role ℕ × Owner.Term Role ℕ,
        FiniteTermCode.encodeEquation (Owner.Symbol Role) equation = word ∧
        equation.1.OwnersIn (fun r => r ∈ owners) ∧ equation.2.OwnersIn (fun r => r ∈ owners) ∧
        ∀ valuation : ℕ → WinnerSet Role,
          relation (equation.1.eval valuation) (equation.2.eval valuation)}
    (owners.card ≤ 1 → language Eq ∈ Cslib.Complexity.P Turing.MultiTapeTM.encBits) ∧
    ∀ observer : Role, (owners.erase observer).card ≤ 1 →
      language (fun x y => observer ∈ x.val → observer ∈ y.val) ∈
        Cslib.Complexity.P Turing.MultiTapeTM.encBits ∧
      language (fun x y => observer ∈ x.val ↔ observer ∈ y.val) ∈
        Cslib.Complexity.P Turing.MultiTapeTM.encBits :=
  ⟨Complexity.OwnerObservationFrontend.equality_language_mem_P three owners,
    fun observer small =>
      ⟨Complexity.OwnerObservationFrontend.implication_language_mem_P three owners observer small,
        Complexity.OwnerObservationFrontend.equivalence_language_mem_P three owners observer small⟩⟩

/-- info: 'KFOL.Paper.owner_count_polynomial_branches' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_count_polynomial_branches

/-- Sharing alone makes constant-free reset equality coNP-complete. The
language consists exactly of original wellformed graphs valid on all inputs. -/
theorem reset_circuit_complexity {Role : Type u} (three : Fin 3 ↪ Role) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : Circuit.Equation Reset.Symbol ℕ,
        Circuit.Code.encode Reset.Symbol equation = word ∧ equation.WellFormed ∧
        ∀ valuation : ℕ → WinnerSet Role,
          ∃ value, equation.eval valuation = some (value,value)} :=
  Complexity.CircuitCompleteness.reset_coNPComplete three

/-- info: 'KFOL.Paper.reset_circuit_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_circuit_complexity

/-- The same full original graph language is coNP-complete already on the
actual three-element reset multiplication table. -/
theorem reset_chain_circuit_complexity :
    let _ := Reset.structureOf (fun i j : Fin 3 => if j = 0 then 0 else max i j)
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ equation : Circuit.Equation Reset.Symbol ℕ,
        Circuit.Code.encode Reset.Symbol equation = word ∧ equation.WellFormed ∧
        ∀ valuation : ℕ → Fin 3,
          ∃ value, equation.eval valuation = some (value,value)} :=
  Complexity.CircuitCompleteness.reset_chain_coNPComplete

/-- info: 'KFOL.Paper.reset_chain_circuit_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_chain_circuit_complexity

/-- A polynomial canonicalization of the actual original core, with any
polynomial comparator deciding semantic equivalence of its outputs, forces P=NP. -/
theorem core_canonicalization_collapse {K : ℕ} (three : Fin 3 ↪ Fin K)
    (canonicalize : {term : Term (Fin K) ℕ // term.IsCore} → List Bool)
    (runtime : Turing.MultiTapeTM.ComputableInPolyTime canonicalize
      (Complexity.FullHardness.originalCoreTermEncoding K) Turing.MultiTapeTM.encBits)
    (compare : List Bool × List Bool → Bool)
    (comparison : Turing.MultiTapeTM.ComputableInPolyTime compare
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBool)
    (complete : ∀ left right : {term : Term (Fin K) ℕ // term.IsCore},
      compare (canonicalize left,canonicalize right) = true ↔
        ∀ valuation : ℕ → WinnerSet (Fin K),left.val.eval valuation = right.val.eval valuation) :
    Cslib.Complexity.P Turing.MultiTapeTM.encBits = Cslib.Complexity.NP Turing.MultiTapeTM.encBits :=
  Complexity.Canonicalization.original_core_comparator (three 0) (three 1) (three 2)
    (three.injective.ne (by decide)) (three.injective.ne (by decide))
    (three.injective.ne (by decide)) canonicalize runtime compare comparison complete

/-- info: 'KFOL.Paper.core_canonicalization_collapse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.core_canonicalization_collapse

/-- `owner:cor:complexity`: complete equality and relative-observation
owner-count dichotomies for the whole selected-owner original-word language. -/
theorem owner_count_dichotomy {Role : Type} [Fintype Role] [DecidableEq Role]
    (three : Fin 3 ↪ Role) (owners : Finset Role) :
    let language (relation : WinnerSet Role → WinnerSet Role → Prop) : Set (List Bool) :=
      {word | ∃ equation : Owner.Term Role ℕ × Owner.Term Role ℕ,
        FiniteTermCode.encodeEquation (Owner.Symbol Role) equation = word ∧
        equation.1.OwnersIn (fun r => r ∈ owners) ∧ equation.2.OwnersIn (fun r => r ∈ owners) ∧
        ∀ valuation : ℕ → WinnerSet Role,
          relation (equation.1.eval valuation) (equation.2.eval valuation)}
    (owners.card ≤ 1 → language Eq ∈ Cslib.Complexity.P Turing.MultiTapeTM.encBits) ∧
    (1 < owners.card → Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits (language Eq)) ∧
    ∀ observer : Role,
      ((owners.erase observer).card ≤ 1 →
        language (fun x y => observer ∈ x.val → observer ∈ y.val) ∈
          Cslib.Complexity.P Turing.MultiTapeTM.encBits ∧
        language (fun x y => observer ∈ x.val ↔ observer ∈ y.val) ∈
          Cslib.Complexity.P Turing.MultiTapeTM.encBits) ∧
      (1 < (owners.erase observer).card →
        Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
          (language (fun x y => observer ∈ x.val → observer ∈ y.val)) ∧
        Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
          (language (fun x y => observer ∈ x.val ↔ observer ∈ y.val))) :=
  ⟨Complexity.OwnerObservationFrontend.equality_language_mem_P three owners,
    Complexity.OwnerCountCompleteness.equality_language_coNPComplete three owners,
    fun observer =>
      ⟨fun small =>
        ⟨Complexity.OwnerObservationFrontend.implication_language_mem_P three owners observer small,
          Complexity.OwnerObservationFrontend.equivalence_language_mem_P three owners observer small⟩,
        fun large =>
          ⟨Complexity.OwnerCountCompleteness.implication_language_coNPComplete owners observer large,
            Complexity.OwnerCountCompleteness.equivalence_language_coNPComplete owners observer large⟩⟩⟩

/-- info: 'KFOL.Paper.owner_count_dichotomy' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_count_dichotomy

/-- `gen:thm:complexity`: the full symmetric, public and core equation
languages are coNP-complete when the binary role count is part of the input.
All three use the same original syntax and explicit permutation-array codec. -/
theorem uniform_equational_complexity :
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ input : FullTermCode.EquationInput,
        3 ≤ input.1 ∧ FullTermCode.encodeEquationInput input = word ∧
        ∀ valuation : ℕ → WinnerSet (Fin input.1),
          input.2.1.eval valuation = input.2.2.eval valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ input : FullTermCode.EquationInput,
        3 ≤ input.1 ∧ FullTermCode.encodeEquationInput input = word ∧
        input.2.1.IsPublic ∧ input.2.2.IsPublic ∧
        ∀ valuation : ℕ → WinnerSet (Fin input.1),
          input.2.1.eval valuation = input.2.2.eval valuation} ∧
    Cslib.Complexity.coNPComplete Turing.MultiTapeTM.encBits
      {word | ∃ input : FullTermCode.EquationInput,
        3 ≤ input.1 ∧ FullTermCode.encodeEquationInput input = word ∧
        input.2.1.IsCore ∧ input.2.2.IsCore ∧
        ∀ valuation : ℕ → WinnerSet (Fin input.1),
          input.2.1.eval valuation = input.2.2.eval valuation} :=
  ⟨Complexity.FullCompleteness.full_coNPComplete,
    Complexity.FullCompleteness.public_coNPComplete,Complexity.FullCompleteness.core_coNPComplete⟩


/-- info: 'KFOL.Paper.uniform_equational_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.uniform_equational_complexity

/-- `gen:thm:complexity`: all three signatures are also coNP-complete for
every fixed K≥3, on the fixed instance of the same original equation encoding. -/
theorem fixed_equational_complexity (K : ℕ) (hK : 3 ≤ K) :
    Cslib.Complexity.coNPComplete (Complexity.FullHardness.originalEquationEncoding K)
      {equation : Term (Fin K) ℕ × Term (Fin K) ℕ |
        ∀ valuation : ℕ → WinnerSet (Fin K),equation.1.eval valuation = equation.2.eval valuation} ∧
    Cslib.Complexity.coNPComplete (Complexity.FullHardness.originalEquationEncoding K)
      {equation : Term (Fin K) ℕ × Term (Fin K) ℕ |
        equation.1.IsPublic ∧ equation.2.IsPublic ∧
        ∀ valuation : ℕ → WinnerSet (Fin K),equation.1.eval valuation = equation.2.eval valuation} ∧
    Cslib.Complexity.coNPComplete (Complexity.FullHardness.originalEquationEncoding K)
      {equation : Term (Fin K) ℕ × Term (Fin K) ℕ |
        equation.1.IsCore ∧ equation.2.IsCore ∧
        ∀ valuation : ℕ → WinnerSet (Fin K),equation.1.eval valuation = equation.2.eval valuation} :=
  ⟨Complexity.FullCompleteness.fixed_full_coNPComplete K hK,
    Complexity.FullCompleteness.fixed_public_coNPComplete K hK,
    Complexity.FullCompleteness.fixed_core_coNPComplete K hK⟩


/-- info: 'KFOL.Paper.fixed_equational_complexity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.fixed_equational_complexity

/-- The actual descriptor-word to primitive-tree-word synthesis machine
runs in polynomial time on all inputs, including malformed words. -/
theorem reset_synthesis_runtime :
    Turing.MultiTapeTM.ComputableInPolyTime Complexity.ResetSynthesis.synthesizeCode
      Turing.MultiTapeTM.encBits (Turing.MultiTapeTM.encOption Turing.MultiTapeTM.encBits) :=
  Complexity.ResetSynthesis.synthesizeCode_polyTime


/-- info: 'KFOL.Paper.reset_synthesis_runtime' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_synthesis_runtime

/-- The machine emits a tree exactly when the independent total descriptor
recognizer accepts; rejection is not replaced by a default output. -/
theorem reset_synthesis_recognition (word : List Bool) :
    (Complexity.ResetSynthesis.synthesizeCode word).isSome =
      Algorithms.GuardDescriptor.recognize word :=
  Complexity.ResetSynthesis.synthesizeCode_isSome word


/-- info: 'KFOL.Paper.reset_synthesis_recognition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_synthesis_recognition

/-- The actual generated primitive term has the original descriptor's exact
canonical table and root, with a bound in its raw record count. -/
theorem reset_synthesis_table (d : Algorithms.GuardDescriptor) (hc : d.check = true) :
    ∃ (root : Fin d.labels.length) (term : Reset.Term (Fin d.labels.length)),
      Complexity.ResetSynthesis.synthesize d = some (term.relabel d.labels.get) ∧
      term.root = root ∧ term.table = d.guards ∧
      term.size ≤ 1 + 2 * d.labels.length * d.records.length :=
  Complexity.ResetSynthesis.synthesize_spec d hc


/-- info: 'KFOL.Paper.reset_synthesis_table' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_synthesis_table

/-- Output bytes encode the actual sparse-label primitive term, whose winner
semantics agree with the original raw guard records on every role carrier. -/
theorem reset_synthesis_output {Role : Type u}
    (d : Algorithms.GuardDescriptor) (hc : d.check = true) :
    ∃ output : Reset.Term ℕ,
      Complexity.ResetSynthesis.synthesizeCode d.encode = some (Algorithms.TermCode.encode output) ∧
      output.size ≤ 1 + 2 * d.labels.length * d.records.length ∧
      ∀ (valuation : ℕ → WinnerSet Role) (winner : Role),
        winner ∈ (output.eval valuation).val ↔
          ∃ record ∈ d.records,
            (∀ k ∈ record.2,(valuation (d.labels.get k)).Ambiguous) ∧
            winner ∈ (valuation (d.labels.get record.1)).val :=
  Complexity.ResetSynthesis.synthesizeCode_encode_spec d hc

/-- info: 'KFOL.Paper.reset_synthesis_output' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_synthesis_output


/-- Canonical reset tables are exactly the minimal semantic ambiguity sets.
The third chain role is present precisely when the distinguished input
contributes; the other inputs carry no occurrence of that marker. -/
theorem reset_table_semantic_definition {Role : Type u} {Var : Type v}
    [DecidableEq Var] (three : Fin 3 ↪ Role) (term : Reset.Term Var) :
    (∀ (valuation : Var → WinnerSet Role) (winner : Role),
      winner ∈ (term.eval valuation).val ↔
        ∃ j, ∃ A ∈ term.table j,
          (∀ k ∈ A, (valuation k).Ambiguous) ∧ winner ∈ (valuation j).val) ∧
    (∀ (j : Var) (A : Finset Var),
      A ∈ term.table j ↔
        (three 2 ∈ (term.eval (fun i => Reset.chainValue three
          (if i = j then 2 else if i ∈ A then 1 else 0))).val) ∧
        ∀ B : Finset Var, B ⊆ A →
          (three 2 ∈ (term.eval (fun i => Reset.chainValue three
            (if i = j then 2 else if i ∈ B then 1 else 0))).val) → A ⊆ B) := by
  constructor
  · intro valuation winner
    rw [term.mem_eval]
    constructor
    · rintro ⟨j,hj,hw⟩
      obtain ⟨A,hA,hstatus⟩ := (term.selected_iff_table _ j).mp hj
      exact ⟨j,A,hA,fun k hk => hstatus hk,hw⟩
    · rintro ⟨j,A,hA,hstatus,hw⟩
      exact ⟨j,(term.selected_iff_table _ j).mpr ⟨A,hA,hstatus⟩,hw⟩
  · intro j A
    have hm (B : Finset Var) :
        (three 2 ∈ (term.eval (fun i => Reset.chainValue three
          (if i = j then 2 else if i ∈ B then 1 else 0))).val) ↔ term.Selected (B : Set Var) j := by
      have hf : Reset.Term.markerValuation three (B : Set Var) j =
          (fun i => Reset.chainValue three (if i = j then 2 else if i ∈ B then 1 else 0)) := by
        funext i
        by_cases hij : i = j <;> by_cases hi : i ∈ B <;>
          simp [Reset.Term.markerValuation,hij,hi]
      have h := term.marker_eval three (B : Set Var) j
      rw [hf] at h
      exact h
    simp only [hm]
    exact term.mem_table_iff j A

/-- info: 'KFOL.Paper.reset_table_semantic_definition' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_table_semantic_definition


/-- A finite-action public quantifier uses full contingent profiles and
whole-player deviations, and its possible SPE winners equal the binary fold.
There is an actual binary public game with exactly those equilibrium winners. -/
theorem finite_action_quantifier {Role : Type u} {Index : Type v}
    [Fintype Index] [Nonempty Index] (owner : Role) (branches : Index → Strategic.Tree Role) :
    (∀ player : Role,
      (∃ plan : Strategic.FiniteChoice.Profile branches,
        Strategic.FiniteChoice.IsSubgamePerfect owner plan ∧
        Strategic.FiniteChoice.winner plan = player) ↔
      player ∈ (WinnerSet.choiceFold owner Finset.univ Finset.univ_nonempty
        (fun i => Strategic.value (branches i))).val) ∧
    (∃ binary : Strategic.Tree Role, ∀ player : Role,
      (∃ plan : Strategic.Profile binary,
        Strategic.IsSubgamePerfect plan ∧ Strategic.winner plan = player) ↔
      ∃ plan : Strategic.FiniteChoice.Profile branches,
        Strategic.FiniteChoice.IsSubgamePerfect owner plan ∧
        Strategic.FiniteChoice.winner plan = player) := by
  constructor
  · intro player
    change player ∈ Strategic.FiniteChoice.possibleWinners owner branches ↔ _
    rw [Strategic.FiniteChoice.possibleWinners_eq_fold]
  · obtain ⟨binary,he⟩ := Strategic.FiniteChoice.exists_binary_tree owner branches
    refine ⟨binary,?_⟩
    intro player
    change player ∈ Strategic.possibleWinners binary ↔
      player ∈ Strategic.FiniteChoice.possibleWinners owner branches
    rw [he]

/-- info: 'KFOL.Paper.finite_action_quantifier' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.finite_action_quantifier

open GameTheory GameTheory.Math.Probability Rounds.Game Rounds.Game.Scalar in
/-- The displayed security laws in the actual diagonal D stage fix a's win
probability against every opposing mixed law, without a Nash assumption. -/
theorem scalar_diagonal_security {Role : Type u} [DecidableEq Role] [Fintype Role] (a b : Role) (hab : a ≠ b) (x y : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hs : 0 < x+y) :
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
  Rounds.Game.Scalar.diagonal_security a b hab x y hx0 hx1 hy0 hy1 hs

/-- info: 'KFOL.Paper.scalar_diagonal_security' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.scalar_diagonal_security

/-- Shared reset circuits can have exponentially many actual canonical
minimal guards despite a linear number of original gates and edges. -/
theorem reset_circuit_exponential_tables (n : ℕ) :
    ∃ (equation : Circuit.Equation Reset.Symbol (Bool ⊕ (ℕ × Bool)))
      (term : Reset.Term (Bool ⊕ (ℕ × Bool))),
      equation.WellFormed ∧ equation.gates.length = 6*n+3 ∧
      Circuit.operationCount equation.gates = 4*n+1 ∧
      Circuit.edgeCount equation.gates = 8*n+2 ∧
      equation.unfold = some (term,term) ∧ 2^n ≤ (term.table (.inl true)).card := by
  obtain ⟨hwf,hsize,hops,hunfold,htable⟩ := Circuit.LargeTables.linear_graph_exponential_table n
  exact ⟨Circuit.LargeTables.graph n,Circuit.LargeTables.tree n,hwf,hsize,hops,
    Circuit.LargeTables.graph_edge_count n,hunfold,htable⟩

/-- info: 'KFOL.Paper.reset_circuit_exponential_tables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_circuit_exponential_tables

/-- `reset:prop:large-circuit-table`: exact guard counts and the minimum
marker-occurrence budget hold for every semantically equivalent reset tree. -/
theorem reset_circuit_tree_succinctness (n : ℕ) :
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
          2^n+1 ≤ other.leafCount ∧ 2^(n+1)+1 ≤ other.size := by
  obtain ⟨hwf,hsize,hops,hunfold,_⟩ := Circuit.LargeTables.linear_graph_exponential_table n
  exact ⟨Circuit.LargeTables.graph n,Circuit.LargeTables.tree n,hwf,hsize,
    Circuit.LargeTables.graph_input_gate_count n,hops,
    Circuit.LargeTables.graph_edge_count n,hunfold,Circuit.LargeTables.card_table_marker n,
    fun _ hA => Circuit.LargeTables.card_mem_table_marker n hA,
    Circuit.LargeTables.occurrences_marker_tree n,
    fun _ three other equal => ⟨Circuit.LargeTables.marker_occurrences_le_of_eval_eq three n other equal,
      Circuit.LargeTables.leafCount_lower_of_eval_eq three n other equal,
      Circuit.LargeTables.size_lower_of_eval_eq three n other equal⟩⟩

/-- info: 'KFOL.Paper.reset_circuit_tree_succinctness' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.reset_circuit_tree_succinctness

/-- `se:prop:threshold-states`: N actual Boolean probes already require
N+1 summary states, without a compositionality hypothesis. -/
theorem boolean_threshold_state_lower_bound {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (N : ℕ) {Summary : Type v} [Fintype Summary] (code : Fin (N+1) → Summary)
    (adequate : ∀ n k, code n = code k → ∀ m : Fin N,
      (c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.threshold a b c n.val (m.val+1)).sequentialValues order) ↔
       c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.threshold a b c k.val (m.val+1)).sequentialValues order))) :
    Function.Injective code ∧ N+1 ≤ Fintype.card Summary :=
  ⟨Rounds.Game.Scalar.finite_threshold_codes_injective a b c hab hac hbc order N code adequate,
    Rounds.Game.Scalar.finite_threshold_summary_card_lower a b c hab hac hbc order N code adequate⟩

/-- info: 'KFOL.Paper.boolean_threshold_state_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.boolean_threshold_state_lower_bound

/-- `se:prop:pair-observation`: arbitrary two-player components are fully
observed by Boolean contexts, or just the countable rational comparison family. -/
theorem pair_game_boolean_full_abstraction {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (left right : Rounds.Game Role) (hleft : left.UsesOnly a b) (hright : right.UsesOnly a b)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role) :
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
  ⟨inferInstance,Rounds.Game.TwoPlayers.sequentialValues_eq_iff_boolean_observation left right a b c hab hac hbc
      hleft hright order,
    Rounds.Game.TwoPlayers.sequentialValues_eq_iff_boolean_winners left right a b c hab hac hbc
      hleft hright order,
    Rounds.Game.TwoPlayers.sequentialValues_eq_iff_rational_observation left right a b c hab hac hbc
      hleft hright order⟩

/-- info: 'KFOL.Paper.pair_game_boolean_full_abstraction' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.pair_game_boolean_full_abstraction

/-- `game:prop:choice-support`: the complete SPE winner observation of an
arbitrary nonempty public action family has support at most K-1, K≥2. -/
theorem public_choice_small_support {Role : Type u} {Index : Type v}
    [Fintype Role] [Nontrivial Role] [Nonempty Index]
    (owner : Role) (branches : Index → Strategic.Tree Role) :
    ∃ (S : Finset Index) (_ : S.Nonempty) (term : Term Role S),
      S.card ≤ Fintype.card Role - 1 ∧ term.IsCore ∧
      Strategic.possibleWinners (Strategic.compile (fun i : S => branches i.val) term) =
        Strategic.FiniteChoice.possibleWinners owner branches :=
  Strategic.FiniteChoice.exists_small_binary_tree owner branches

/-- info: 'KFOL.Paper.public_choice_small_support' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_choice_small_support

/-- The K-1 support bound is attained by the nonowner terminal actions. -/
theorem public_choice_support_sharp {Role : Type u} [Fintype Role] [DecidableEq Role]
    (owner : Role) :
    Strategic.FiniteChoice.possibleWinners owner
      (fun i : {r : Role // r ≠ owner} => Strategic.Tree.leaf i.val) = {r | r ≠ owner} ∧
    ∀ (S : Finset Role) (_hS : S.Nonempty), owner ∉ S →
      Strategic.FiniteChoice.possibleWinners owner (fun i : S => Strategic.Tree.leaf i.val) =
        {r | r ≠ owner} →
      S = Finset.univ.erase owner ∧ S.card = Fintype.card Role - 1 := by
  constructor
  · rw [Strategic.FiniteChoice.possibleWinners_eq]
    simp [Strategic.value_leaf, Strategic.possibleWinners_leaf, WinnerSet.singleton_inj]
  · exact fun S hS hn he => Strategic.FiniteChoice.terminal_support_sharp owner S hS hn he

/-- info: 'KFOL.Paper.public_choice_support_sharp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.public_choice_support_sharp

/-- Rational Boolean rival observations recover the exact scalar order;
a larger scalar permits fewer victories by the third observer. -/
theorem scalar_rational_observation_order {Role : Type u} [Fintype Role] [DecidableEq Role]
    (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (left right : Rounds.Game Role)
    (order : GameTheory.Languages.Bridges.FOSGToEFG.ExplicitOrder Role)
    (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hleft : left.sequentialValues order = {Rounds.Game.Scalar.distribution a b x hx0 hx1})
    (hright : right.sequentialValues order = {Rounds.Game.Scalar.distribution a b y hy0 hy1}) :
    x ≤ y ↔ ∀ probe : Rounds.Game.ScalarTerm, probe.UnaryGenerated → probe.rate < 1 →
      (c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.publicChoice a right (probe.game a c)).sequentialValues order) →
       c ∈ Rounds.Game.possibleWinners
        ((Rounds.Game.publicChoice a left (probe.game a c)).sequentialValues order)) :=
  Rounds.Game.Scalar.singleton_scalar_le_iff_rational_tests left right a b c hab hac hbc order
    x y hx0 hx1 hy0 hy1 hleft hright

/-- info: 'KFOL.Paper.scalar_rational_observation_order' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.scalar_rational_observation_order

end KFOL.Paper
