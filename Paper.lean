module

public import KFOL.Algebra
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
valuation and does not increase syntax size. This statement does not certify
the paper's additional polynomial machine running-time clause. -/
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
equal semantics at every valuation and no larger syntax tree. The running-time
claim remains a separate encoding/machine obligation. -/
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
three distinct roles. The separate polynomial machine-time clause remains open. -/
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
The separate polynomial machine-time claim is not asserted here. -/
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
labels. Machine bit encodings and running time remain separate obligations.
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
The full paper claim also requires a uniform polynomial machine bound. -/
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
four displayed winner sets closed under both operations. Minimum generation
requires a separate exclusion of all smaller algebras. -/
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
indexed forty native identities form a complete basis on the intended
winner-set carrier. Six variables suffice and every basis needs at least four.
The data family in Definitions/Owner is independent of semantic validity. -/
theorem owner_forty_equation_basis {Role : Type u} (three : Fin 3 ↪ Role)
    (owner observer : Role) (ho : observer ≠ owner) :
    letI := Owner.oneOwnerStructure owner
    Fintype.card (Fin 40) = 40 ∧
    (Set.range Owner.FiniteBasis.basisAxiom).Finite ∧
    (∀ i : Fin 40, (Owner.FiniteBasis.basisAxiom i).variableCount ≤ 6) ∧
    (∀ e : Equational.Identity (Owner.Symbol Unit), e.Holds (WinnerSet Role) ↔
      Equational.Derives (Set.range Owner.FiniteBasis.basisAxiom) e.lhs e.rhs) ∧
    (∀ (T : Equational.Theory (Owner.Symbol Unit)) (n : ℕ),
      (∀ e : Equational.Identity (Owner.Symbol Unit),
        e.Holds (WinnerSet Role) ↔ Equational.Derives T e.lhs e.rhs) →
      (∀ e ∈ T, e.variableCount ≤ n) → 4 ≤ n) := by
  let _ := Owner.oneOwnerStructure owner
  exact ⟨Fintype.card_fin 40, Owner.FiniteBasis.theory_finite,
    (fun i => Owner.FiniteBasis.variable_bound _ ⟨i, rfl⟩),
    Owner.FiniteBasis.isBasis_winnerSet three owner observer ho,
    Owner.FiniteBasis.variableBound_ge_four_winnerSet three owner observer ho⟩

/-- info: 'KFOL.Paper.owner_forty_equation_basis' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms KFOL.Paper.owner_forty_equation_basis

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

end KFOL.Paper
