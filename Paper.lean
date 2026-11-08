module

public import KFOL.Algebra

/-!
# Kernel-checked claims of the main paper

Each declaration repeats the complete mathematical claim. Definitions of the
winner carrier, operations, term syntax and evaluation are in
`KFOL/Definitions/Public.lean`. The finite-arity testing predicate is indexed
in `KFOL/Definitions/TestDomains.lean`; its full meaning is repeated below.
The intrinsic-core definitions are in `KFOL/Definitions/Core.lean`.
This slice covers `sym:thm:pairs`, `sym:thm:optimal` and the algebraic clauses
of `gen:thm:core`; its machine running-time clause remains outstanding.
Player views and their subdirect representations, and the full semilattice
trace, are also included. View definitions are in `Definitions/Views.lean`.
Common sources and their atomic consequences use the occurrence enumeration
in `Definitions/Core.lean`.
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

end KFOL.Paper
