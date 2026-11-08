module

public import KFOL.Algebra

/-!
# Kernel-checked claims of the main paper

Each declaration repeats the complete mathematical claim. Definitions of the
winner carrier, operations, term syntax and evaluation are in
`KFOL/Definitions/Public.lean`. The finite-arity testing predicate is indexed
in `KFOL/Definitions/TestDomains.lean`; its full meaning is repeated below.
This slice covers `sym:thm:pairs` and `sym:thm:optimal`.
-/

@[expose] public section

namespace KFOL.Paper

universe u v

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

end KFOL.Paper
