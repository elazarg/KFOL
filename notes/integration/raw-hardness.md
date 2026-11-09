# Native hard-pair reductions integration

## Pure two-guarded-owner reduction: complete mathematics

Production `KFOL.Reductions.GuardedPair` proves the report's
`thm:H-hardness` native reduction mathematics, including the third-role
observational clause. Definitions are consolidated in existing
`KFOL/Definitions/Reductions.lean`; the new signature is
`GuardedPair.Symbol.guarded : Bool → Symbol 3`. There is no primitive reset,
union, role constant, winner constant, or switch. `true` interprets H_a,
`false` H_b. Every reset is the original expanded native tree
`Term.reset s t = Term.guarded true t s s`.

`Reductions.GuardedPair.equation formula` is exactly the report construction:
W is the right reset comb of source Boolean inputs over root z;
clause branches nest the literal's H owner over z, y_i and the remaining
branch; R is the right reset comb of those branches over W;
the equation is c reset R = R. Inputs are z=0,c=1,y_i=i+2.
The shared sparse support includes dummy0 and every listed source variable;
no numerical maximum controls output construction.

The complete public statement is:

```lean
{Role : Type u} (a b d : Role)
(hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
(formula : Reductions.CNF) :
  (∀ v : ℕ → WinnerSet Role,
    (Reductions.GuardedPair.equation formula).1.eval a b v =
      (Reductions.GuardedPair.equation formula).2.eval a b v) ↔
    ¬Reductions.Satisfiable formula
```

Proof: `Reductions.GuardedPair.equation_valid_iff_unsatisfiable`.
`third_role_observation_valid_iff_unsatisfiable` proves the same equivalence
with the full equality replaced by d-membership equivalence on every
valuation. `satisfying_assignment_separates` exhibits the actual d marker:
true inputs are {a}, false inputs {b}, z={a,b}, c={d}; d belongs to the left
and is absent on the right. `guarded_marker` handles every marker, including
a marker equal to a guarded owner, so the UNSAT argument quantifies over
all winner-set valuations.

The exact combined original expanded tree size is:

```
left.size + right.size =
  5 + 6*support.length + 6*formula.length + 12*sum(clause.length).
```

Proof: `Reductions.GuardedPair.equation_size`. It holds for every CNF,
including empty clauses and empty conjunctions, without a width-three
hypothesis. The right comb duplicates each small literal or clause branch;
it never duplicates an accumulated left-comb continuation. The clause gates
retain one continuation occurrence. Generic fixed finite signature
codecs/native constructors are assigned to the complexity worker; fixed
alphabet runtime is not presented as a uniform-K theorem.

Validation: `lake build KFOL.Reductions.GuardedPair` passed1190 jobs;
`tests/ReductionsGuardedPair.lean` checks empty formula/empty clause,
actual native expanded sizes, sparse variable1000000000, universally valid
empty-clause equation, and the exact third-role SAT witness. Standard axiom
guards cover equality, third-role observation, and exact size.

Remaining: native word generation/validity frontend/class transport belongs
to the complexity worker. Required raw binary pairs are the next pure
mathematical slice; they are not counted as completed by this H result.

## Remaining raw binary pairs: complete mathematics

The compiled candidate modules RawFolds, RawPair, RawCorrectness,
RawTwoOwners, RawSizes and RawReset close the remaining mathematical
reduction obligations in thm:raw-pairs. They share one original binary-only
signature RawPair.Symbol.binary : Bool → Symbol 2 and mathlib terms, without
constants, switches or compressed trees. Definitions are to be consolidated
in existing Definitions/Reductions.lean; no new per-fragment definition file
is required.

RawPair.Term.eval first second t v interprets true as first, false as second.
The complete public ordinary Nat-variable reduction statements are:

- RawPair.union_equation_valid_iff_unsatisfiable a marker c (three pairwise
  inequalities) formula: validity of RawPair.equation formula interpreted by
  first=choice a, second=union iff ¬Satisfiable formula.
- RawPair.twoOwners_equation_valid_iff_unsatisfiable a b c (three pairwise
  inequalities) formula: validity of RawPair.twoOwnerEquation formula with
  first=choice a, second=choice b iff ¬Satisfiable formula.
- ResetChoice.equation_valid_iff_unsatisfiable a b d (three pairwise
  inequalities) formula: validity of ResetChoice.equation formula with
  first=reset, second=choice a iff ¬Satisfiable formula.

In each statement validity expands literally to ∀v : Nat→WinnerSet Role,
the two native term evaluations are equal. No certificate, reduction
correctness, outside theorem or finite-exhaustiveness hypothesis appears.
Support is the already-proved sparse ResetUnion.support, never a maximum
numeric label; literal names are the same injective odd/even source labels.

For choice/union and two choices, both actual core trees have combined size
4+20*support.length+2*literalCount. The empty-clause gate outputs a fixed
valid pair; the two-owner empty-conjunction gate outputs a fixed invalid
variable pair. Every complete output is bounded by the same affine formula.
Core SAT witnesses assign false rails {a}, true rails {c}, marker {b}.
For two owners the absorbing outer-rail case is proved independently;
otherwise all internal trees agree with the union interpretation, and the
outer operands are proved different from {b} before replacing that choice
by union.

For reset/choice, ResetChoice.translate changes only binary operation
labels in the previously completed reset/union source trees. It preserves
exact tree size. The complete output size is bounded by
28*support.length+2*formula.length+2*literalCount+8, for all CNFs without
width assumptions. Generic choiceFold_ambiguous_witness and an actual
UNSAT predicate-rails argument close the arbitrary-valuation implication;
no unsupported assertion that the calibration input is atomic is used.
At its SAT valuation every replaced union is individually proved equal
to the intended owned guard, connecting to the existing reset/union SAT
countervaluation. Empty source clauses are handled by a fixed valid output.

These are original expanded native trees; fixed-alphabet codecs, source
word generation and coNP/class transport remain with the complexity worker.
They do not assert a uniform-K native runtime from fixed-signature machines.

Regression candidate ReductionsRawPairs checks exact empty cases, all3
final theorem instantiations, and numeric source label1000000000 with no
large-label loop. All3 semantic reduction axiom guards allow only propext,
Classical.choice, Quot.sound; all3 native size bounds need only propext and
Quot.sound. No manuscript, Paper, inventory, audit or sibling library edits
were made by this worker.

Exact proposed Paper-facing raw statements (all variables independent):

```lean
{Role : Type u} (a marker c : Role)
(ham : a ≠ marker) (hac : a ≠ c) (hcm : c ≠ marker)
(formula : Reductions.CNF) :
  (∀ v : ℕ → WinnerSet Role,
    (Reductions.RawPair.equation formula).1.eval (WinnerSet.choice a) WinnerSet.union v =
      (Reductions.RawPair.equation formula).2.eval (WinnerSet.choice a) WinnerSet.union v) ↔
    ¬Reductions.Satisfiable formula

{Role : Type u} (a b c : Role)
(hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
(formula : Reductions.CNF) :
  (∀ v : ℕ → WinnerSet Role,
    (Reductions.RawPair.twoOwnerEquation formula).1.eval (WinnerSet.choice a) (WinnerSet.choice b) v =
      (Reductions.RawPair.twoOwnerEquation formula).2.eval (WinnerSet.choice a) (WinnerSet.choice b) v) ↔
    ¬Reductions.Satisfiable formula

{Role : Type u} (a b d : Role)
(hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
(formula : Reductions.CNF) :
  (∀ v : ℕ → WinnerSet Role,
    (Reductions.ResetChoice.equation formula).1.eval WinnerSet.reset (WinnerSet.choice a) v =
      (Reductions.ResetChoice.equation formula).2.eval WinnerSet.reset (WinnerSet.choice a) v) ↔
    ¬Reductions.Satisfiable formula
```

The pure H observational implication clause is also now exported explicitly
as `GuardedPair.third_role_observation_implication_valid_iff_unsatisfiable`:

```lean
{Role : Type u} (a b d : Role)
(hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
(formula : Reductions.CNF) :
  (∀ v : ℕ → WinnerSet Role,
    d ∈ ((Reductions.GuardedPair.equation formula).1.eval a b v).val →
      d ∈ ((Reductions.GuardedPair.equation formula).2.eval a b v).val) ↔
    ¬Reductions.Satisfiable formula
```

Together with the already-exported equivalence clause and explicit marker
d witness, this closes the lower-bound mathematics in owner:cor:complexity
for an observer outside two selected owners. Native machine/class transport
and the uniform criterion statements remain separate.

Promotion validation: `lake build KFOL.Reductions.RawPairs
KFOL.Reductions.GuardedPair` passed1201 jobs. Both production regression
files ReductionsRawPairs and ReductionsGuardedPair passed warnings-as-errors.
Definitions/Reductions is373 lines after consolidation. All promoted source
is pure mathlib; no GameTheory/ComplexityLib imports occur in this branch.

## Role-count dependence: complete strict theory theorem

`KFOL.Reductions.Colouring` proves the full `thm:colouring-theories` result,
including its native finite-arity equation and every valuation quantifier.
The complete proposed Paper-facing statement is:

```lean
(n : ℕ) (hn : 3 ≤ n) :
  {e : Equational.Identity ResetUnion.Symbol |
    letI := ResetUnion.structureOf (Role := Fin (n + 1))
    e.Holds (WinnerSet (Fin (n + 1)))} ⊂
  {e : Equational.Identity ResetUnion.Symbol |
    letI := ResetUnion.structureOf (Role := Fin n)
    e.Holds (WinnerSet (Fin n))}
```

Proof: `Reductions.Colouring.theory_succ_ssubset`.
This compares the complete independent identity theories, not a selected
finite test set. `Colouring.equation n` is a genuine mathlib identity with
arity n+2: root0, marker1 and the n distinct vertex inputs i+2. `edges n`
contains precisely i<j, with exhaustive membership proof. Baseline, right,
left and the equation are exactly the report's expanded native reset/union
complete-graph construction.

`equation_holds_fin n` proves this identity on every nonempty winner-set
valuation over Fin n. Its independent finite pigeonhole lemma first chooses
the actual atom of each nonambiguous input; edge ambiguity makes these
chosen roles injective; finite injective implies surjective, contradicting
a fresh marker outside the baseline. No finite certificate or omitted
cardinality hypothesis substitutes for this argument.

`successor_separates n (hn : 2≤n)` supplies the actual next-carrier valuation:
vertex i gets {i}, root gets {0,1}, marker gets {n}; marker n occurs on the
left and is absent on the right. `not_equation_holds_fin_succ` connects it
to failure of the same finite-arity identity. This is an original tree
identity with ordinary independent inputs, without role constants.

The larger-to-smaller inclusion is proved for arbitrary role embeddings.
`embedWinnerSet` is the nonempty image map; it preserves union and reflects
singleton/ambiguous status, hence preserves reset. `eval_embedWinnerSet`
proves native term evaluation commutes with the map, and
`holds_of_role_embedding` transfers every larger-carrier identity. Applied
to Fin.castSucc and combined with the displayed graph witness, it yields
the strict inclusion. The image map, graph data and explicit valuation are
concentrated in Definitions/Reductions.lean (412 total lines), with all
proofs in the single Colouring module.

Validation: `lake build KFOL.Reductions.Colouring KFOL.Reductions.RawPairs`
passed1123 jobs; `tests/ReductionsColouring.lean` passed warnings-as-errors.
Regressions inspect the complete n=3 edge list and actual five-variable
identity, then instantiate validity on three roles, failure on four, and
strict inclusion of their full theories. All central theorem guards allow
only propext, Classical.choice and Quot.sound. This result has no remaining
machine-runtime/class obligation. No paper source was edited by this worker.

## Arbitrary finite raw subsignatures (production)

Exact scope: main `thm:raw-pairs`, whose signature is an arbitrary selection
from the owned choices, union and reset. The earlier three pair reductions
and reset/union reduction are now connected to an independently defined
native selected-operation syntax, rather than only four isolated alphabets.

Definitions are in the existing `KFOL/Definitions/Reductions.lean`:
`Raw.Operation Role` has exactly choice r, union and reset;
`Raw.Symbol selected` has one binary constructor labelled by a proof-carrying
member of the selected finite operation set. Its term evaluation directly
uses the actual winner-set operations. `Raw.Valid selected (s,t)` means
`∀ v : Nat → WinnerSet Role, s.eval v = t.eval v`.
`Raw.operationEquiv selected` identifies its entire dependent operation
alphabet with the selected subtype, supplying a finite alphabet even for
infinite Role. There is no function-valued operation parameter in validity.

All proof interfaces are in `KFOL/Reductions/RawSubsignature.lean`:

* `Raw.Term.ofRawPair operations` maps the two tags to actual selected
  operations, preserves every original node and variable occurrence, and
  has exact `eval_ofRawPair`, `size_ofRawPair`, `varFinset_ofRawPair` bridges.
  `ofResetUnion` has exact evaluation and expanded-size bridges as well.
* `Raw.Reduction.{resetUnion,choiceUnion,twoChoices,resetChoice}` are the
  actual native CNF reductions; `valid_*_iff` proves each is valid exactly
  when its original CNF is unsatisfiable. Hypotheses assert only membership
  of the displayed operations and the required distinct actual roles.
* `Raw.exists_hard_pair selected (h : 1 < selected.card)` exhausts every
  possible two-operation selection, finding reset+union, two distinct
  choices, choice+union or choice+reset. The proof is a direct exhaustive
  case split over the independent operation datatype.
* Consequently the full proposed paper-facing pure statement is:

  ```lean
  theorem raw_signature_cnf_reduction {Role : Type u}
      (three : Fin 3 ↪ Role) (selected : Finset (Raw.Operation Role))
      (hcard : 1 < selected.card) :
      ∃ reduction : Reductions.CNF →
          Raw.Term selected Nat × Raw.Term selected Nat,
        ∀ formula,
          (∀ valuation : Nat → WinnerSet Role,
            (reduction formula).1.eval valuation =
              (reduction formula).2.eval valuation) ↔
            ¬Reductions.Satisfiable formula
  ```

  Proof: `Raw.exists_cnf_reduction`.
* `small_signature_cases` exhausts the ≤1-operation case: empty, one owned
  choice, union or reset. `Term.support_eq_varFinset` identifies the explicit
  finite support with mathlib's complete variable occurrence set.
  `support_eq_iff_valid_choice` and `support_eq_iff_valid_union` prove
  equality iff these exact supports agree, ignoring repeated occurrences;
  they require only two distinct roles. Empty-signature terms are variables
  and `valid_empty_iff` proves validity iff syntactic equality. The singleton
  reset translation `toReset` is node preserving and `eval_toReset` is exact,
  so the existing native reset checker applies without changing meanings.

This closes the pure semantic coverage of ALL finite raw subsignatures.
Machine/class transport into each fixed selected alphabet, its small-case
frontends and the coNP upper bound are owned by the complexity worker;
no polynomial runtime is inferred from the existential reduction theorem.
Fixed finite alphabet constants must not be presented as uniform-K bounds.
The worker has received the compiled syntax and embedding APIs.

Validation: the production `lake build KFOL.Reductions.RawSubsignature`
passed all1124 jobs. `tests/ReductionsRawSubsignature.lean` checks infinite
role carriers with sparse owner labels, the exact small-case criteria and
the arbitrary-selected-signature reduction theorem. Nineteen central
embedding/classification/correctness theorem axiom checks all contain only
propext, Classical.choice and Quot.sound; they are guarded in the regression.
No manuscript, Paper, audit or manifest files were edited by this worker.
