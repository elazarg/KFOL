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
