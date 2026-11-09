# Policies integration

The compiled production candidate is `KFOL/Policies/Public.lean`. It is pure
mathlib algebra: it imports neither GameTheory nor ComplexityLib. Independent
policy/signature/guard/criterion/algorithm definitions are concentrated in
`KFOL/Definitions/Policies.lean` (268 lines). Every result concerns native
mathlib terms with exactly binary reset and the indexed ternary policy
symbols; there are no winner constants, switches, DAGs, or compressed trees.

## Completed semantic scope

- `selective:thm:guards`: full general labelled policy guard semantics; the
  same actual checker for every fixed nonempty proper policy; complete
  observational comparison, policy/carrier independence, and the explicit
  fixed-three-role atom-or-pair countervaluation. Machine runtime remains.
- `selective:eq:inner`, the symmetry and R_{a,b} identification of G, and the
  strict nondefinability paragraph after `selective:cor:G`: proved for the
  original ordered owned-choice expression. Reset nondefinability excludes
  every reset-only term of arbitrary depth, using the exact two displayed
  valuations preserving all ambiguity and possible-a input statuses.
- `selective:cor:G`: the actual native syntax checker is correct, and either
  named owner's observation is equation-complete. Machine runtime remains.
- Policy endpoint, union/intersection and marker identities are proved,
  including whole-list joint-test absorption. These support the required
  family reduction; no native hardness assembly is claimed yet.
- Tractable alternatives of `selective:thm:families`: the independent finite
  classification criterion has a correct executable checker. The actual
  native equation checker is proved correct under either stated criterion;
  repeated-pattern observers are equation-complete in the second case;
  every rejected equation has an actual atom-or-pair countervaluation.
  All finite-pattern-meet and least-valuation hypotheses are discharged in
  the final theorem. This is a connected semantic algorithm theorem.

## Main-family public statement

`Policies.Term.familyEquationB_correct` proves:

```lean
[DecidableEq Role] [DecidableEq Label] [DecidableEq Var]
(three : Fin 3 ↪ Role)
(D : Label → Finset Role) (roles : List Role) (labels : List Label)
(hroles : ∀ r, r ∈ roles) (hlabels : ∀ d, d ∈ labels)
(heasy :
  (∀ r s,
    passingPattern (fun d => (D d : Set Role)) r ⊆ passingPattern (fun d => (D d : Set Role)) s ∨
    passingPattern (fun d => (D d : Set Role)) s ⊆ passingPattern (fun d => (D d : Set Role)) r) ∨
  ((∀ r s, ∃ t,
      passingPattern (fun d => (D d : Set Role)) t =
        passingPattern (fun d => (D d : Set Role)) r ∩ passingPattern (fun d => (D d : Set Role)) s) ∧
    ∃ r s, r ≠ s ∧ passingPattern (fun d => (D d : Set Role)) r =
      passingPattern (fun d => (D d : Set Role)) s))
(left right : Policies.Term Label Var) :
  left.familyEquationB D roles labels right = true ↔
    ∀ v : Var → WinnerSet Role,
      left.eval (fun d => (D d : Set Role)) v = right.eval (fun d => (D d : Set Role)) v
```

The program's declaration uses `Term.familyEquationB D roles labels left
right`; the field notation above is equivalent. The independent hypothesis
is named `FamilyEasy`. It does not mention validity, normalization, guards,
program behavior, or realizability. Dictionary coverage makes finiteness
explicit without using maximum numeric variable labels. Repeated role names
in a dictionary cannot produce a spurious repeated pattern: the criterion
checks that its two representatives are distinct roles.

`familyEasyB_correct` proves the separate criterion checker correct. It
includes empty families, endpoint policies and repeated policy symbols.

`repeated_observer_equation_complete` gives the full second-case clause:
with global pattern intersection closure, k≠spare and equal patterns,
full equality on all winner-set valuations is equivalent to equality of
k-membership on all such valuations. It is not a finite sample statement.

`familyEquation_countervaluation` gives, from `familyEquationB = false`
under FamilyEasy, an actual valuation v with unequal native evaluations
and `∀ i, ∃ r s, v i = singleton r ∪ singleton s`.

## Strict G statement

The fully expanded strictness claim is:

```lean
(a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
  ¬∃ t : Reset.Term (Fin 3), ∀ v : Fin 3 → WinnerSet Role,
    t.eval v =
      (WinnerSet.choice a (WinnerSet.choice b (v 1) (v 2)) (v 1)).reset (v 0)
```

Proof: `Policies.twoOwnerSelective_not_reset_definable a b c hab hac hbc`,
with `WinnerSet.twoOwnerSelective` unfolded. `WinnerSet.two_choice_selective`
proves the original inner expression equals `selective {a,b} Z Y`, and
`policyBlocks_pair` gives the literal two-atom conditional formula.
`twoOwnerSelective_separates` is the displayed witness: X={b,c}, Z={a},
Y={b} omits a while Y={c} includes a.

`Term.twoOwner_observation_equation_iff` proves the either-owner clause;
`Term.twoOwner_equationB_correct` connects the actual program to the
intended R_{a,b} native interpretation. G=R_{a,b} is a separate proved
semantic identity, not the definition of the owned-choice expression.

## Proof architecture

`Basic` proves membership and root status independently of algorithms.
`Guards` compiles exactly one labelled guard per original leaf. `SinglePolicy`
erases only the repeated label of a constant policy interpretation, reuses
the proved generic Owner.Guard coverage calculus, and supplies the concrete
minimal valuation for that policy. `Strict` uses the exact reset selector
semantics for the arbitrary-depth nondefinability argument.

`Lattice` proves passing-set union/intersection and native policy lattice
identities. `Patterns` proves row/column chain equivalence, exact finite
criterion checking, finite nonempty pattern-meet representation, and least
atoms outside every proper blocking conjunction. Repeated-pattern lifting
upgrades observer-erased blocking unions to the original policy sets.

`Normalized` adds ambiguity when the passing union at the newly tested
input reaches the blocking universe. Its lost atomic case is supplied by
the second child's unguarded root source. The compiler has exact observer
semantics, canonical guard output, an unguarded root guard, and exactly one
guard record per original native leaf; it never expands a policy operation
into an exponentially larger term.

`Coverage` constructs a concrete least atom-or-pair valuation for each
normalized guard and proves full pairwise coverage completeness.
`Recognition` connects every layer. Chain families compare every observer
using policies with that observer erased. In the second case the program
uses the original policies and full role universe, so coverage is sound
at all observers; a repeated observer proves completeness. The second
program branch requires no runtime choice of an observer.

## Runtime interfaces

D is an explicit finite policy table, with role and symbol dictionaries.
`passingFinset`, `patternChainB` and `familyEasyB` scan those lists. Guard
payloads are a source variable, ambiguity list and labelled passing list.
`blockingUnion` and `Guard.blockingAt` are finite unions. Native compiler
`Term.normalGuards`, comparison `dominatesB`/`coversB`, and branch program
`Term.familyEquationB` are computable. No loop is bounded by the largest
variable label. `normalGuards_length` proves exact original-leaf accounting.
Machine runtime composition is assigned to the complexity worker.

## Validation and remaining work

`lake build KFOL.Policies.Public`: passed1119 jobs. The complete staged
regression file passed with warnings as errors; production regression is
`tests/Policies.lean`. It checks one-policy asymmetry/minor laws, repeated
symbols, the five-role example with every pair easy and full family not
easy, the nested-family native union identity, and the full-union collision
identity in the covering-overlap branch. Central correctness and actual
countervaluation axiom guards allow only propext, Classical.choice and
Quot.sound.

For the full required family dichotomy, the remaining mathematics is
construction of the non-easy-family native 3SAT reduction, including the
minimal-pattern partition, calibration, correctness and native tree-size
bound. The machine polynomial and coNP/class transport layers remain with
the complexity worker. Interpret the complexity conclusion as 'criterion
implies polynomial; its complement implies coNP-complete', without asserting
P≠NP. The criterion must not be stated as a literal iff with membership in P.

After family-hardness mathematics, add the literal owner:lem:two-source
Guard.Covers wrapper noted in owner.md; its arbitrary-model absorption core
and the full forty-law basis are already proved.
