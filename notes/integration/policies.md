# Policies integration

The compiled production candidate is `KFOL/Policies/Public.lean`. It is pure
mathlib algebra: it imports neither GameTheory nor ComplexityLib. Independent
policy/signature/guard/criterion/algorithm definitions are concentrated in
`KFOL/Definitions/Policies.lean` (547 lines, including the fixed-family reduction definitions). Every result concerns native
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
  family reduction.
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

`lake build KFOL.Policies.Public`: passed1207 jobs. The complete staged
regression file passed with warnings as errors; production regression is
`tests/Policies.lean`. It checks one-policy asymmetry/minor laws, repeated
symbols, the five-role example with every pair easy and full family not
easy, the nested-family native union identity, and the full-union collision
identity in the covering-overlap branch. Central correctness and actual
countervaluation axiom guards allow only propext, Classical.choice and
Quot.sound.

The full required family dichotomy now has its non-easy-family native CNF
reduction proved, including missing-meet macros, calibration, correctness,
sparse Nat naming and exact affine width-three tree-size bound. The machine
polynomial and coNP/class transport layers remain with
the complexity worker. Interpret the complexity conclusion as 'criterion
implies polynomial; its complement implies coNP-complete', without asserting
P≠NP. The criterion must not be stated as a literal iff with membership in P.

After family-hardness mathematics, add the literal owner:lem:two-source
Guard.Covers wrapper noted in owner.md; its arbitrary-model absorption core
and the full forty-law basis are already proved.

## Complete semantic hardness (ready for Paper integration)

`Policies.non_easy_family_nat_cnf_reduction` proves the full statement:

```lean
[Fintype Role] [Fintype Label]
(D : Label → Set Role) (three : Fin 3 ↪ Role) (code : Role ↪ ℕ)
(hne : ¬FamilyEasy D) :
∃ plan : Policies.Hardness.Plan Role Label, ∀ formula : Reductions.CNF,
  (∀ valuation : ℕ → WinnerSet Role,
    Policies.Term.eval D
      ((plan.equation formula).1.relabel (Policies.Hardness.Variable.toNat code)) valuation =
    Policies.Term.eval D
      ((plan.equation formula).2.relabel (Policies.Hardness.Variable.toNat code)) valuation) ↔
    ¬Reductions.Satisfiable formula
```

The non-easy condition can be expanded exactly as the negation of the
`FamilyEasy` disjunction displayed above. `Plan` contains only fixed native
policy macros and finite dictionaries; it is independent of the formula.
`Plan.equation` is the displayed report equation P reset R = R. E/F macro
occurrences are fully expanded into original reset/labelled selective
symbols. Formula Boolean names use 2i+2, root/marker are 0/1, calibration
names are 2code(r)+3. The naming injection and the generic relabel theorem
prove full valuation equivalence; repeated variable occurrences are not
identified beyond their actual common name.

`Hardness.Plan.equation_size_le` proves for every Plan and width-three CNF,
writing N=support.length, F=formula.length, S=preliminary.length,
C=max(clauseBound 3,4), A=calibration.length,
P=(calibration.flatMap passedLabels).length, B=calibrationBranches.length:

```
left.size + right.size ≤ 4+(4+3S)N+2(C+1)F+4A+3P+2(C+1)B.
```

All S,C,A,P,B are fixed-family constants. `PolicyExpr.size_gate` is exact:
continuationCopies * continuation.size + overhead. Arbitrary clause lengths
are semantically handled but no false polynomial macro expansion bound is
asserted for them; machine reduction will use the explicit width-three
gate, mapping wider formulas to a fixed valid equation. Nat relabeling
preserves exact tree size. Binary-code output bound/native runtime and class
transport remain with the complexity worker.

Proof modules: `PolicyExpr`, `HardPatterns`, `Hardness`, `Reductions`,
`Families`, `Sizes`, all exported by `Policies.Public`. `HardPatterns` uses
one minimal passing-pattern extension and the remaining incomparable
extensions to obtain the same two blocking macros as the report's minimal
partition. `Families` derives either a missing meet globally or a missing
meet after deleting its unique role; no outside generation theorem is used.
`calibration_eq_singleton` and `Plan.calibration_identified` derive the actual
calibration input singleton from positive/negative tests and atomicity. The
final reduction theorem assumes no incidence certificate, completeness
oracle, SAT reduction correctness theorem or published classification.

Exact LaTeX scope: closes all remaining mathematical reduction obligations
in `selective:thm:families`, and its two-policy consequences use the same
native operations. Runtime/class assertions stay partial until the machine
branch is integrated. The positive criterion's polynomial test remains a
separate actual Bool checker with correctness already proved.

`tests/PoliciesHardness.lean` checks both genuine hard incidence cases
(missing meet and injective calibrated meet), instantiates their full native
CNF reductions, and checks disjoint sparse naming. The final reduction,
calibration and output-size theorems have standard-three axiom guards.

## Uniform pair-countercertificate existence: complete pure bridge

`KFOL.Policies.PublicCompilation` connects every native policy term to the
actual existing full public algebra. `Term.toPublic three roles D` is a
proof-level expansion using only original variable leaves and owned-choice
nodes; `isCore_toPublic` proves it contains no winner constants or role
switches. The definition is centralized in Definitions/Policies (now572
lines), rather than adding another independent semantic surface.

The selected value is the finite owned-choice suppression over r∈D of
Y∪Z with guard Y. If Y is a D atom the existing atomic suppression theorem
returns that atom. Otherwise Y remains contained in the union and is none
of the listed absorbing atoms, so every suppression step keeps Y∪Z. Outer
reset uses the existing finite core reset construction. `eval_toPublic`
proves exact agreement on every original valuation, with explicit complete
role dictionary; no family classification hypothesis or label finiteness is
needed.

The exact verifier-facing corollary is:

```lean
{Role : Type u} {Label : Type w} {Var : Type v} [Finite Role]
(D : Label → Finset Role) (three : Fin 3 ↪ Role)
(s t : Policies.Term Label Var)
(failure : ∃ v : Var → WinnerSet Role,
  s.eval (fun d => (D d : Set Role)) v ≠ t.eval (fun d => (D d : Set Role)) v) :
∃ v : Var → WinnerSet Role,
  (s.eval (fun d => (D d : Set Role)) v ≠ t.eval (fun d => (D d : Set Role)) v) ∧
  ∀ i, ∃ a b, v i = (WinnerSet.singleton a).union (WinnerSet.singleton b)
```

Proof: `Policies.Term.exists_pair_countervaluation`. The companion
`exists_pair_val_countervaluation` exposes the existing full-language
Set-valued property `(v i).val = {a,b}`. Both transfer the already-proved
full-language pair theorem through the actual public compiler. Original
native syntax is retained in the conclusion. Var and Label may be infinite;
all variables, not merely a chosen support, receive pair-valued inputs.
The compiler can expand exponentially and is never run by the native
verifier. Its only purpose is the semantic existence proof; runtime remains
on the original tree and original dictionary.

Validation: Public build passed1213 jobs. Regression
`tests/PoliciesPublicCompilation.lean` passed warnings-as-errors, checks
infinite Nat label/variable types, exact sparse variable1000000000
preservation and all-variable native countercertificate API, with only
standard-three axioms for compiler semantics, core syntax and pair theorem.
This closes the pure existence obligation requested by the generic uniform
policy verifier. The complexity worker has the exact production API.
