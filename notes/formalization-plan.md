# Formalization design and maintenance plan

The completion target is the entire main paper, its substantive mathematical
prose, and the report material those claims require. The entire technical report
is not a completion target. The [inventory](formalization-claims.json) records
23 main result rows, 64 required catalog rows and 21 required prose obligations,
all proved. Its source catalog contains 154 statements.

## Public audit surface

- [Paper.lean](../Paper.lean) contains 79 main-facing mathematical statements in
  about 600 lines, ordered by subject and labelled for the main results.
- [Report.lean](../Report.lean) contains 36 further mathematical report statements
  and proof ingredients.
- Every public theorem writes its proposition in mathematical vocabulary.
  Its proof is one application of a named library theorem. Neither root file
  defines semantic objects, assembles conjunctions, or contains tactic proofs.
- Each file ends with one `#audit_namespace` command. It checks every declaration
  in that namespace, including nested/generated declarations, and fails on
  transitive axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
- Codecs, bitsets, machine internals and intermediate receipts stay in the
  library. All 140 previous complete contracts remain in
  `KFOL/Results/Certificates`; the pinned relocation manifest checks that their
  complete signatures were preserved.

Main statements contain the clauses the manuscript asserts. Report support
lemmas and facts in proof sketches belong in Report or their natural proof
modules. A reference to an appendix does not pull every result in that appendix
into required scope. Consolidated theorems may serve several inventory rows.

Natural definitions may name recurring concepts such as operation equality,
contextual observation, idempotency, validity and encoded languages. They must
not merely package an entire result as `NamedClaim`. Definitions are independent
of the proof and decision procedure they specify. The [audit guide](audit-guide.md)
and [definition index](formalization-definitions.md) describe the reading order.

## Definitions and import boundaries

Three vocabulary entrypoints organize the mathematical presentation:

| Entry | Contents |
| --- | --- |
| `Definitions/PaperAlgebra` | Semantic equality, idempotency, public observations, player-view order and marker valuation |
| `Definitions/PaperGames` | Actual SE values, scalar values, contextual equivalence, candidate winner summaries and two-player public folds |
| `Definitions/Complexity` | Independently specified decision problems, original encodings, polynomial-time interface and semantic synthesis/extraction relations |

The underlying core definitions remain grouped by algebra, games, rounds,
equational logic and representation. The generated Paper and Report definition
surfaces follow theorem types and semantic/computational definitions, erasing
proof subterms and excluding theorem proof bodies. They are separate from the
transitive proof-axiom audit.

`KFOL.Algebra` and the pure representation modules import neither GameTheory nor
ComplexityLib. Semantic guard proofs remain below the native-machine boundary.
Strategic interpretation and hidden rounds reuse GameTheory separately. The
main-facing result aggregation may import those branches together; this does
not change the independent algebra target or its import audit.

Use one set of definitions for every K. Finiteness and distinct-role assumptions
belong in individual theorems. The two-role boundary uses the same carrier and
operations. Owner semilattice orders are explicit local structures, not competing
global instances or ordinary subset inclusion.

## Semantic contracts

Public SPE means complete unilateral deviations in every subgame, including
unreached branches. Its definition does not use backward induction. Repeated
variables denote independently solved game copies. The strategic-form bridge
agrees with GameTheory Nash optimality.

Arbitrary-domain binders use well-founded public trees with history-dependent
nonempty action types. The main statement assumes finite decision depth. A
pruning keeps at most K−1 original actions per retained node for K≥2, preserving
each retained subgame's actual SPE winners. A separate syntax-only `Compiles`
relation certifies recursive folds using each retained child once and only the
original owner's helper nodes. The supplied depth bound concerns the pruned
tree; binary compilation may insert decision levels. The library construction
also covers all well-founded public trees.

Sealed rounds have finite nonempty menus, private commitments, full revelation
and no retained secret across the boundary. Their value is defined by canonical
behavioral SE, with rationality and limit consistency. Equality with observed
mixed SPE, product beliefs even off path and the round recurrence are proved.
Possible winners alone have infinite contextual index already on Boolean games.
Candidate summary structures are defined independently of that obstruction.

Equational satisfaction and derivation are independent. Basis completeness
concerns arbitrary algebras and every finite arity. Nonfinite-basability uses
finite countermodels for every genuine variable bound, not bounded searches.
Literal equation families have proved cardinalities and expanded variable bounds.

Algorithms use original syntax and binary words. Charge binary variable/role
names, explicit permutation arrays, binary K, physical dictionary slots and raw
records. Fixed-K and uniform-K results remain distinct. Complexity uses actual
native multitape machines and canonical Cslib classes; checker correctness or a
semantic reduction alone is not a completed coNP-completeness claim.

## Required scope and exclusions

The policy-family dichotomy, full serial-SE/observed-SPE correspondence,
main scalar observations, congruence classifications, finite bases, native
complexity endpoints and the two-player discussion remain proved requirements.
No imported classification theorem is left as a premise of an unconditional
main result. Special cases of external results have direct proofs where needed.

The dependent syntactic calculus/private-store connection, report-only numerical
free-algebra lists, general real quantifier elimination, general round
semialgebraicity, encoded substitution runtime and H/policy circuit extensions
remain outside required scope. The reset substitution formula and required
reset-circuit clauses remain proved. Optional report statements retain accurate
written, finite-check or external-artifact status.

Category theory is not used. Products, quotients, homomorphisms and generated
varieties have explicit mathematical interfaces. The scoped mixed-open-game
refutation documented in README remains in force; the rejected unit and
associativity laws are not used for any composition theorem.

## Dependencies

The pinned production setup is Lean/mathlib 4.35.0; GameTheory
`6f1af625b77215dd9e4454e6120275dbd8b61f51` from the authorized
`port/cslib-complexity` branch; ComplexityLib
`054834a4a4e6ac3ec50ed770bacea7fc42eccc7d`; and CSLib
`254e30e6d4299c51323aaeaf5f51a4763b375d4a`.
The [library assessment](formalization-libraries.md) records exact interfaces.
Do not modify the sibling GameTheory checkout. The retired Std-only development
is historical, not a second current build.

## Verification and changes

Run `make check` and `make paper` for a complete integration. The checks validate
inventory fingerprints, literal façade statements, immutable relocated
signatures, the independent algebra import boundary, both root namespace audits,
the whole-source axiom closure, both definition indexes and strict regressions.
They also require actual failures for forbidden imports and an unsupported axiom
used outside its audited namespace.

After changing numbering, run `make paper` and commit the label snapshots it
updates. Keep the main text at most 15 pages. New mathematics goes in the report
where it belongs in the argument; replace superseded material. Evidence belongs
in the verification appendix. A statement remains unfinished if it lacks its
full mathematical clauses, assumes a needed external theorem, or gives only an
unconnected certificate. No placeholders, project axioms or `native_decide`
count as completion.

## Report-only query investigation

The query extension is package Q: three report result environments and one
audited mathematical remark, with five audited `Report` statements. It adds a
small independent navigation language
in `Definitions/Queries` and proofs in `KFOL/Query`. Exact compilation and its
quadratic constructor bound, schema-relative equivalence, a relational
representation for one owned choice, and two expressive separations are proved.
This extension changes no main-paper theorem or definition. The optional
`checks/check_xpath.py` regression uses lxml/libxml2; the standard Python suite
remains dependency-free. Future extensions should distinguish the fixed
nonempty input schema from arbitrary XPath documents and keep runtime claims
separate from syntax-size bounds.
