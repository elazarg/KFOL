# Formalization delivery history through 01352a3

These records describe the completed implementation sequence through commit `01352a3`. The [active plan](formalization-plan.md), [status board](formalization-status.md) and current claim inventory determine remaining scope. Historical next-step prose is not the current task queue.

### First delivery milestone completed

The independently buildable **pair-countervaluation slice** is complete on Lean/mathlib v4.35.0. It uses mathlib only and did not wait for GameTheory's ComplexityLib update. The native term representation was retained after the checked comparison in `tests/SyntaxComparison.lean`; see [the syntax decision](formalization-syntax.md) and [definition index](formalization-definitions.md). The list below records the completed delivery contract.

1. Reconcile `sym:thm:pairs` and its supporting existing Lean declarations against the exact paper statement. Record which definitions and helper lemmas the slice actually needs; leave unrelated migration work alone.
2. Establish the minimal public algebraic interface: nonempty winner sets, owned choice, role permutations, full term syntax and evaluation. Keep profiles, SPE and every GameTheory import outside this interface.
3. Compare native and mathlib term representations on this slice and a small substitution/equational-congruence example. Choose using theorem readability, executable traversal and actual proof overhead; retain one implementation afterward. Do not build the full generic HSP/completeness framework to run this comparison.
4. Port the existing pair-countervaluation argument. Root `Paper.lean` explicitly states that any failed equation has a failing valuation assigning one or two winners to every input, with all hypotheses and quantifiers visible. The proof may invoke the library theorem; the statement cannot delegate to a named claim predicate.
5. Pass a clean algebra target and `Paper` build, guarded axiom checks, and a transitive import check excluding GameTheory, GameTheoryComplexity and complexity-machine imports. Supply a short definition index for this theorem's type and record the completed statement in the inventory.

The milestone is complete when that main-paper theorem is checked end to end on the chosen auditable algebraic definitions. It does not require the rest of `Paper.lean`, a new mathematical result, or a GameTheory bridge. It validates the syntax, dependency boundary and paper-facing audit format with an existing substantial proof. The same interface now also proves sharp test domains (see below). The algebraic idempotent extension is recorded below; perform the public-SPE and round integration gates when the updated GameTheory dependency set is ready.

### Sharp test domains completed

Root `KFOL.Paper.optimal_test_domain` repeats the entire `sym:thm:optimal`
claim: the characterization at every finite arity, leastness under inclusion,
and the exact `K(K+1)/2` count. Necessity uses genuine unary terms isolating each
singleton and pair, built from the original syntax through a derived union
and ground-set synthesis. The cardinality is proved by a bijection with
mathlib's symmetric square, not a finite sample. The reusable testing predicate
is indexed in `Definitions/TestDomains.lean`; the root theorem spells it out.
Only this characterization requires finite roles and three distinct roles.
The shared definitions and pair theorem keep their original generality.

### Idempotent algebra and checked extraction completed

`KFOL.Paper.idempotent_elimination` now states the exact occurrence criterion,
equivalence with expressibility in the core and semantics-preserving extraction
at all valuations, with no increase in constructor count. The core is a
predicate on the existing terms, not a new syntax/evaluator. Input occurrences
record their accumulated permutations independently of the extraction.
`KFOL.Paper.checked_core_extraction` additionally proves that the finite-role
`extractCore?` program succeeds exactly for idempotent terms, and every success
returns a core with equal semantics and bounded output size.

This completes the algebraic and functional clauses of `gen:thm:core`. That
inventory row remains partial: a constructor-count bound is not a polynomial
machine-time proof for encoded permutations. The existing complexity milestone
must supply that remaining clause. Regression cases check noncommuting
permutation order, cancellation across a choice node, actual program reduction,
and the two-role counterexample to the no-winner characterization. The
independent `check_core.py` also checks 1200 decorated/arbitrary terms.

### Player views and semilattice trace completed

`KFOL.Paper.player_views` proves the exact contextual classification for unary
polynomials with arbitrary finite parameter lists, and the K+1 count of the
actual quotient. `KFOL.Paper.public_subdirect_representation` proves the
injective homomorphism, coordinate surjectivity and both carrier/factor counts.
`KFOL.Paper.intrinsic_player_views` extends the homomorphism to all idempotent
full-language operations and proves irredundance. The concrete view states and
representatives are in `Definitions/Views.lean`; all are independent of
contextual equivalence and of the homomorphism claims they certify.

`KFOL.Paper.semilattice_trace` includes the full `gen:cor:trace` statement.
Its clone portion uses explicit finite-arity support laws: nonempty support,
exact classification of restricted operations, realization of every nonempty
support, projections and composition by union. Substitution preserves
idempotency and agrees with semantic composition. No generic clone or category
framework is needed for these laws. The theorem also proves essentiality of
all core arguments, regularity of identities and absence of near-unanimity and
Mal'cev terms in the full language. All these clauses are kernel checked.

Tests guard three abstraction boundaries: switches need not preserve player
views, subdirect representations need not fill the product, and equal supports
determine operations only on ambiguous inputs. Two-role and nullary cases are
also checked. GameTheory remains absent from this dependency closure.

### Common sources and atomic consequences completed

`KFOL.Paper.common_source` now covers all of `gen:thm:source`. It selects one
actual leaf and accumulated permutation satisfying the entire disjoint family
of constraints. With two distinct indices that same witness is an input, and
its membership in the existing input-occurrence list is included. The new
`sourceOccurrences` enumeration retains the original labels, traversal order
and duplicate leaves. A proved bridge connects it to `inputOccurrences`.
The proof needs neither finite types nor three roles and handles empty or
infinite index families. It depends on elementary algebra and the shared syntax,
not on idempotent elimination.

The immediate prose claims are also complete:
`KFOL.Paper.atomic_repeated_triples` proves preservation of the repeat-triple
relation whenever the relevant outputs are atomic, and
`KFOL.Paper.no_atomic_if_then_else` excludes a selector for any two distinct
control labels. They use common-source separation directly; the external S2
classification remains a separate required input. Boundary tests cover overlap,
permuted source values, the single-region winner case and an empty index type.
An independent check enumerates actual leaf paths in 210 finite term cases.

### Reduct domains and supplementary diagonal certificates completed

`KFOL.Paper.reduct_test_domains` proves the exact reduct criterion at every
finite arity. `KFOL.Paper.minimum_reduct_test_domain` includes the lower bound
and an attaining domain: six with three roles, K+2 thereafter. Genuine unary
public separators and the ambiguity-adder give necessity without importing the
whole unary classification. The all-pairs count and two disjoint pairs supply
the respective sharp cardinalities. This closes the remaining required
main-prose test-domain-count obligation.

The accepted follow-on checkpoint also completes the optional report result
`gen:thm:idem-domain`, as `KFOL.Paper.idempotency_certificates`. Its scope stays
optional; it is not promoted into the definition of main-paper completeness.
The full ambiguous-domain criterion, the lower bound allowing mixed domains,
and attainment by ambiguous domains are all kernel checked. The minimum is
three at K=3 and ceil(log₂(K+1)) at K≥4. The generic construction reserves
co-singleton incidence labels and extends to K proper labels; it does not rely
on unproved enumeration or on the external S2 classification.

Regression cases distinguish diagonal from tuple testing, show why the
ambiguity restriction matters in the criterion, and allow a role absent from
all tests. The independent existing checkers exhaust their K=3,4 cases and
check diagonal constructions through K=64. Definitions remain in the same
four shared definition modules, and the algebra still imports only mathlib.

### Shared equational foundation completed

`Definitions/Equational.lean` supplies independent validity and derivation,
finite identity theories, bases, actual-support variable bounds, and explicit
local structure values. Generic terms, substitution, homomorphisms,
substructures and quotient operations are mathlib's. `Equational/Native.lean`
connects full/core syntax by both round trips, evaluation, variable support and
substitution compatibility. The comparison test now uses this production
codec. No additional generic term datatype or category framework was needed.

`Equational/Logic.lean` and `Completeness.lean` prove soundness and completeness
by quotienting the term algebra by derivability. `isBasis_iff_models` converts
a semantic characterization into a syntactic basis. `Preservation.lean` proves
HSP preservation and injective reflection; the reverse Birkhoff representation
is not part of this milestone. `Locality.lean` transfers identities from
small-generated subalgebras, counting actual support rather than padded arity,
and proves the final logical reduction from bounded finite countermodels to
nonfinite basability. The paper-specific countermodels remain to be built.

The regression suite covers competing structures on `Bool`, arity-100 padding,
nullary axiom satisfaction in the quotient model, absence of core ground terms,
empty zero-generator closures, and empty products. All new declarations are in
the standard-axiom/import audit. Existing paper-claim completion counts stay
unchanged: shared infrastructure does not finish a particular basis theorem.

### Reset semantics and table bridge completed

`Reset.Term` uses mathlib's term datatype for exactly one binary operation.
Root and selection are independent structural definitions. `KFOL.Paper.reset_selection`
repeats all clauses of `reset:lem:selection`: exact mixed-input union semantics,
root ambiguity, monotonicity, selection of the root and self-independence.
`KFOL.Paper.reset_definability` proves expansion into the existing native core for
every finite role set with three distinct roles. Definitions remain together in
`Definitions/Reset.lean`; the shared public carrier and operations are reused.

Canonical minimal tables have a structural finite collection and a proved
normalization. Minimal enabling sets, antichains, the unique empty root guard
and self-exclusion are checked. The fixed three-value chain separates every
selector difference. `KFOL.Paper.reset_tables_semantics` proves table completeness,
chain completeness and the common identity theory for all role sets of size
at least three. `Reset.identity_holds_iff_table` connects this result directly
to the shared equational basis API.

`KFOL.Paper.reset_substitution` includes the explicit canonical-table formula for
actual term substitution, and the root and evaluation laws. Tests cover
alternative prerequisites, repeated occurrences, colliding inner roots,
unused positions, no nullary terms, nonassociativity and two-role selection.
The independent existing reset checker also verifies mixed-input semantics,
all small separators and 1000 substitutions.

The complete main proposition `reset:thm:three` remains partial because its
polynomial machine-time clause is still owed. The combined derived-reset
prose obligation also includes the guarded-choice example. The algorithm prose
obligation includes recognition and synthesis; the later compact-table milestone
below checks the criterion, realization size and recognition correctness, with
machine bounds still outstanding. Executable syntax synthesis is checked below.
The separate complexity milestone also owes the machine-time clause of
idempotent extraction. Strategic integration remains a separate gate; no
upstream GameTheory files have been changed.

### Six-law reset basis completed

`KFOL.Paper.reset_basis` states the full equivalence between equation validity
and derivability from R1--R6, repeating all six identities in the type. It also
proves that this family has exactly six distinct members. `Definitions/Reset.lean`
contains the syntactic family and an independent six-law algebra predicate;
`Equational.Derives` remains the shared independent inference relation.

`Reset/Basis` proves the special case directly. From the six equations it
derives the natural-order and common-root multiplication laws, repetition
deletion and suffix absorption. Every term has a common-root path normal form
in every six-law algebra. Exact selector coverage then implies arbitrary-model
equality, and generic equational completeness supplies a derivation. Paths can
have repeated variables; the proof deletes repetitions algebraically and does
not assume pairwise distinct occurrences. The published theorem of Freese et al.
is a proof reference, not an assumption in the completed Lean theorem.

The clean build and full axiom/import audit include all new private helpers.
Regression cases distinguish right and left projection models, allow empty
carriers for theory satisfaction, check actual variable counts and a nontrivial
nested consequence, and prove associativity is not derivable. The main basis
row is complete; the runtime clause of canonical tables stays partial.

### Antimatroid representation completed

`KFOL.Paper.reset_antimatroids` states a bijection on actual semantic term
functions and finite antimatroids with exactly one feasible singleton. Its
natural image formula includes actual variable support, the root, all feasible
sets and the readiness/selector correspondence. `reset_family_product` states
the exact family operation, allowing overlapping supports and repeated labels.
The independently axiomatized family and semantic term-function subtype are in
`Definitions/Reset.lean`, keeping the definition surface in six files.

The proof constructs the family of each term, derives readiness and family
recovery, and proves that every independently specified family has a representing
term. Accessible orders are reversed into paths and joined with a common root.
Equality of families is exactly selector equality; the chain separator then
identifies actual semantic functions and proves both inverse laws. No external
antimatroid representation theorem or finite certificate is a hypothesis.

The existence proof can enumerate all feasible sets. It closes the complete
main antimatroid theorem while leaving compact table recognition/synthesis and
polynomial bounds in their own obligations. Tests cover independent axioms,
overlapping grounds, two different path families, padded inputs, and empty
ambient types. Clean Lean checks and the full audit cover every new helper.

### Compact table realizability and recognition checked

`KFOL.Paper.reset_table_realizability` repeats the antichain, unique empty-root,
self-exclusion and constructibility conditions, and proves equivalence with
actual canonical tables. Its realization has at most `1 + 2nM` primitive syntax
occurrences, including repeated leaves and joining nodes. The independent
candidate data and inductive constructibility predicate remain in the existing
reset definition file. No caller-supplied realization certificate is assumed.

Necessity uses minimality to prove that every canonical prerequisite is feasible
in the represented antimatroid. Sufficiency builds the family of constructible
sets and constructs one path per listed prerequisite. Each path's selectors
are permitted by the candidate, and
joining paths recovers every required selector. Minimality then identifies the
actual canonical table.

`reset_table_recognition` connects a computable finite-scan Boolean checker to
the existence of an actual realizing term. Greedy closure succeeds after at
most as many rounds as target positions exactly when the target is constructible.
`reset_table_local_completeness` proves the report's alternative local condition
equivalent, using self-exclusion and cardinal induction. Regressions include
alternative prerequisites, unused inputs, cycles satisfying the root and
self-exclusion constraints, invalid antichains, and the empty target.

### Executable compact synthesis checked

`KFOL.Paper.reset_table_synthesis` connects the executable option-valued
synthesizer to actual term realizability. Every successful output has the
requested root and canonical tables, with the same `1 + 2nM` primitive-tree
size bound. The independent candidate data and constructibility definition
are unchanged.

The algorithm uses mathlib's colexicographic order to list supplied guards and
chooses the least fresh enabled position in each target. The finite input order
is required only by the executable interface. The greedy-order proof establishes
feasibility, absence of repeats and support coverage; existing path selection
lemmas then prove soundness of every generated path. Joining exactly M such
paths realizes the whole table. No feasible-set or powerset enumeration is used.

The order-free mathematical existence theorem is now derived from this same
checked algorithm, so the earlier separate choice construction is removed.
Primitive paths and joins have moved into the existing reset definition file,
keeping the auditable definition surface in six files. Regressions compute
actual output guards, unused inputs, primitive counts and rejection, using
kernel proofs and proved rewrites for finite sorting.

The whole `reset:thm:synthesis` row remains partial because polynomial machine
running time has not been certified. The term-to-table size bound is checked
below; machine adapters remain the next algorithm obligation. Minimal clone,
guarded-choice, forty-law completeness and strategic milestones retain their
own obligations.

### Guard extraction and table size checked

`KFOL.Paper.reset_guard_extraction` specifies an executable structural traversal
that returns the root and one raw guard entry per variable occurrence. The
collector carries child roots instead of recomputing them from child syntax.
Its root agrees with the independent structural root, and normalizing its
entries gives exactly the independent canonical tables.

`reset_table_size` bounds both raw and canonical entry counts by the number L
of leaf occurrences. Each individual output has at most its syntactic
occurrence count in distinct guards. Raw entry lists, including duplicates,
have descriptions of at most `1 + L²` label occurrences. Canonical tables have
the sharper bound `1 + nL`, where n is the actual support cardinality, and
`n ≤ L`. The primitive-tree measure satisfies `size + 1 = 2L`.

All prerequisites and outputs lie in the actual support; unused inputs have
empty tables. The proof works over arbitrary variable types with decidable
equality, including infinite types. It uses syntax induction and mathlib finite
cardinality and sum APIs, independently of the antimatroid representation.
The same six definition files contain the occurrence counts and collector.
Regressions distinguish repeated leaves, duplicate raw entries and dominated
guards, and compute a padded example over ℕ without a finite ambient type.

### Machine foundation and prerequisite primitive checked

An isolated downstream gate builds the pinned ComplexityLib Cobham/FPn API on
Lean/mathlib 4.35.0 without source patches and checks its standard axiom list.
The same immutable ComplexityLib and Cslib revisions used by GameTheory's
complexity extension are now direct KFOL dependencies; the existing mathlib
pin remains unchanged. There is no GameTheory or GameTheoryComplexity import.

`KFOL.Paper.reset_guard_subset_machine` states polynomial time for the actual
word-level prerequisite-subset test in the imported Turing-machine model.
It includes the exact codec, all-width finite-set correspondence, rejection of
unequal widths and the connection to the independent guard-enabling predicate.
The program scans positions by input word length with a one-bit recursive
state; Cobham's bounded-recursion theorem supplies the machine certificate.
The pure word definitions and correctness proofs remain mathlib-only.

The audit now has separate compiled environments: `KFOL.Audit.Algebra` rejects
all transitive game/machine imports from the algebra and word semantics;
`KFOL.Audit` checks every authored declaration and private helper against the
standard allowed axioms. Exact import-all source coverage is still enforced.
Regressions compute successful and failed inclusions, coordinate order, invalid
widths, zero-width inputs and a concrete guard-enabling case.

This establishes a machine component and dependency compatibility, not the
planned end-to-end reset/union reduction gate. Sparse binary labels and compact
support indices are connected to framed records below; their scan certificates
remain the next machine work.
Full extraction, normalization/equality, recognition, synthesis and substitution
machine bounds, class transport and the strategic gates remain obligations.

### Compact indices and framed binary records checked

`KFOL.Paper.reset_support_indexing` proves that the executable label dictionary
has exactly the actual support, no repeated labels and at most L entries for
L variable leaves. Dictionary lookup and the two set maps round-trip exactly;
the subset-word machine therefore applies to supported guards over arbitrary
variable-name types. Unused status labels need no dictionary positions.
Mathlib's list-indexing equivalence supplies the actual finite-support bijection.

`reset_guard_record_codec` states strict two-sided codecs for binary output
indices, fixed-width prerequisite words, framed record streams and sparse
natural-name dictionaries. The implementation reuses ComplexityLib's binary
natural code and block parser. The new framing proof establishes complete
consumption; invalid fields and trailing data cannot yield a successful parse.
Each record is framed independently, avoiding repeated duplication of its tail.

`reset_binary_guard_records` obtains the compressed records from the term's
own traversal, rather than assuming a supplied certificate. Decoded expansion
recovers every occurrence and therefore exactly the canonical tables. There
are L raw records on n support positions, `n ≤ L`; their encoding uses at most
`6L(L+1)` bits. The sparse dictionary uses at most twice the sum of the original
leaf-label binary widths plus `2L`. Membership-word width depends only on the
number of distinct labels.

Pure indexing remains mathlib-only and is included in the independent import
audit. The eight definition files separate algebra, word algorithms and the
external codec boundary. Regressions exercise separated numeric names, a root
whose index is nonzero, duplicate occurrences, exact bit lengths, noncanonical
indices, bad ranges and widths, and truncated streams.

These representation and output-size results do not certify whole-program
machine time. The original binary input-tree connection is now checked below.
Whole descriptor validation and shared support indices for identity inputs are
checked below; certified field scans remain separate work.

### Binary input parser and executable frontend checked

`KFOL.Paper.reset_binary_input_codec` repeats the complete codec, injectivity,
prefix-parser reconstruction and bit-size statements. Reset nodes use a tag
bit and concatenate their two child codes; variable nodes use a tag bit and
a framed canonical binary name. Decoding rejects malformed or incomplete trees,
noncanonical names and every nonempty suffix. Fuel is bounded by input bit
length, independently of numeric label values.

`reset_binary_extraction` connects the original bits to the actual collector
and support compressor. The executable frontend accepts exactly the valid
tree encodings and returns a single framed word containing the dictionary and
raw record stream. Decoded expansion recovers every original occurrence and
the canonical tables. For N input bits, the complete output uses at most
`6N(N+1) + 2N + 2` bits, including all sparse-name dictionary bits and framing.
The definition surface remains eight files and the pure import audit is unchanged.

Complete externally supplied dictionary/record descriptors are now validated
below, followed by shared support for two identity inputs. Certified parser
and field/table scans remain. Exact executable semantics and polynomial
output length do not finish polynomial runtime.
The full table algorithms and end-to-end reduction gate remain partial.

### Complete descriptor validation and semantic recognition checked

`KFOL.Paper.reset_binary_descriptor_codec` repeats the exact codec of complete
dictionary-and-record words. The decoder rejects duplicate dictionary names,
invalid field codes, bad ranges/widths and incomplete frames. Repeated records
and unused dictionary positions are allowed and preserved. Expansion and
recompression are inverse, and every actual extraction output decodes to its
original occurrence list. Width and record count are bounded by input bits.

`reset_encoded_table_recognition` states all independent table conditions and
proves that external recognition accepts exactly descriptors realized by an
actual reset tree. The checker infers the root from an empty prerequisite;
uniqueness follows from the semantic criterion, not dictionary order. The
entry count equals the distinct-record count. Existing compact realization
therefore gives a tree of size at most `1 + 2nM`, or `1 + 2N²` in original
descriptor bit length N. Malformed words are rejected by the executable program.

The complete parser also accepts raw extracted descriptors. The semantic
recognizer checks canonical tables and rejects raw dominated/self-dependent
guards. The binary normalization bridge and shared-support equality checker are
now proved below. Full encoded recognition runtime and the end-to-end reduction
gate remain partial.

### Binary normalization and shared-support equation checking checked

`KFOL.Paper.reset_record_normalization` repeats the executable record filter's
exact relation to mathematical minimization, enabling preservation, idempotence
and nonincreasing binary length. It retains the original dictionary and minimal
duplicate records. External normalization accepts exactly parsed descriptors.

`reset_normalized_binary_extraction` proves that the actual original-input
frontend, followed by normalization, yields recognized canonical tables and
expands to the original term's independently defined tables. The proof constructs
finite-index syntax by mathlib variable relabeling; it assumes no certificate.
The generic renaming and minimization lemmas stay in the mathlib-only algebra.

`reset_binary_equation_checker` gives a complete checker for paired original
binary tree inputs, including malformed-word rejection. Both sides share the
union of their supports, with dimension bounded by original input bits. Equality
of the normalized indexed tables is exactly equality on all mixed winner-set
valuations whenever three distinct roles exist. Independent dictionary order,
record order and duplicates do not cause a false result.

The definition surface remains eight files. Next certify parser, dictionary and
record scans in the machine model, then compose the complete extraction,
normalization/equality and recognition bounds. Executable semantics and encoded
size are now connected throughout this reset frontend, but full polynomial
machine time, synthesis/substitution time and the end-to-end reduction gate
remain partial.
