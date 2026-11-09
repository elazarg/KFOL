## Complete pure-H complexity and reusable finite-algebra verifier

`GuardedPairMachines.reduction_polyTime` certifies the actual complete sparse CNF
construction into the signature containing ONLY two ternary H symbols. Reset is
expanded as H_a(t,s,s); the retained continuation occurs once, so original tree
generation is polynomial without a source-clause width promise. The exact pure
count is `5 + 6*support.length + 6*formula.length + 12*literalCount`.
`CNFHardness` factors the pinned machine-certified 3SAT complement transport and
injective raw-code image transport without reduction-correctness assumptions at
any final H endpoint.

`GuardedPairHardness` proves actual typed and full binary validity hardness, plus
exact third-role winner-observation equivalence hardness, under only three
pairwise distinct roles. The binary language explicitly rejects malformed words.

`FiniteValueWitness` extracts the existing finite-value numbering, unary value
code, sparse first-occurrence lookup and padded one-hot countervaluation proofs;
public names and implementations stay in `FiniteAlgebraVerifier` unchanged.
The original binary reset/union verifier imports that shared implementation and
retains its complete public endpoint. `FiniteTermVariables` supplies the actual
occurrence collector on any original finite-signature tree, native running time,
encoded byte/count bounds, and independent mathlib-realize congruence.

`FiniteSignatureVerifier.holds_mem_coNP` and `language_mem_coNP` prove a native
coNP upper bound for ANY fixed finite nonempty algebra, ANY finite dependent
signature and ANY binary relation of outputs. They use independent mathlib
`Term.realize`, not the verifier recursion as the semantic definition. The raw
verifier accepts every malformed input as a countercertificate, which proves
malformed-word rejection for the underlying validity language even in a trivial
one-element algebra. Certificates have at most `card(Value)*inputBytes` bits;
lookup uses actual source occurrences rather than numeric variable maxima.

`GuardedPairCompleteness.coNPComplete`, `.language_coNPComplete`,
`.observation_coNPComplete` and `.observation_language_coNPComplete` combine that
upper verifier with the actual original H reduction. They require only
`[Fintype Role]` and pairwise distinct a,b,d. The observation is exactly membership
of d in both outputs. No primitive reset, preprocessed input, correctness
hypothesis or supplied finite certificate is hidden.

Scope: these upper bounds hold at every FIXED finite algebra/signature. Their
finite-value and finite-alphabet constants depend on the role set. They do not
assert a uniform polynomial in binary K. The uniform one-owner reset/H checker is
separate and has no K-dependent alphabet or enumeration. Sparse pair-valued
verifiers are the next uniform-K gate; the full/core and policy pair-countermodel
results provide their mathematical completeness.

Validation: production H + existing raw reset/union endpoints build 2,157 jobs.
New ComplexityGuardedPair and existing ComplexityReduction regressions pass,
including ternary-only signature, sparse 2^30 name, exact expanded size, original
codec roundtrip and concrete Fin3 full raw validity/observation class types.
New H generator, generic raw coNP, both raw complete endpoints and the preserved
old reset/union raw completeness theorem print only the standard three axioms.
