# Native complexity integration

The complexity branch now uses the successor native deterministic multitape
machine model on Lean/mathlib 4.35.0. The machine predicate below quantifies over
actual machines and polynomial time/space bounds. The development imports the
successor library directly; it does not import GameTheory into algebra.

## Checked checkpoint

Strict production builds passed for:

- `KFOL.Complexity.SuffixFold`: generic typed right-to-left scan. The callback is
  certified jointly in context, suffix and state, and a proved polynomial bound
  charges the encoded intermediate states.
- `KFOL.Complexity.GuardSubset`: migrated the actual existing `subsetFn`; its
  suffix accumulator is one bit. `subsetFn_polyTime` replaces the old Cobham/FPn
  certificate with the same total word semantics.
- `KFOL.Complexity.Framing`: the actual existing prefix parser `Words.unpair?`,
  including malformed inputs and both returned fields, plus validity/payload
  projections and exact paper framing/pairing emission.
- `KFOL.Complexity.BlockScan`: the complete existing `Words.undelimitBlocks`.
  The input-length-clocked loop preserves framed-prefix length plus remaining
  suffix length. Its encoded state is at most `2*N+2`; it is proved equal to the
  original complete parser, including failure on incomplete/malformed frames.
- `KFOL.Complexity.Dictionary`: canonical binary labels, their binary-valued
  decoder, complete sparse dictionary decoding and uniqueness. Numeric label
  values are never converted to unary clocks.
- `KFOL.Complexity.DescriptorValidation`: complete actual descriptor decoding,
  including canonical label/index codes, distinct dictionary names, output
  ranges, exact prerequisite widths and complete stream consumption.

The helpers are implementation constructions in these proof modules. The sole
new public encoding wrapper is `DescriptorValidation.descriptorEncoding`, whose
value is exactly the already audited `GuardDescriptor.encode`; injectivity is
the existing exact codec theorem. No new descriptor meaning is introduced.

## Complete paper-facing proposition ingredients

With `open Turing.MultiTapeTM`, the complete unconditional statements are:

```lean
ComputableInPolyTime
  KFOL.Algorithms.GuardWords.subsetFn (encPi encBits) encBits

ComputableInPolyTime KFOL.Words.unpair? encBits
  (encOption (encPair encBits encBits))

ComputableInPolyTime KFOL.Words.undelimitBlocks encBits
  (encOption (encList encBits))

ComputableInPolyTime KFOL.Words.BinaryNatCode.value encBits encNat
ComputableInPolyTime KFOL.Words.BinaryNatCode.encode encNat encBits
ComputableInPolyTime KFOL.Words.BinaryNatCode.decode? encBits (encOption encNat)

ComputableInPolyTime KFOL.Algorithms.LabelDictionary.decode encBits
  (encOption (encList encNat))

ComputableInPolyTime (fun labels : List Nat => decide labels.Nodup)
  (encList encNat) encBool

ComputableInPolyTime
  (fun word => (KFOL.Algorithms.GuardDescriptor.decode word).isSome)
  encBits encBool

ComputableInPolyTime KFOL.Algorithms.GuardDescriptor.decode encBits
  (encOption KFOL.Complexity.DescriptorValidation.descriptorEncoding)
```

The corresponding theorem anchors are `subsetFn_polyTime`, `unpair_polyTime`,
`undelimitBlocks_polyTime`, `value_polyTime`, `encode_polyTime`, `decode_polyTime`
(in Dictionary), `dictionary_decode_polyTime`, `dictionary_nodup_polyTime`,
`decode_isSome_polyTime` and `decode_polyTime` (in DescriptorValidation).

The final decoder certificate uses exact codec soundness: validation followed
by copying the original word writes precisely the existing serialization of the
decoded dependent value. This certifies the actual decoder and supplies no
caller certificate or theorem hypothesis.

## Encoding boundary and regression

The paper codec and native machine product embedding are deliberately distinct:

```lean
Turing.MultiTapeTM.encPair encBits encBits ([], []) = [false]
KFOL.Words.pair [] [] = [false, true]
```

Their lengths are `2*left.length+1+right.length` and
`2*left.length+2+right.length`, respectively. Native machines above use `encBits`
for the original paper words and the explicitly displayed native embeddings for
typed intermediates. `tests/ComplexityCodecs.lean` checks this distinction, the
binary size of sparse names, valid zero versus malformed binary zero, and exact
original-word output for the typed descriptor decoder. All finite checks use
kernel `decide`.

## Complete descriptor normalization

`KFOL.Complexity.OptionTraversal.mapMWithInput_polyTime` certifies complete
list traversal of any uniformly certified partial callback, including rejection
at any element. `RawRecords.view_polyTime` reads the actual existing typed
descriptor into native `(binary label list, list of (binary output, bitset))`
data. `RawRecords.encodeData_polyTime` emits its exact original serialization.
The projection and serializer satisfy `encodeData_view` without normalization.

The complete unconditional normalization statements are:

```lean
ComputableInPolyTime KFOL.Algorithms.GuardDescriptor.normalize
  KFOL.Complexity.DescriptorValidation.descriptorEncoding
  KFOL.Complexity.DescriptorValidation.descriptorEncoding

ComputableInPolyTime KFOL.Algorithms.GuardDescriptor.normalizeWord
  encBits (encOption encBits)
```

These are `KFOL.Complexity.NormalizeMachine.normalize_polyTime` and
`normalizeWord_polyTime`. The implementation scans the actual listed records,
compares binary output indices and bitset inclusion, filters dominated guards,
and emits the result. Its exact specification is the pre-existing pure
`GuardDescriptor.normalize`: minimal repeated records retain their multiplicity
and original order. The external machine validates complete original bits,
rejects malformed words, and returns exactly the complete encoded normalized
descriptor on success. There is no decoded natural-value loop clock.

## Complete semantic realizability recognition

`ReachMachine.constructible_polyTime` certifies greedy closure of the actual
listed prerequisites. `ReachMachine.constructible_view` proves its Boolean
answer equivalent to the independently defined `GuardTable.Constructible` for
every descriptor and target. It assumes no antichain or well-formedness
certificate. Every round scans the target's explicit width and the actual
records; the clock is the target width. Output indices stay binary. Self-bit
lookup uses a unary width to cap the binary output index before lookup.

The complete unconditional recognizer statements are:

```lean
ComputableInPolyTime KFOL.Algorithms.GuardDescriptor.check
  KFOL.Complexity.DescriptorValidation.descriptorEncoding encBool

ComputableInPolyTime KFOL.Algorithms.GuardDescriptor.recognize encBits encBool
```

These are `KFOL.Complexity.RecognitionMachine.check_polyTime` and
`recognize_polyTime`. The bridge is exact equality with the existing checker,
via its independently proved well-formedness criterion. A native candidate
scan checks unique unconditional output, root guards, antichains,
self-exclusion and constructibility, and is then composed with the complete
existing descriptor decoder. Sparse names, duplicate minimal records,
dominated guards, cyclic construction dependencies, self-dependency, multiple
unconditional outputs and malformed input are exercised in
`tests/ComplexityRecognition.lean` using kernel `decide`.

Production builds of `NormalizeMachine` and `RecognitionMachine` pass
(`2065` and `2066` jobs respectively), as does strict compilation of the new
regression file. The two normalization and two complete recognition endpoints,
plus the construction bridge and construction machine theorem, depend only on
`propext`, `Classical.choice` and `Quot.sound`.

## Original binary tree frontend

`TermMachine.termEncoding` is exactly the established injective
`TermCode.encode`, preserving its prefix code and binary names.
`TermMachine.decode_polyTime` certifies the actual complete decoder:

```lean
ComputableInPolyTime KFOL.Algorithms.TermCode.decode encBits
  (encOption KFOL.Complexity.TermMachine.termEncoding)
```

The explicit stack parser is proved extensionally equal to the existing decoder
on every bit word. It preserves the complete original word under reconstruction,
runs for `3*N` steps, and uses at most `6*N+5` encoded state bits in the concrete
AST representation. Incomplete trees, noncanonical names and trailing bits are
rejected. `tests/ComplexityTerms.lean` exercises these boundaries and independent
repeated occurrences.

`TermMachine.decode_polyTime_of_storage` generalizes the same verified parser to
any injective storage of annotated terms with certified uniform leaf/binary
constructors and a proved polynomial storage bound in the original code size.
Every intermediate annotated subtree and pending frame is charged.
`TermMachine.fold_polyTime` packages this as a reusable bottom-up evaluation
rule: certified leaf/node algebra operations and a complete output-storage bound
produce a native whole-tree fold machine. These are generic closure theorems;
the concrete frontend below discharges all their premises.

`TermSupport.labels_polyTime` certifies the actual `SupportIndex.labels` under
the original term codec and native `encList encNat`, including mathlib's exact
rightmost-occurrence `dedup` order. `GuardExtraction.collect_polyTime` computes
every raw occurrence/prerequisite in time polynomial in original bits, with a
proved quadratic complete binary storage bound. `collect_entries` recovers
exactly the independently defined `Term.guardEntries` by set interpretation of
prerequisite lists. `GuardCompression.compress_view` and `compressAll_view`
identify raw binary compression exactly with the established dependent finite
record compression; no dictionary uniqueness hypothesis is needed for these
codec bridges.

The complete unconditional original frontend theorem is
`KFOL.Complexity.GuardCompression.extract_polyTime`:

```lean
ComputableInPolyTime KFOL.Algorithms.TermCode.extract encBits (encOption encBits)
```

It includes original parsing, actual support, all raw guards, finite indexing
and exact dictionary/record framing. Sparse name values never set a dimension
or loop clock. Polynomial-time equality on shared support is certified below; its comparator
treats canonical records as sets, ignoring list order and multiplicity.

## Complete original binary reset equality

The exact unconditional endpoints are
`KFOL.Complexity.ResetEquality.check_polyTime` and `checkWord_polyTime`:

```lean
ComputableInPolyTime
  (fun p : KFOL.Reset.Term Nat × KFOL.Reset.Term Nat =>
    KFOL.Algorithms.ResetEquation.check p.1 p.2)
  (encPair KFOL.Complexity.TermMachine.termEncoding
    KFOL.Complexity.TermMachine.termEncoding) encBool

ComputableInPolyTime KFOL.Algorithms.ResetEquation.checkWord encBits encBool
```

The machine computes the established shared dictionary, compresses every actual
occurrence guard into that dictionary, reads the exact dependent descriptors,
normalizes them with the certified semantic normalizer, then checks inclusion
of the two record sets in both directions. The exact bridge uses the existing
`ResetEquation.normalized_equal_iff`; it compares canonical guard functions,
independently of record-list order and duplicate multiplicity. The complete
word endpoint includes original pair framing, both complete original-tree
decoders, and rejection of every malformed pair/tree.

The production build passes `2072` jobs. Strict `tests/ComplexityTerms.lean`
passes, covering noncanonical names, incomplete trees, trailing bits, sparse
labels, exact repeated-occurrence extraction, R2/R3 identities (including
multiple minimal records), failed associativity, and malformed equations.
All eight public parser/fold/support/extraction/equality endpoints print only
`propext`, `Classical.choice` and `Quot.sound` as axioms.

This closes the polynomial equality clause of `reset:thm:three` together with
the established canonical-table and fixed-chain semantics. The complete binary
frontend is now part of the runtime theorem rather than just an output-size
bound.

## Uniform owner scan gate

`OwnerRuntime.inputEncoding` encodes the dependent input
`Σ n, Owner.GuardTable (Fin n)` by an explicit unary dimension, binary root and
source indices, and two complete n-bit prerequisite words per record.
`view_polyTime` reads that exact injective representation. Native
`permitted_polyTime`, `update_polyTime`, `allowed_polyTime` and `next_polyTime`
are connected by `permitted_view`, `update_view`, `allowed_view` and `next_view`
to the existing independent owner program. In particular the next scan visits
exactly `List.finRange n × List.finRange n` in the established deterministic
order. All dimensions, comparisons and captured table data are charged.
This is an integration-ready scan layer, not the whole owner checker/synthesizer
runtime.

## Actual machine-level reset/union hardness

The compact mathlib-only shared syntax and actual construction live in
`Definitions/Reductions.lean`; independent prefix codec proofs are in
`Algorithms/ResetUnionCode.lean`. The support is `(0 :: actual literal names).dedup`,
so variable-free CNFs have a harmless dummy consistency pair and sparse numeric
names never generate ambient-position loops. All native tree operations,
left/right combs, literal-name arithmetic and copies are certified in
`ResetUnionMachines` and `ResetUnionReduction`.

`ResetUnionReduction.reduction_polyTime` certifies the actual complete
`Reductions.ResetUnion.equation` under native binary CNF input and exact original
one-word equation output. `encoded_reduction_polyTime` writes those same bits.
`ResetUnionSource.source_encoding_eq` is definitionally the successor library's
`encCNF`, and `source_satisfiable_iff` connects its SAT semantics to the independent
local definition. The complete total `threeSATReduction_polyTime` additionally
maps formulas with wide clauses outside the source 3SAT language to a fixed
valid equation.

`ResetUnionHardness.coNPHard` and `language_coNPHard` instantiate the actual
algebraic correctness theorem, native complete generator and imported
`ThreeSAT_npComplete`, giving respectively:

```lean
Cslib.Complexity.coNPHard ResetUnionMachines.equationEncoding
  {equation | KFOL.ResetUnion.Valid Role equation}

Cslib.Complexity.coNPHard encBits (KFOL.ResetUnion.Language Role)
```

Their sole mathematical hypothesis is `three : Fin 3 ↪ Role`. No correctness,
size, runtime or source completeness result is left as a caller hypothesis.
The word language independently rejects malformed equation codes.
`tests/ComplexityReduction.lean` passes strict compilation, including dummy
support, empty CNF versus empty clause, exact codec roundtrip, source width
rejection, sparse-name arithmetic and a `2^30` name producing fewer than 5000
output bits. The generator, total source reduction, both hardness endpoints and
imported source completeness theorem print only standard axioms.

The fixed-role coNP upper bound is complete. `FiniteAlgebraVerifier` provides
sparse first-occurrence lookup, bounded certificates, native polynomial runtime
and soundness/completeness. `ResetUnionCompleteness.coNPComplete` proves the typed
endpoint. `ResetUnionDecoding` certifies the complete original equation decoder;
`ResetUnionWordCompleteness.coNPComplete` transports membership to the complete
raw word language using a proved total malformed-input fallback. All print only
standard axioms. No uniform-K bound is asserted by this fixed finite-algebra gate.

## Finite-signature codec and complete owner checker

`Definitions/Encoding` now also contains `KFOL.FiniteTermCode`, a mathlib-only
codec for any fixed finite dependent operation alphabet `Operation σ = Σ n, σ n`.
Canonical binary operation indices are explicitly framed; recursive child codes
are concatenated. `maxArity σ` exposes the finite alphabet's arity bound.
`Algorithms/FiniteTermCode` proves operation roundtrips, the maximum-arity bound,
original-prefix parsing with a bit-length depth clock, accepted-word reconstruction,
full decoder roundtrip and encoding injectivity. Constants and ternary symbols
use the same definitions. `Equational.language` is now an `abbrev` with its identical
record body, making the signature wrapper transparent to generic term proofs.
`tests/ComplexityFiniteTerms`, the existing `Equational` and `ComplexityCodecs`
regressions all pass. No native runtime theorem for this generic tree parser is
claimed yet. `Complexity/FiniteTermMachines` does certify the original-format
variable constructor, every fixed-arity function constructor and the generic
finite-operation lookup constructor, under the exact generic term encoding.

`OwnerRunMachine.run_polyTime` certifies the complete owner saturation execution,
including every recorded `(w,z)` frame, at exactly twice the original target
membership-word width. Each step increases serialized state by at most `6*n+3`;
its captured original table and target width are charged on every iteration.
`iterate_view` and `run_view` identify all states and frames with the independent
owner program for every table and clock, without canonicality hypotheses.

`OwnerCheckMachine` includes both finishing branches, deterministic finishing
witness selection, every canonicality scan, duplicate rejection and all target
acceptance tests. Its full public endpoint is:

```lean
KFOL.Complexity.OwnerRuntime.source_check_polyTime :
  ComputableInPolyTime
    (fun input : KFOL.Complexity.OwnerRuntime.Input =>
      input.2.check (List.finRange input.1))
    KFOL.Complexity.OwnerRuntime.inputEncoding encBool
```

Here `Input = Σ n, Owner.GuardTable (Fin n)`. `inputEncoding` explicitly pairs
unary `n` with binary root/output positions and full membership words for each
many/outside prerequisite. `check_view` proves equality with the actual source
checker on every such table; no canonical-input promise or realizability
hypothesis is assumed. This certificate is uniform in the table dimension.
It is a typed table certificate; it does not assert a raw owner-table word decoder
or a uniform-role tree-signature bound.

`tests/ComplexityOwner` checks a valid singleton table, duplicate rejection,
missing-root rejection, the exact checker bridge and the native public type.
Production builds pass 2,069 jobs; the generic codec and owner runtime endpoints
print only the three standard axioms.

## Complete owner synthesis runtime

`OwnerTermMachines` specializes the generic finite signature to reset plus
owner-labelled ternary H, with native constructors and exact original-code header
sizes. `OwnerPathMachines` certifies the actual `Owner.Term.pathBody` and
`pathTerm` functions; each frame has one recursive occurrence, and its stored
variable codes plus the captured original root bound accumulator growth.

`OwnerSynthesisMachine` composes the complete independent table check, actual
saturation run with recorded frames, both finishing alternatives, complete
`mapM` over every required guard, path construction and the expanded final join.
`OwnerSynthesisBridge` proves exact `finishTerm_view`, `guardPath_view` and
`synthesize_view` equalities with the independently defined source programs.
The complete public native endpoint is:

```lean
KFOL.Complexity.OwnerRuntime.source_synthesize_polyTime
  {Role : Type} [Fintype Role] (owner : Role) :
  ComputableInPolyTime
    (fun input : KFOL.Complexity.OwnerRuntime.Input =>
      (input.2.synthesize owner (List.finRange input.1)).map
        (fun term =>
          (⟨input.1, term⟩ : KFOL.Complexity.OwnerRuntime.Output Role)))
    KFOL.Complexity.OwnerRuntime.inputEncoding
    (encOption KFOL.Complexity.OwnerRuntime.outputEncoding)
```

`Output Role = Σ n, Owner.Term Role (Fin n)`. Its injective output encoding pairs
unary `n` with the fully expanded generic original tree code after renaming
positions by `Fin.val`; no sharing or circuit compression is hidden. The input
encoding is the same explicit width/bitset table encoding as the whole checker.
Failed checks and failed construction branches return `none` exactly as in the
source definition. The runtime is uniform in the table dimension and number of
records, with the finite role alphabet fixed. No caller-supplied correctness,
realizability or complexity premise is required.

The regression covers successful actual singleton synthesis, rejected duplicate
tables, exact native/source output correspondence and the public native type.
All source synthesis runtime and bridge endpoints print only standard axioms.

## Generic original-tree folds and complete decoders

`FiniteFoldMachine` implements a generic prefix-tree stack machine for a fixed
finite dependent signature, including constants and ternary operations. Cached
ASTs connect each runtime annotation to its actual mathematical subtree.
`trace_term` proves exact evaluation, preserving surrounding frames and suffixes,
at a clock charging every node and child return; `cost + 1 ≤ 2*code.length`.
Every step preserves valid annotations and never increases the serialized
source-forest weight, including on malformed inputs.

`FiniteFoldStorage.encoded_state_bound` bounds native state by
`32*(P+1)^3*(c*(P+1)^d+1)`, where `P` is the original encoded context/word budget
and `c,d` bound mathematical annotation bytes. `FiniteFoldRuntime.fold_polyTime`
certifies the actual mathematical fold with joint native certificates for its
leaf and n-ary callbacks. Original captured context, reconstructed ASTs, complete
child lists and output annotations are all charged. This is a reusable theorem;
paper-facing applications discharge its callback and annotation premises.

`FiniteTermDecoding.decode_polyTime` certifies the complete independent original
`FiniteTermCode.decode`, for every raw bit word. A checked candidate re-encoding
proves agreement with the independent pure parser and rejects malformed/trailing
words. `decodeEquation_polyTime` certifies the complete outer paper framing and
both child trees. `equationRecode_polyTime` and `arguments_polyTime` explicitly
convert between the original paper equation format and native typed tuples.
The pure `encodeEquation/decodeEquation` definitions reside in the existing
`Definitions/Encoding`; roundtrip, accepted-word and injectivity proofs reside in
`Algorithms/FiniteTermCode`. The fixed-alphabet operation decoder uses finite
canonical-code membership; large binary indices never become loop clocks.

These signature bounds are fixed-signature bounds. Uniform varying-role or
varying-label signatures require explicit operation codec, decoder and arity
certificates; enumerating an arbitrary `Fintype.equivFin` alphabet is not a
uniform-K argument.

## Complete uniform-K one-owner original-word equality

`OwnerTermFrontend` instantiates the generic fold on `Owner.Symbol Unit`, the
fixed reset/ternary-H alphabet. Its actual mathematical annotation is
`(t.root, (t.withOwner false).guards true)`; the native encoding uses a binary
root and complete lists of guards, binary sources and many/outside name lists.
`Owner.GuardEncoding.guardAnnotationWeight_le_encode` supplies the complete byte
bound `6*(original code.length+1)^3`, retaining every repeated prerequisite and
sparse binary variable name. `annotation_polyTime` and `guards_polyTime` certify
the actual whole extraction. `dominates_polyTime`, `covers_polyTime` and
`equation_polyTime` certify all finite scans and the full independent original
syntax checker, with no supplied guard tables or preprocessing promises.

`OwnerWordFrontend.checkWord` decodes both original complete trees, applies that
actual checker, and returns false on any malformed outer or inner word. Its
complete native endpoint is `OwnerTermFrontend.checkWord_polyTime`:

```lean
ComputableInPolyTime KFOL.Complexity.OwnerTermFrontend.checkWord encBits encBool
```

Its independent complete semantic theorem is
`OwnerTermFrontend.checkWord_iff three owner observer hne word`:

```lean
checkWord word = true ↔ ∃ left right : Owner.Term Unit ℕ,
  FiniteTermCode.encodeEquation (Owner.Symbol Unit) (left,right) = word ∧
    ∀ valuation : ℕ → WinnerSet Role,
      (left.withOwner owner).eval valuation =
        (right.withOwner owner).eval valuation
```

The only hypotheses are an arbitrary role type with decidable equality, three
distinct roles, a chosen owner and a distinct observer. The algorithm, input
codec, machine and polynomial are independent of that role type and its size;
this is uniform in K. The pure outsider-list correspondence preserves
list order and repeated tests. `owner:thm:one-table` now has its whole original
binary-input runtime clause in addition to existing semantics and counts.

Production build passes 2,057 jobs. `ComplexityFiniteTerms` covers constants,
ternary constructors, exact equation roundtrip, trailing bits, malformed framing
and native decoder types. `ComplexityOwnerTerms` covers incomplete words,
original ternary-H identity/nonidentity, a `2^30` sparse variable, exact outside
tests and the public arbitrary-role word-language theorem. All strict regressions
pass; extraction, whole equality, complete raw checker, correctness, generic
decoder and generic fold endpoints print only standard axioms.

## Remaining work

Complete native machine certificates cover original reset parsing, actual
support, all guard extraction/compression, descriptor normalization, whole reset
equality, and semantic table realizability recognition. The polynomial runtime
clauses of `reset:thm:three` and `reset:thm:synthesis` are discharged. Reset/union
has full fixed-role machine-level coNP-completeness for typed equations and the complete binary language, including malformed words.

Whole owner-table checking and expanded term synthesis are now certified.
Original one-owner term extraction/equality, including ternary H and complete
malformed-word handling, are certified uniformly in K. Further pure-H, raw-pair,
full-signature, policy-family, circuit and colouring reduction/verifier machines
remain separate obligations; uniform-K upper bounds are not inferred from the
fixed finite-algebra verifier. Generic finite-signature constructors, complete
decoders and polynomial-annotation folds are ready for that reuse.
