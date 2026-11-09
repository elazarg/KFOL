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

## Remaining work

This checkpoint completes parser, validation, full binary descriptor
normalization and complete polynomial semantic realizability recognition.
Together with the existing semantic characterization and bounded realization,
it discharges the recognition runtime clause of `reset:thm:synthesis`.
It does not yet certify the whole original-tree equality algorithm. Machine
construction of synthesis witnesses, substitution, and the end-to-end
reset/union hardness reduction remain separate obligations.
