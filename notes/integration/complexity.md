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

## Remaining work

This checkpoint completes the parser/validation stage, not the full reset
algorithm runtime. The semantic reset pipeline, normalization and identity
checker are already proved independently. Next implement certified decoded
record traversals and compose them with those specifications to obtain whole
normalization/equality or recognition machine bounds. Synthesis, substitution,
and the end-to-end reset/union hardness reduction remain separate obligations.
