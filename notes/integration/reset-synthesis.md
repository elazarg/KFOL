# Native original reset-table synthesis — complete

Exact required scope: main `sections/algebra-reset.tex` closing sentence,
“polynomial recognition and synthesis and a substitution formula.” The
substitution formula is already proved independently; a native substitution
runtime is report-only and OPTIONAL. This delivery closes the actual original
reset synthesis runtime and its semantic connection, with no Owner translation,
abstract algorithm certificate, finite-certification assumption or externally
supplied correctness hypothesis.

Production files:

- `KFOL/Reset/Realizability/Records.lean`: mathlib-only literal original-record
  construction and root/table/node-bound proof, supplied by nonfinite worker.
- `KFOL/Complexity/ResetSynthesisMachine.lean`: actual native greedy scan,
  dictionary lookup, primitive syntax construction, complete all-word parser /
  checker / byte output, polynomial machines and exact source bridges.
- `tests/ComplexityResetSynthesis.lean`: strict regressions and 15 explicit
  standard-three axiom guards.

The pure source descriptor and its independent semantics remain the existing
`Algorithms.GuardDescriptor` in Definitions/Encoding: a distinct binary-label
dictionary, a literal raw list of finite output/prerequisite records, its
minimal-selector table and rooted `Reset.GuardTable.WellFormed`. Duplicates and
unused dictionary slots are retained; recognition never silently minimizes an
invalid nonminimal table. There is no new semantic definition module.

`GuardDescriptor.recordTerm d root` joins one primitive path for EACH original
record, in its original list order including duplicates. A path follows the
least enabled fresh target position using exactly `d.labels.length` greedy
steps. The clock is the physical dictionary width; after a target is complete,
extra steps do nothing (`GuardTable.greedyOrder_eq_of_card_le`).
`recordTerm_spec` proves that for any wellformed table its root is the selected
root, its independently defined selector table is exactly `d.guards`, and its
actual primitive node count is at most `1+2*n*m`, with n dictionary length and
m RAW record-list length. No normalization or hypothetical finite certificate
is substituted for the actual term.

The native implementation uses the existing RawRecords binary dictionary and
bitset masks. Internal chosen positions use unary coding solely for bounded
physical scans. Sparse original labels stay binary and binary lookup caps the
index against the physical dictionary length before any list traversal. Every
loop runs over actual records, masks, dictionary positions or output syntax;
none runs to the maximum numerical label. Internal native functions are total
on arbitrary raw records; the public front end parses and validates ALL bytes,
then checks semantic realizability before emitting syntax.

`ResetSynthesis.run_view` is exact equality with the source n-step greedy list,
not just acceptance agreement. `path_view`, `findRoot_view` and
`rawSynthesize_view` prove the actual generated reset tree is exactly
`recordTerm` relabelled to the original dictionary names. Root selection is the
first actual empty-mask record, justified by the independent unique-empty-root
condition, and has no “dictionary position 0 is root” convention.

The output uses the existing ORIGINAL primitive reset prefix-tree codec
`Algorithms.TermCode.encode`, not a descriptor or a separate term signature.
`ResetSynthesis.synthesizeCode` parses a complete descriptor word, rejects
malformed or unrealizable words with none, and otherwise returns that actual
primitive syntax word. The complete word→optional-word function has a native
machine polynomial certificate (`synthesizeCode_polyTime`). The actual source
output satisfies the exact guard semantics for EVERY role carrier and EVERY
valuation; repeated syntax occurrences are preserved.

Proposed complete Paper statements (namespace prefixes can be shortened there):

```lean
theorem reset_synthesis_runtime :
    ComputableInPolyTime Complexity.ResetSynthesis.synthesizeCode
      encBits (encOption encBits) :=
  Complexity.ResetSynthesis.synthesizeCode_polyTime

theorem reset_synthesis_recognition (word : List Bool) :
    (Complexity.ResetSynthesis.synthesizeCode word).isSome =
      Algorithms.GuardDescriptor.recognize word :=
  Complexity.ResetSynthesis.synthesizeCode_isSome word

theorem reset_synthesis_table (d : Algorithms.GuardDescriptor)
    (hc : d.check = true) :
    ∃ (root : Fin d.labels.length) (t : Reset.Term (Fin d.labels.length)),
      Complexity.ResetSynthesis.synthesize d = some (t.relabel d.labels.get) ∧
      t.root = root ∧ t.table = d.guards ∧
      t.size ≤ 1 + 2 * d.labels.length * d.records.length :=
  Complexity.ResetSynthesis.synthesize_spec d hc

theorem reset_synthesis_output {Role : Type u}
    (d : Algorithms.GuardDescriptor) (hc : d.check = true) :
    ∃ output : Reset.Term ℕ,
      Complexity.ResetSynthesis.synthesizeCode d.encode =
        some (Algorithms.TermCode.encode output) ∧
      output.size ≤ 1 + 2 * d.labels.length * d.records.length ∧
      ∀ (v : ℕ → WinnerSet Role) (winner : Role),
        winner ∈ (output.eval v).val ↔
          ∃ p ∈ d.records,
            (∀ k ∈ p.2, (v (d.labels.get k)).Ambiguous) ∧
            winner ∈ (v (d.labels.get p.1)).val :=
  Complexity.ResetSynthesis.synthesizeCode_encode_spec d hc
```

These are full statements, not exported aliases. They can supplement existing
Paper recognition/normalization/equality/extraction/substitution-formula
statements and close `main-prose:reset-algorithms`. The report's stronger
polynomial encoded-substitution claim remains optional and is not asserted by
this delivery.

Validation:

- `lake build KFOL.Complexity.ResetSynthesisMachine`: 2070 jobs passed.
- Full native source strict compile with warnings-as-errors and autoImplicit
  false passed before promotion.
- `tests/ComplexityResetSynthesis.lean` strict compile passed: billion-valued
  sparse original label, root at dictionary position 1 with nonroot first
  record, repeated root record, unused dictionary slot, exact generated tree,
  original output bytes, empty descriptor and malformed word.
- Entire source audit (including private declarations) covered 119 declarations
  in ResetSynthesisMachine and Records, admitting only propext,
  Classical.choice and Quot.sound. Regression file has 15 explicit guards for
  source scan, native runtimes, source construction and final semantics.
- Pure Records build 1125 jobs and independent 17-declaration axiom audit passed;
  mathlib-only import audit passed. No upstream/library/toolchain modifications.

No required synthesis gap remains.
