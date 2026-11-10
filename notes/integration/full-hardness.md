# Original full/core hardness and canonicalization: ready

All files strictly compile with Lean 4.35.0, autoImplicit=false and
warningAsError=true. The complete regression passes. All authored/generated
source declarations across FullHardnessSyntax, FullHardnessMachine,
FullHardness, FullHardnessPublic, Canonicalization and FullCertificateSize are
transitively audited:
82 declarations, standard three axioms only.

## Integrated modules

Production modules: `FullHardnessSyntax`, `FullHardnessMachine`,
`FullHardness`, `FullHardnessPublic`, and `FullCertificateSize`, under `KFOL/Complexity`.
`Canonicalization` adds the complete actual-core-subtype specializations.
`tests/FullHardness.lean` checks the public endpoints and native transport.

The original full/core construction introduces no independent semantic
predicate: `Term.eval`, `Term.IsCore`, `FullLanguage` and `CoreLanguage` retain
their existing definitions. Helper encodings are literal restrictions of the
same original explicit-array byte representation.

Fresh production `lake build` passed 2192 jobs. Both regression files passed
with `autoImplicit=false` and `warningAsError=true`; all-declaration transitive
axiom audits checked 130 generator and 82 lower/canonicalizer/helper declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur.

## Exact endpoints

`FullHardness.full_coNPHard`:

    Cslib.Complexity.coNPHard encBits FullTermCode.FullLanguage

`FullHardness.public_coNPHard`:

    Cslib.Complexity.coNPHard encBits FullTermCode.PublicLanguage

The public signature permits original winner constants and choices while
forbidding internal renames. `fixed_public_coNPHard` supplies the same fixed-K
endpoint. The generated hardness instances already belong to the core.

`FullHardness.core_coNPHard`:

    Cslib.Complexity.coNPHard encBits FullTermCode.CoreLanguage

The existing independent languages require K >= 3 and exact original explicit
array syntax bytes. Hardness outputs actual original K=3 terms, with only two
owned-choice symbols; every target is proved IsCore. Both semantic directions
follow from actual original evaluation, with no named external theorem assumed.

`fixed_full_coNPHard a b d hab had hbd` and `fixed_core_coNPHard ...` work for
every Fin K containing the three specified distinct roles. Their target
encoding is exactly `encodeEquationInput ⟨K,e⟩`, where e is a pair of the actual
original Term (Fin K) Nat syntax. The core predicate additionally requires
both actual terms IsCore. Thus fixed-K hardness is not merely hardness for the
uniform language at one convenient header.

`equationWord_polyTime a b` executes the exact original target word mapping on
arbitrary original native source equations. Each source binary node produces
one original target choice node; variable labels and repeated occurrences are
preserved, without winner leaves, renames, macros or permutation enumeration.

`Canonicalization.original_core_comparator` uses the ACTUAL CORE SUBTYPE:

    CoreTerm K := {t : Term (Fin K) Nat // t.IsCore}

and its restricted original term word embedding. Given three distinct roles,
a native polynomial canonicalizer, a native polynomial word comparator and
full semantic correctness of comparison for every two core terms, it concludes
P encBits = NP encBits. No runtime behavior is required outside the core.
`original_core` specializes to literal equality of canonical output words.

`FullCertificateSize.framed_pairValues_length_le input pairs` bounds EXACTLY

    (Words.delimit (Algorithms.LabelDictionary.encode
      (FullSparseEvaluation.pairValues
        (FullTermSize.labels (view input.2.1) ++
          FullTermSize.labels (view input.2.2)) pairs))).length

by `16 * ((encodeEquationInput input).length + 1)^2`. Every guessed role is
bounded by actual binary K, source pool length by actual tree bytes. No maximum
variable label or cardinality enumeration is charged as constant time.
