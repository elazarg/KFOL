# Original reset DAG generator: complete native runtime

`KFOL.Complexity.CircuitGenerator.encoded_reduction_polyTime` proves the actual
native machine runtime of

```lean
fun φ => Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation φ)
```

from `ResetUnionReduction.cnfEncoding` (the original nested-list binary CNF
encoding) to `encBits`. It has no size, growth, semantic, finite-certificate,
fixed-variable-count or caller-supplied runtime hypothesis.

`reduction_polyTime` first constructs the exact original graph under
`CircuitMachine.dataEncoding`; `CircuitMachine.encodeData_polyTime` and
`encodeData_view` then give the exact original graph word. The output is never
an unfolding of the graph.

The source transports are:

- `view_buildRightComb`, original reverse emission order;
- `view_buildClause`, retained predecessor shared by reference;
- `view_buildConsistency`, original two-node forward blocks plus comb;
- `view_buildCNF`, all actual clause prefixes, including empty clauses.

All transports hold for arbitrary original input gates and arbitrary numeric
references, without requiring well-formedness. Existing independent
`equation_wellFormed` and `eval_equation` establish the generated circuit's
structural and semantic correctness.

The implementation obtains every new cache position from a physical list
length or a unary index into an actual list. Sparse literal dictionaries retain
mathlib's exact rightmost deduplication order. Names and cache references are
binary; support computation and dictionary lookup never enumerate through a
maximum numeric name. `slots` receives its loop count in unary, sourced only
from actual list lengths. Prefix rescanning can cost a polynomial amount of
extra time but never duplicates a predecessor subgraph into a gate.

Modules: CircuitGeneratorRecords, Comb, Builders, Blocks, CNF, CNFMachine,
References, CircuitGenerator, all in KFOL/Complexity. Eight production modules. The small Records module exports the unique
Reset operation Fintype instance reused by the cached circuit verifier.

Validation: fresh production Lake build passed 2192 jobs, followed by strict
production regressions and all-declaration auditing. Strict compilation of every file with autoImplicit=false and
warningAsError=true; 130-declaration source/transitive axiom audit permits only
propext, Classical.choice, Quot.sound; strict regression tests connect the exact
original runtime theorem and decoder roundtrip and check repeated cache
references, empty CNF, empty clauses, and billion-valued sparse names.
