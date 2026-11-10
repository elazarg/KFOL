# Native shared reset DAG formalization — required fragment complete

Required scope: the FIRST TWO clauses of report `reset:thm:circuits`, cited by
the main tree-representation paragraph after `gen:thm:complexity`: reset DAG
word-language coNP-completeness at fixed K≥3, already on the actual three-value
generator. These clauses now have complete native machine proofs. Root checked
the main text and explicitly classified the report environment as a required
dependency_fragment. Its H/policy DAG class clauses are optional; the pure
repeated-edge semantic transports remain proved independently.

Generic untrusted definitions are concentrated in the new
`KFOL/Definitions/Circuits.lean`, importing ONLY Definitions/Reset. Sparse CNF
program/input/SAT-witness data are in the existing Definitions/Reductions.
There is no import from GameTheory or ComplexityLib in the pure graph branch.
No policy-definition import is added to Reductions (Policies imports it).

The independent native graph is `Circuit.Equation σ Var`: one actual list of
`Gate.input j | Gate.func operation refs` plus two output cache indices.
Each vector is typed `Fin arity → Nat`; its external view is EXACTLY
`List.ofFn refs`, in numeric Fin order. `ValidFrom` checks every ref is strictly
earlier than its original gate; `WellFormed` also checks both outputs.
`Gate.eval` rejects out-of-cache refs before indexing, and `runFrom` appends
exactly one real algebra value per gate. It never uses a default value or a
numeric-maximum loop. `Equation.Holds M` requires original-graph wellformedness
and two actual equal cached outputs for every valuation; None=None is never
used as validity. Winner-set evaluation uses actual sets, so graph sharing
does not create representation-list multiplicity.

The `Reductions/Circuits` branch contains:

* Basic: totality/cache-prefix preservation, fixed reference order, structure
  homomorphisms acting on actual caches, gate/run/equation commutation.
* Builder: original topological right-comb, clause, CNF and consistency gate
  builders. Each has independent reference/output bounds, exact gate counts,
  and actual shared-cache evaluation in every reset-signature algebra.
  Previous clause outputs are cache refs, never recursive tree copies.
* ResetCNF: the actual sparse-input native source equation. With
  N=`Reductions.ResetUnion.support formula`.length (including its dummy0)
  and L=`formula.flatten.length`, the ORIGINAL graph has exactly
  **5*N+2*L+1 reset nodes** and **7*N+2*L+3 total nodes**, including
  2+2*N input nodes. `equation_wellFormed`, `equation_reset_gate_count` and
  `equation_gate_count` prove these quantities for all CNFs, empty clauses
  and empty conjunctions included. `eval_equation` proves the actual output
  pair is `(A_q reset R,R)` in every algebra/every valuation.
* Values/Satisfying: original clause OR/shared-continuation AND marker
  semantics, inconsistent-rail absorption, full winner-valued UNSAT
  correctness and explicit SAT countervaluation. The countervaluation uses
  ONLY the displayed generator values Z,U,T at EVERY variable, including
  unused names. No input has an arbitrary supplied finite certificate.
* Unfold: independent native evaluation agrees with proof-level unfolding
  into actual free terms. `Equation.reset_holds_iff_chain` proves that
  EVERY wellformed reset DAG is completely tested by the fixed three-value
  chain, using the completed reset-term theorem. This unfolding may be
  exponential and is never executed by a native algorithm.
* Transfers: each reset node with refs `[left,right]` maps to a single
  ternary node with refs `[right,left,left]`. `gates_liftReset` proves every
  target gate is an input or ONLY the selected ternary operation: no
  primitive reset remains. Graph nodes/output refs are preserved exactly;
  reset edges=2*reset-node-count, target edges=3*reset-node-count.
  `eval_toGuarded`/`eval_toPolicy` instantiate the actual winner-set diagonal
  laws without a minor/correctness hypothesis. Thus the pure H-only and
  any single-policy CNF reductions are fully connected to native graphs.
  Concrete theorem statements name `liftReset (.guarded ())` or
  `liftReset (.selective label)` explicitly; no separate interpretation
  aliases enlarge the definition surface.

Full proposed paper-facing pure theorem statements:

```lean
theorem reset_dag_cnf_equation {Role : Type u} (three : Fin 3 ↪ Role)
    (formula : Reductions.CNF) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    (Circuit.ResetCNF.equation formula).Holds (WinnerSet Role) ↔
      ¬Reductions.Satisfiable formula

theorem reset_dag_three_generator {Role : Type u} {Var : Type v}
    (three : Fin 3 ↪ Role) (equation : Circuit.Equation Reset.Symbol Var) :
    let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
    equation.Holds (WinnerSet Role) ↔ equation.WellFormed ∧
      ∀ valuation : Var → WinnerSet Role,
        (∀ j, ∃ stage : Fin 3,
          valuation j = Reset.chainValue three stage) →
        ∃ value, equation.eval valuation = some (value, value)

theorem guarded_dag_cnf_equation {Role : Type u} (three : Fin 3 ↪ Role)
    (owner : Role) (formula : Reductions.CNF) :
    let _ := Owner.oneOwnerStructure owner
    ((Circuit.ResetCNF.equation formula).liftReset
      (Owner.Symbol.guarded ())).Holds (WinnerSet Role) ↔
        ¬Reductions.Satisfiable formula

theorem policy_dag_cnf_equation {Role : Type u} {Label : Type w}
    (three : Fin 3 ↪ Role) (D : Label → Set Role) (label : Label)
    (formula : Reductions.CNF) :
    let _ := Policies.structureOf D
    ((Circuit.ResetCNF.equation formula).liftReset
      (Policies.Symbol.selective label)).Holds (WinnerSet Role) ↔
        ¬Reductions.Satisfiable formula
```

Proofs are respectively `ResetCNF.equation_holds_iff_unsatisfiable`,
`Equation.reset_holds_iff_chain`, `ResetCNF.guarded_holds_iff_unsatisfiable`,
`ResetCNF.policy_holds_iff_unsatisfiable`. No full complexity conclusion is
claimed from these pure statements alone.

Validation: production `lake build KFOL.Reductions.Circuits` passed all1137
jobs. Regression `tests/ReductionsCircuits.lean` checks actual references,
strict-prefix WF, empty CNFs/clauses, sparse label1000000000 without max-name
allocation, exact node counts, rejection of absent outputs, the three
semantic reduction endpoints and absence of primitive reset in the ternary
interpretations. Twenty-one central theorem axiom checks use only standard
propext/Classical.choice/Quot.sound (several need fewer); exact outputs are
guarded in the regression. All pure staging modules compiled first.

The final native implementation is now production and fully built:

* `Algorithms/CircuitCode`: exact flat gate/graph encode/decode roundtrip AND
  converse, injectivity, physical gate-count versus original byte-length.
  Code definitions are centralized in existing Definitions/Encoding.
* `Complexity/CircuitRecords`: bounded-arity native records carry an optional
  finite opcode and binary variable/ref lists. `view` retains the original
  shared gate list/output refs; operation args stay in numeric Fin order.
* `Complexity/CircuitCodec`: actual native original-word encoder/parser,
  including canonical binary names, complete framing and arity validation.
  `encodeData_view` is EXACT original graph bytes; `decodeData_eq` proves
  native parsing is exactly pure decoding mapped to its physical record view
  on EVERY word. Malformed and trailing words cannot enter the language.
* `Complexity/CircuitEvaluator`: checked binary-ref lookup, cached original
  node evaluation, safe output lookup and actual complete polynomial runtime.
  `evaluate_view` is the independent typed graph evaluator, including failed
  refs/outputs. Its finite algebra values have constant encoded width; one
  value is appended per node, so sharing never doubles representation lists.
* `Complexity/CircuitVerifier`: a complete native countervaluation verifier,
  with physical input-node names (repeats retained) and at most finite-card
  bits per actual input occurrence. Every arbitrary supplied certificate
  decodes to genuine algebra values; invalid graphs are rejected. The
  padded witness theorem supplies full machine-level coNP membership for
  every fixed finite algebra/signature, using ORIGINAL cached graphs.
* `Complexity/CircuitCompleteness`: the actual Fin3 reset table gives coNP
  membership; proof-level graph/model equivalence transfers the SAME Fin3
  verifier to every role carrier with a three embedding, without enumerating
  its carrier or using numeric label maxima.
* `Complexity/CircuitGenerator*` (worker nonfinite_basis, own delivery note):
  native static-offset graph builders have exact source-order/cache-ref
  correspondence and polynomial runtime. Final
  `CircuitGenerator.encoded_reduction_polyTime` produces EXACTLY
  `fun φ => Circuit.Code.encode Reset.Symbol (Circuit.ResetCNF.equation φ)`
  under the pinned CNF codec, for all CNFs and all widths. No detached size
  certificate or supplied abstract generator correctness is substituted.
* `Complexity/CircuitHardness`: source correctness for every CNF, native
  generator runtime and pinned machine-level3SAT completeness are connected
  by the shared total `CNFHardness.coNPHard_of_CNF` rule (wide3SAT inputs map
  to an actual valid fallback graph). This closes actual many-one hardness.

The TWO final unconditional class endpoints (import CircuitHardness) are:

```lean
theorem CircuitCompleteness.reset_chain_coNPComplete :
  let _ := Reset.structureOf
    (fun i j : Fin 3 => if j = 0 then 0 else max i j)
  Cslib.Complexity.coNPComplete encBits
    (Circuit.Code.Language Reset.Symbol (Fin 3))

theorem CircuitCompleteness.reset_coNPComplete {Role : Type u}
    (three : Fin 3 ↪ Role) :
  let _ := Reset.structureOf (WinnerSet.reset (Role := Role))
  Cslib.Complexity.coNPComplete encBits
    (Circuit.Code.Language Reset.Symbol (WinnerSet Role))
```

For a paper-facing FULL proposition, the language in either theorem expands
without a delegation alias to

```lean
{ word | ∃ equation : Circuit.Equation Reset.Symbol Nat,
  Circuit.Code.encode Reset.Symbol equation = word ∧
  equation.WellFormed ∧
  ∀ valuation : Nat → M,
    ∃ value : M, equation.eval valuation = some (value,value) }
```

with the displayed actual model M. Thus malformed codes, invalid references,
cycles and invalid outputs are excluded. None=None cannot certify validity.
The upper bound's complete verifier parses and evaluates the original graph;
it NEVER unfolds a shared subexpression. The unfolding used for the finite
model theorem is only a mathematical proof construction. Actual costs are
certified by ComplexityLib's deterministic multitape machine predicate, not
a project-specific abstract polynomial notion or a finite certificate.

Final validation: `lake build KFOL.Complexity.CircuitHardness` passed ALL2179
jobs. `tests/ComplexityCircuits.lean` passed with both warnings-as-errors and
autoImplicit=false, including21 exact axiom guards for codec inverses,
physical bounds, the real finite model, native encoder/decoder/evaluator,
verifier soundness/completeness, both uppers and ALL FOUR final hardness/class
endpoints. Every check has only propext, Classical.choice, Quot.sound. The
regression also checks actual invalid billion-index cached rejection,
original-word codec correspondence, finite3 completeness and infinite-Role
WinnerSet completeness (no role-carrier enumeration). The generator worker
separately checked its130 declarations and native source regression.

Next REQUIRED item (same worker): actual original reset table synthesis
runtime. A separate encoded substitution runtime was explicitly reclassified
optional by root after reading the main prose; its required substitution
FORMULA is already proved. No manuscript/Paper/audit/config files were edited
by this worker; parent owns public statement/inventory integration.
