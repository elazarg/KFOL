# Native shared reset DAG semantic gate

Required scope: report `reset:thm:circuits`, cited by the main tree-representation
paragraph immediately after `gen:thm:complexity`. This delivery is the complete
paper-specific semantic/CNF/count gate. Native binary codec/runtime/class
transport is the next owned stage; the coNP-completeness result remains partial
until that stage is certified.

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

Next stage (same worker owns): exact native shared-graph binary word codec
with malformed rejection, polynomial original-graph CNF generator, cached
Fin3 evaluator/countercertificate checker, coNP verifier and pinned machine
3SAT/coNP-hardness transport. General finite-signature cached value evaluator
must deduplicate winner lists when later supporting arbitrary winner values;
no algorithm may unfold the graph. Parent reprioritized this before reset
synthesis/substitution runtime endpoints. No manuscript/Paper/audit/config
files were edited by this worker.
