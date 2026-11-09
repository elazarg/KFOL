# Complete serial SE / observed mixed-SPE correspondence

`KFOL/Rounds/Correspondence.lean` finishes the independent semantic bridge.
`consistent_rationality_iff_subgamePerfect` compares canonical sequential
rationality against canonical whole-policy Nash in every actual public
subgame. Consistency forces the product belief at every public history,
including zero-reach histories. `SerialRun` identifies its actual complete
terminal law after any player's whole-policy replacement with the projected
observed continuation law. Every source replacement lifts to a serial one;
terminal source comparisons are automatic.

`sequentialValues_eq_observedValues` proves both inclusions. The reverse
inclusion constructs consistent assessments for the lifted profile rather
than assuming a supplied equilibrium certificate. The actual root winner
laws agree, independently of certified run fuel. `sequentialValues_round`
and its fully expanded `_iff` then give the exact all-tuples selected-
continuation mixed-Nash recursion. Equal continuation syntax at different
joint tuples remains separate in policies and selections.

Root `Paper.lean` repeats equality of the independent value sets, the leaf
Dirac equation and the full existential round proposition as
`round_equilibrium_recursion`. No new axioms, recursive equilibrium
definition, or positive-reach assumption enter these statements.

Validation: the complete production Lean build, whole-source transitive
axiom audit, independent algebra import audit and all strict regression
files pass under `make check-lean`. `make paper` passes; main text stays
14 pages and the verification appendix now records the completed bridge.
