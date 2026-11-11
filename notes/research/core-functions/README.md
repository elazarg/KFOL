# All-arity core functions

The full winner-set term-function classification is not settled here.

The singleton-output predicates are settled in every finite arity by
`KFOL.Core.exists_term_iff_admissibleProfiles`, exported with its complete
statement in `Report.core_singleton_profiles`. The intrinsic conditions are
monotonicity, unanimity, and a nonempty intersection for every selection of
one winning coalition per owner. The proof constructs an actual core term:
each owner chooses a winning coalition, and a leaf returns the union of
variables in the common intersection. The interpretation on actual winner
sets is `Core.winnerSet_eq_singleton_iff_profile`.

Singleton profiles and variable support do not specify the whole function.
The two reset terms `x δ (y δ z)` and `(x δ y) δ z` have the same profiles
and support, but differ at `x={c}`, `y={a}`, `z={a,b}`.

## A stronger obstruction

`certificate.json` describes a ternary operation on the seven nonempty
subsets of three roles. Values are bitsets 1 through 7. The table is ordered
lexicographically by the three inputs, with seven consecutive outputs per
line. The six `rows` are valuations; `relation` is a set of 45 six-tuples.

The three input columns belong to the relation, which is closed under every
coordinatewise owned choice. Applying the candidate function to those columns
gives `(2,6,5,7,7,7)`, outside the relation. Thus no core term realizes it.
Exhaustiveness of the relation is unnecessary: closure suffices for this
structural-induction obstruction.

Nevertheless, the candidate is idempotent, monotone for ordinary inclusion,
and has the union of all three variables on the all-ambiguous cell. Every
status cell has union provenance. It passes every disjoint-region
common-source test and every substitution of three unary polynomial
functions. These include every unary section. Furthermore, such a
substitution yields the identity only if all three substituted functions are
the identity. That last condition is necessary for a full-support core term
by the existing idempotent-extraction theorem: any nonidentity unary
polynomial needs a winner parameter, and an identity term cannot contain
such a leaf.

The certificate was discovered with a temporary SAT search. Verify all its
properties independently, without the solver or any added package:

```
python3 notes/research/core-functions/check.py
```

This finite exploratory certificate is checked in Python. The all-arity
singleton-profile theorem, including its synthesis direction, is proved in
Lean and covered by the ordinary namespace and transitive axiom audits.
