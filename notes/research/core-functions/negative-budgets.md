# Omission independence and irredundant upper bounds

Both statements are proved in `Core/Staircase`, using the independent atomic
rows in `Definitions/CoreStaircase`.

## Omission independence

If a is absent from t(v), arbitrary simultaneous changes to every input
containing a leave the complete value unchanged. Only inputs that omit a
must be kept fixed. This holds for arbitrary role and variable types.

Induct on the term. An absorbing singleton child omits a and so is unchanged
by induction; it continues to absorb. Without an absorber, both children omit
a and both are unchanged. The property gives the binary invariant relation

    R_a = { (A,B): a belongs to A or A=B }.

It is a useful direct constraint on source guards. The established local
interpolation crowns with locality at least two already preserve this and
all other binary invariant relations, so it is not a complete criterion.

## An arbitrary staircase

Choose distinct a,b,c and n variables. Row i gives input c to columns j<i,
a to column i, and b to columns j>i. Every row imposes the same upper bound:
owner a must be absent.

If a term satisfied all n bounds, omission independence would make its
values at both Boolean endpoints of each staircase step equal. Chaining
the steps identifies its constant-b and constant-c values, contradicting
idempotence. Deleting row i admits projection X_i, which contains a at that
row alone. Thus every proper subfamily is feasible and the whole family is
infeasible. All input values are atoms; no positive membership request or
prescribed profile is needed.

This proves that no fixed number of rows suffices to test upper-bound
feasibility. It is distinct from nonfinite relatedness: the staircase law
already follows from the binary omission relation and idempotence.

Exploratory six-row obstructions and finite negative-Helly counts are no
longer needed for this conclusion; the uniform staircase supersedes them.
