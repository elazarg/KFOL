# Candidate synthesis normal form: bounded values and atomic cuts

This is a research specification for the next formalization step. The Python
prototype checks the two retained finite examples. The general correctness
argument below has not yet been formalized. It gives a target-directed
recognition procedure, rather than the sought structural description of the
core clone.

Fix finite role and valuation sets, with at least three roles. Write `v_j` for
the tuple of values of input variable `j` across the valuations. Let `U_i` be
the required upper bound at valuation `i`.

At each coordinate `i`, allow the following bounds:

```
U_i,  I,  {r} for every owner r.
```

There are at most `(K+2)^m` bound vectors, where `m` is the number of
valuations. For each vector `B`, maintain either no value or one tuple `M(B)`.
The intended meaning is the largest term value bounded by `B`. A stored tuple
has one actual core term as its witness; coordinates are not assembled from
unrelated terms.

Initialize `M(B)` with the union of all input columns bounded by `B`, leaving
it absent if no column qualifies. Neutral union makes this a term value.

For a root owned by `r`, choose independently at each coordinate one of these
pairs of bounds for its children:

| Condition | Left bound | Right bound |
| --- | --- | --- |
| Always allowed | `B_i` | `B_i` |
| `r` belongs to `B_i` | `{r}` | `I` |
| `r` belongs to `B_i` | `I` | `{r}` |

For each resulting pair `(L,R)`, if both `M(L)` and `M(R)` exist, add
`M(L) ⋆_r M(R)` to `M(B)` by union. Repeat until no bound changes.

The atomic cuts make each production safe: either both children are bounded,
or an owner's singleton absorbs the unrestricted child. Monotonicity and
idempotence handle the bounded/bounded case. Every update remains an actual
term value. Each update strictly adds a role at some coordinate, or changes
an absent value to a nonempty tuple, so there are at most `K*m*(K+2)^m`
updates. Witness terms can be retained as a DAG and unfolded if required.

For completeness, consider a term bounded by `B` and its two children at an
owned root. At a coordinate where the left value is the owner's singleton,
choose the left atomic cut. Otherwise choose the right atomic cut if its
value is that singleton. At every remaining coordinate the operation is
union, so both child values are bounded by `B_i`. These choices give two
allowed bound vectors. Induction puts the actual child values below the
stored maxima for those bounds. Monotonicity then puts the root value below
the production already included in `M(B)` at the fixed point.

Consequently, the proposed synthesis test for a function is to use every
input valuation as a row and the function's output table as `U`, and check
`M(U)=U`. This uses bounds and atomic cuts, not closure over all term tables.
It still has exponentially many states in the number of rows; no efficient
structural classification is claimed.

For the two current obstructions, the prototype gives:

| File | Requested tuple | Largest bounded term tuple |
| --- | --- | --- |
| `certificate.json` | `(2,6,5)` | `(2,2,5)` |
| `remaining.json` | `(5,3,5)` | `(1,1,1)` |

The second example has only the common atom below the three requested regions.
Its failure involves surviving ambiguous contributions, even though all
singleton-profile conditions and the first persistence law hold.
