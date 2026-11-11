# Recognition by repeated singleton tests

`peeling.py` independently checks the finite row-deletion equations below.
It uses only Python's standard library. Run:

```
python3 notes/research/core-functions/peeling.py
python3 notes/research/core-functions/peeling.py --full --owners 3
python3 notes/research/core-functions/peeling.py --full --owners 4
```

The recognizer never enumerates terms, computes a generated subpower, or
consults auxiliary invariant clauses. A separate unpruned subpower enumerator
is used only as an independent semantic oracle. The default suite checks empty
rows and variables, empty bounds, conflicting and repeated atomic demands,
small random matrices, and the known six-row obstruction with 7,260 generated
tuples. Full mode exhausts every raw upper tuple and positive query for the
small matrices, also testing exact tuple realizability by union of membership
witnesses. It adds mixed queries with demands inside and outside the bounded
row set. The six-row oracle uses three owners; extra owners act as the already
derived union on that matrix.

## The three equations

Fix finite role and row sets I and Q, with |I|≥3, a finite family of input
columns c_j in Pow(I)^Q, and raw upper bounds A_i⊆I. A finite set N⊆Q selects the bounds
currently imposed. A finite demand set D⊆Q×I asks for the exact atom {r} at
row i for every (i,r)∈D. A positive query p is either absent (written ⊥) or a
pair (q,k) asking for k at row q. Rows appearing in D or p need not belong to
N. A rainbow subset of D contains at most one demand per owner; the empty
subset is included.

Let Col_N(D;p) mean that some input column fits all current bounds, all exact
atomic demands, and the optional positive query. Define G and F by:

```
(1) G_N(D;p) = Col_N(D;p)
                or exists i∈N, r∈A_i:
                     F_(N\{i})(D∪{(i,r)};p).

(2) B_N(D) = for every rainbow S⊆D: G_N(S;⊥).

(3) F_N(D;⊥)   = B_N(D),
    F_N(D;q,k) = B_N(D) and G_N(∅;q,k)
                 and for every (i,r)∈D with r≠k:
                       exists s≠r: G_N({(i,r)};q,s).
```

This is well founded: first define G at rank |N| using F at smaller ranks,
then define F at that rank from G. Atomic challenges and positive queries may
change, but every recursive call that returns from G to F deletes a bounded
row. The maximum deletion rank is |N|.

Their exact meaning is that F_N(D;p) holds precisely when one core term fits
all N-bounds, D-demands and the optional positive query. Empty bounds are
allowed. Conflicting atomic demands fail the rainbow test. If there are no
variables, even the empty rainbow challenge has no generator and fails. For
an empty row set with at least one variable, a projection supplies the unique
empty evaluation tuple.

## Why the equations are complete

Consider all core evaluation tuples fitting N. They are generated under core
operations by the bounded projection columns and those bounded tuples that
are atomic at some bounded row. To see this, induct on a term: an atomic
bounded-row output is already a boundary generator. Otherwise every bounded
row is ambiguous at the parent, so no root-owned absorption occurs there;
both children are bounded and the root combines their tuples. Conversely,
owned choice is contained in the union of its operands, so bounded tuples
remain bounded under every core operation. Equation (1) describes exactly
this generator set through a smaller bound set and one new atomic demand.

For each atomic demand (i,r), let E_(i,r) be the generators whose row-i value
is {r}. The least required owner-r singleton profile is generated upward by
these E_(i,r) and by the full generator set, which enforces unanimity even when
owner r has no demands. The constructive profile classification says that
these profiles can be realized exactly when every rainbow selection of the
E_(i,r) has nonempty intersection. Unselected owners use the full generator set.
This is equation (2), including the empty selection that requires at least
one generator.

For a positive query (q,k), the base positive generator makes the union of all
generators contain k at q. For any demand (i,r) with r≠k, the last condition in
(3) says E_(i,r) is not contained in the generators whose row-q value is {r}.
The base positive generator also lies outside that wrong-singleton set,
so even the unanimity coalition does not force it. Consequently the least
demanded r-profile does not force that wrong singleton at q. Synthesize the
least admissible profiles and take their greatest profile
completion. At q it returns {k} when the synthesized term is atomic, and
otherwise returns the union of all generator values there. Either value
contains k. This proves (3). Necessity follows from the same profile tests and
provenance.

## Applying the test directly to canonical guards

For a canonical family Γ, let C(k,j,p) be its Boolean source coefficient and
let Q be the fixed set of n K^n isolated-source probes. Use their projection
columns as c_j. Put

```
N = {q=(k,j,p): C(q)=false},       A_q = I\{k} for q∈N.
```

Then Γ is realizable exactly when it is canonical and

```
F_N(∅;⊥) and for every q=(k,j,p) with C(q)=true: F_N(∅;q,k).
```

All ingredients are read from the guard table and these fixed probes. Fitting
N forbids precisely the false source observations. For every true observation,
the positive test supplies a bounded witness; their finite union realizes all
true observations simultaneously. The initial feasibility test handles the
case with no positive observations, including empty variables. Canonicity and
source reconstruction then identify the resulting prime families with Γ.
One may instead use the full raw probe meaning as upper bounds, requiring a
positive witness for every membership in every target row, together with one
bounded witness. Both versions avoid auxiliary term or invariant-clause
witnesses in the stated test, while retaining the finite peeling recursion.

This is recursive recognition, not the sought short structural guard
characterization. Finite relatedness remains unsettled; the five-local
counterexample rules out defining families of invariant relations with arity
at most five.
