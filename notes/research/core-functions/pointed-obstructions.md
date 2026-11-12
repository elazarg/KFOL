# Pointed and normalized obstruction schemas

Research proof, pending formalization. This simplifies the already proved
clutter schema; it does not eliminate its auxiliary diagram quantifier.

## Statement

Fix finite K>=3, rows {q} disjoint-union N, a query owner a at q, and one
original forbidden owner k_i at each i in N. Suppose the projection columns
satisfy some core-invariant relation validating

    a in X_q ==> OR_(i in N) k_i in X_i.                 (Q)

There is an admissible boundary/no-trap clutter validating the same query,
containing all those columns, whose nontrivial clause heads:

* have no vertices in query row q;
* at each negative row i have fiber empty, {k_i}, or K\{r} for some r.

The row-full pure nonemptiness boundaries and membership tautologies remain
implicit. Consequently there are only (K+2)^|N| possible nontrivial heads,
and K+1 nontrivial stem families (pure plus every membership owner at q).
No nonoriginal singleton head is needed, even for the literal all-cut (T)
axiom, not only for selected elimination orders.

The converse is immediate from soundness. Thus the universal query test can
restrict exactly to these normalized clutters. It still quantifies over
clutters; no short direct guard condition or goal completion follows.

## 1. The row preorder

For owner k define, on nonempty winner sets,

    A <=_k B  iff  (k in A ==> k in B)
                     and (A != {r} ==> B != {r} for every r).     (1)

This records the monotone tests 'contains k' and 'is not singleton r'. Its
quotient has K singleton states plus N (ambiguous, k absent) and P (ambiguous,
k present). In the quotient join order, all singleton r!=k lie below N<P,
while singleton k lies below P and is incomparable with N. This is only an
explanatory quotient; the proof can use (1) directly.

Every owned choice is monotone for <=_k. For membership k, use the owner/
other-owner membership recursions: preserved k-membership and exclusion of
absorbing singletons pass from old operands to larger ones. For each
non-singleton test, argue contrapositively with singleton profiles: if the
new output is {r}, one new operand is {r} at an r-choice, or both are {r}
at another owner's choice; (1) makes the corresponding old operands {r}.

## 2. A mixed order closure preserving the query

Let R be any invariant relation containing the input columns and validating
(Q). Form R^sharp of tuples X for which there is Y in R with

    X_q subseteq Y_q,
    Y_i <=_(k_i) X_i for every i in N.                    (2)

This is downward closure at the query row, and upward closure at each
negative row. Choice monotonicity for inclusion and (1) makes R^sharp
invariant. It contains the input columns. It still validates (Q): a positive
query in X was already positive in Y, while original k_i-membership cannot
be lost at any negative row.

It is also union-closed, and retains the mixed closures in (2).

## 3. Head rounding under negative upward closure

For an owner subset T at negative row i define

    rho_i(T) = T            if |T|>=K-1;
               {k_i}        if |T|<=K-2 and k_i in T;
               empty        otherwise.                         (3)

Thus rho_i(T) is an allowed head fiber, or the full row (a tautology).
The key elementary fact is

    every B >=_(k_i) A meets T  iff  A meets rho_i(T).             (4)

For |T|>=K-1, the test 'meets T' is either nonemptiness or 'not singleton r',
so it is already monotone. In the other case, suppose A misses rho_i(T).
There are at least two owners outside T. Choose an ambiguous two-owner B
outside T, including k_i if k_i is in A. This is possible because if k_i
lies in T, the hypothesis already says k_i is not in A. Then A<=_(k_i)B and
B misses T. This proves (4).

Apply rho rowwise to any head S having no query-row vertices. Since R^sharp
is upward-closed independently at the negative rows, a pure or query-stem
clause with head S is valid on R^sharp iff its stronger clause with head
rho(S) is valid: if rho(S) fails, choose the B_i in (4) simultaneously and
use upward closure to contradict validity of S. Conversely rho(S) subseteq S.

This is the point that handles arbitrary cuts of an old off-owner block.
Their partial nonoriginal singletons can be deleted without losing validity,
so they never need to become independent certificate heads.

## 4. Complete clause presentation with heads away from q

The following proves that normalized clauses already present R^sharp.
Take a nonempty raw tuple X outside R^sharp. If for every a in X_q the tuple
({a},X_N) belonged to R^sharp, their finite union would be X. Hence choose
a in X_q with ({a},X_N) outside R^sharp.

By the mixed order closures, no Y in R^sharp can have a in Y_q and
Y_i<=_(k_i)X_i at every negative row. Thus the valid clause

    a in Y_q ==> OR_i NOT(Y_i<=_(k_i)X_i)                         (5)

separates X. Each negative-row test in (5) is exactly one allowed head:

    X_i singleton r         : K\{r};
    X_i ambiguous, k_i absent: {k_i};
    X_i ambiguous, k_i present: empty.

This follows immediately from (1). Empty raw coordinates are excluded by
pure row-full nonemptiness boundaries. Thus the clauses (5), over all a and
all allowed heads valid on R^sharp, together with the row boundaries,
present R^sharp exactly. All nontrivial premises are at q; pure valid heads
may be added without changing the model relation.

## 5. Literal no-trap, not just selected orders

Take all valid normalized negative-only heads at the pure stem and each
query-row stem, add row-full boundaries and tautologies, then minimize
supports to obtain clutters. For every negative-only head S, Section 3 says
that semantic validity of a pure/query-stem clause is equivalent to support
by a normalized head contained in S.

Now fix a nontrivial minimal head H, an owner r and any H_r subseteq S
proper subset H as in (T). If the S-restricted clause were valid, rounding
would support S by a proper normalized head, contradicting minimality of H.
It is therefore invalid. Apply the existing semantic blocker-progress proof
to the invariant relation R^sharp. It supplies a remaining head vertex with
valid blockers. Since H and S have no query-row vertices, the blocker row
is negative and every blocker head B_r(i,S) is also negative-only. Section 3
rounds each valid blocker to a supported normalized subhead. This is exactly
(T), for every cut S.

The exceptional row-full pure heads satisfy (T) trivially: the initial
r-colored vertex at that row plus its off-owner block is the whole row,
which is already supported. A tautological edge {p} has no proper initial
cut at its own owner; at another owner its conditional blockers are
membership tautologies. Fill every nonquery stem with pure weakening and
tautologies, as in the fixed-stem reduction. Their (T) obligations reduce to
the pure case or the tautology case.

The resulting literal clutters satisfy (B),(T), contain all projection
columns, and support the original query (Q), whose head was already
normalized. This proves the statement.

## An unavoidable four-vertex auxiliary head


Use the three atomic rows already in AtomicAmalgamation:

       X Y Z
    A  0 1 2
    B  0 2 1
    C  1 2 0

Write rA for the membership atom (A,r), and likewise B,C. The projection
output columns, written as masks, are X=(1,1,2), Y=(2,4,4), Z=(4,2,1).
Consider the valid persistence clause

    2A ==> 0A or 1B or 2C.                    (C)

It is valid throughout the explicit choice-closed relation certified in
Core/AtomicAmalgamation, hence on every core term. This can be checked from
six entries of its published matrix: if 2A holds and 0A does not, the A-mask
is 4 or 6; if 1B is absent the B-mask is 1,4,5. The corresponding entries
are, respectively, (0,8,0) and (0,8,112); every allowed C-mask has owner 2.
Thus a diagram containing the columns and supporting (C) exists by the
closed-hypergraph theorem.

**Claim.** Every admissible diagram containing these projection columns and
supporting the head H={0A,1B,2C} at stem 2A must literally contain the pure
edges

    U={0B,1B,2C},
    V={0A,1A,1B,2C}.                          (F)

In particular V has cardinality four, larger than the target head's three.
These are additional mixed-row edges, not row-nonemptiness boundaries.

First H is a minimal valid head at stem 2A. The following core terms have
the premise and meet H only in the displayed atom:

    term                         (A,B,C) masks    sole H atom
    (Z star_2 Y) star_1 X         (5,5,2)          0A
    Z                            (4,2,1)          1B
    Z star_2 Y                   (4,4,4)          2C

The model set of an admissible diagram containing the projections contains
all these term tuples.
Consequently support of H at 2A must be witnessed by the edge H itself;
no smaller edge is possible.

Apply (T) to that edge and owner 2. The initial cut is S={2C}. The vertex
0A cannot be exposed: its required pure blocker is

    {0A,1A,2C},

which projection Z misses. Thus 1B must be exposed, and its blocker U must
be pure-supported. Each of X,Z,Y meets U in exactly one distinct atom
(0B,1B,2C, respectively). Hence no proper subset of U can be pure-supported:
U itself is an edge.

Now apply (T) to the proper cut S={1B,2C}. Its only remaining vertex is 0A,
and its required pure blocker is V. The following core terms meet V only in
the indicated atom:

    term                         (A,B,C) masks    sole V atom
    X                            (1,1,2)          0A
    Y star_1 X                   (2,5,2)          1A
    Z                            (4,2,1)          1B
    Z star_2 Y                   (4,4,4)          2C

Thus V itself is a pure edge. This proves the claim solely from the literal
(B),(T) axioms and evaluations of short terms, not from completeness of a
search or from the syntactic weakening policy of the old checker.

Consequences: the fixed-query diagram test cannot be restricted to auxiliary
heads of size at most the target head; or to the original negative atoms;
or to row boundaries plus a single extra pure edge. These precise proposed
simplifications already lose a three-row obstruction. A simple graph of
pairwise clause-head edges also loses it even when the target head is allowed
as a separate three-way conclusion.

This does NOT exclude a richer graph construction with vertices for subsets,
or arbitrary hypercycles on all row-owner atoms. Such a construction could
encode V, and further argument would be required to show completeness.

## 3. Why the other owners at the fixed premise row cannot all be discarded

Take two identical valuation rows A=B with singleton projection inputs 0,1,2.
The generated relation is the diagonal {(S,S):S nonempty}. The clause

    0A ==> 0B

is valid. Its pure covers describe the upward closure of the diagonal,
namely pairs with a common winner. Combining all such pure covers with this
one implication does not give an invariant relation:

    X=({0},{0}),  Y=({1,2},{1})

both have common winners and satisfy the implication, but their owner-1
choice is ({0,1,2},{1}), violating it. Conditional blockers with other
membership owners at row A are therefore substantive, not mere bookkeeping.
