# A four-row ambiguity obstruction

Write B={b,c,N,P}. Meet is minimum in b<P<N<c, join is maximum
in b<N<P<c, and observer union has P absorbing and b union c=N.
Terms may use all three operations. Consider four valuations of A,B,C,D:

| Row | A | B | C | D |
|---|---|---|---|---|
| E1 | c | c | b | b |
| E0 | b | b | c | c |
| R | N | P | c | b |
| S | P | N | b | c |

**Four-row law.** For every term t,

    t(E1)=c and t(E0)=b  imply  t(R)=P or t(S)=P.

This has an elementary invariant-relation proof. No enumeration of terms,
Boolean functions, or generated subalgebras is needed.

## The invariant relation

Let R4 consist of the tuples (x,y,z,w) in B^4 satisfying all three clauses:

1. If x=c, then z,w are different from b.
2. If y=b, then z,w are different from c.
3. If x=c and y=b, then z=P or w=P.

The four columns of the displayed matrix are

    (c,b,N,P), (c,b,P,N), (b,c,c,b), (b,c,b,c).

They all belong to R4. We prove closure under each operation coordinatewise.

For meet, an output x=c requires both inputs to have x=c, so neither
corresponding z or w is b. Their meet is again different from b. An output
y=b requires at least one input with y=b; that input's z,w differ from c,
so their meet with anything still differs from c. Thus clauses 1 and 2 hold.
If both endpoint premises hold, select an input with y=b. It also has x=c,
so it has P at z or w. The other input has x=c and hence is not b at that
position. Meeting P with any non-b value gives P. This proves clause 3.

The join argument is dual. For clause 3 select an input with x=c; both
inputs have y=b. The selected P cannot be masked by c in the other input,
so it survives the join. The endpoint rules prove clauses 1 and 2 as above.

For observer union, an output c at x requires c in both inputs, and an
output b at y requires b in both inputs. These facts preserve the first two
clauses. When both premises hold, either input supplies a P at z or w, and
P absorbs observer union. This preserves clause 3.

Induction on terms now proves the four-row law. The proof also allows
constants b and c: their constant four-tuples belong to R4.

## The two-test obstruction is sharp

Let f=AB OR AC OR BD. The two marked cubes R and S have respective Boolean
restrictions A and B. In particular, their marked coordinates B and A are
inessential. Nevertheless no term with Boolean function f can avoid P on
both rows: its outputs at E1 and E0 are c and b, so the four-row law applies.

Each test separately has a pure meet/join witness with Boolean function f:

    t_R = (A meet (B join C)) join (B meet D),
    t_S = ((A join D) meet B) join (A meet C).

Their values on (R,S) are (N,P) and (P,N), respectively. Thus the conflict
is genuinely between the two requirements. The cubes are disjoint, since
R fixes (C,D)=(1,0) and S fixes (C,D)=(0,1).

The [coherent-cube theorem](../coherent-cube-safety.md) proves more: any
family of marked cubes with a common Boolean vertex can be satisfied exactly
when its marked coordinates are individually inessential. A single cube
therefore never causes an additional obstruction. Two cubes are the smallest
possible budget that can do so.

## Application to the winner operation F

Observe owner a in the winner algebra: menus containing a map to P, the
singleton menus {b},{c} map to b,c, and {b,c} maps to N. On menus over these
three owners, the owned choices induce meet, join, and observer union.

For F from the [construction](README.md), the four outputs are

    F(E1)=c, F(E0)=b, F(R)=N, F(S)=N.

Here P in an input row may be represented by {a}. The two exceptional
regions defining F apply precisely at R and S, whereas E1 and E0 are atomic
and agree with H. These values violate the four-row law. Hence F has no
core term realization, even though its whole atomic boundary has one common
realizer and all its proper ghost residuals are core operations.

The standalone checker corroborates the matrix, the displayed witnesses,
and closure of the relation defined by the three clauses. The argument above
is the proof; there is no finite-clone completeness assumption.
