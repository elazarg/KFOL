# Eight-cofactor obstruction to hereditary SCC sufficiency

Put

    F = cd ∨ af ∨ ace ∨ ade ∨ cef ∨ bdef,
    H = cd ∨ af       ∨ ade ∨ cef ∨ bdef.

Their six-variable truth masks, with Boolean assignment index the subset
bitmask of a,b,c,d,e,f, are respectively 18373273242067595264 and
18373273242057109504.

The canonical essential-source extension D_F is not a pure bichain term
operation, and consequently is not a full union-expanded term operation.
Nevertheless every proper Boolean cofactor has a realizable canonical
extension. Moreover F has a proper safe OR cover, so the proposed hereditary
SCC criterion holds for every cofactor of F. This refutes that criterion's
sufficiency.

## The eight constraints

Write a partial Boolean cube with N for a free coordinate. At each cube
below mark the indicated coordinate P and leave its other free coordinates
N. D_F outputs N in all eight rows. The displayed coordinate is inessential
for both F and H, and both functions are nonconstant on every cube.

| Number | Cube (a,b,c,d,e,f) | Mark | F restricted | H restricted |
|---|---|---|---|---|
| 1 | (0,N,N,N,N,0) | e | cd | cd |
| 2 | (1,N,N,N,N,N) | b | f∨cd∨ce∨de | f∨cd∨de |
| 3 | (N,0,N,1,1,N) | f | a∨c | a∨c |
| 4 | (N,0,N,N,1,1) | d | a∨c | a∨c |
| 5 | (N,N,0,0,N,N) | e | af | af |
| 6 | (N,N,0,N,0,N) | d | af | af |
| 7 | (N,N,1,N,N,N) | b | d∨af∨ae∨ef | d∨af∨ef |
| 8 | (N,N,N,0,0,N) | c | af | af |

Call a pure term respectful when it avoids P at these eight marked inputs.
Every respectful term's Boolean function is independent of the marked
coordinate on each listed cube. Indeed essentiality there would force P
by the essential-source lower bound.

If a respectful term has Boolean function F or H, both children at its
root are respectful. On a nonconstant parent cube, an OR child cannot be
constantly 1 and an AND child cannot be constantly 0. Thus a P in either
child cannot be masked by the root operation. This applies to all eight
cubes because both F and H are nonconstant on them.

## Ownership transfers

A monotone Boolean function owns a set S when it is true at its
characteristic assignment. Monotonicity permits adding coordinates. The
independence constraints permit deleting the marked coordinate at any edge
inside its cube.

First, ownership of bdef forces ownership of every minterm of H. The
following deletion chains give the complete certificate; coordinates may
be added before a deletion.

    bdef -> cdef -> cde -> cd        [7,3,1]
    bdef -> adef -> ade              [2,3]
    bdef -> adef -> aef -> af        [2,4,5]
    bdef -> cdef -> cef              [7,4]

The bracketed numbers identify the cubes authorizing each deletion. For
example the first step adds c, then deletes b by cube 7.

Consequently a respectful Boolean child g≤F owning bdef satisfies H≤g≤F.
The only true assignments in F but not H are ace and abce. Cube 2 makes g
independent of b at those assignments. Thus g is exactly H or F. If g≤H,
it is exactly H.

For the AND case dualize the Boolean constraints (interchange fixed 0,1;
keep N and the marked coordinate). Write

    F* = abc∨acd∨ace∨ade∨acf∨adf∨cdf∨cef∨def,
    H* = F* ∨ df.

Under the dual eight constraints, ownership of cef forces all minterms of
F*. Here are paths giving every needed implication:

    cef -> acf                      [1*]
    cef -> abcf -> abc               [1*,3*]
    cef -> cdf                      [5*]
    cef -> def                      [8*]
    cef -> adef -> adf               [8*,1*]
    abc -> abde -> ade               [8*,7*]
    ade -> acd                      [5*]
    ade -> ace                      [6*]

Again additions are implicit before the authorized deletion. In addition,

    df -> cef                       [6*].

Therefore a dual respectful child below F* owning cef equals F*, and one
below H* owning df equals H*.

## Descent proof

Choose a respectful pure term with Boolean function in {F,H} having the
fewest gates. It is not a variable.

If its root is OR, one child owns bdef. The first transfer certificate makes
that child's Boolean function H or F. If its root is AND, apply the dual
certificate to its Boolean children: ownership of cef (for F*) or df (for
H*) makes one child's Boolean function equal to the parent's. In either
case the child is a smaller respectful term with Boolean function in
{F,H}, contradicting the choice.

So no respectful pure term has Boolean function F. In particular no pure
term realizes D_F. The general pure/full equivalence for canonical D
extensions excludes full terms as well.

## Why the hereditary SCC condition passes

The full canonical safe-child preorder of F has five SCCs and two source
SCCs. Its source-principal Boolean children are

    H = cd∨af∨ade∨cef∨bdef,
    K = ac(e∨df).

Both are strict safe children and H∨K=F. Equivalently, on every nonconstant
F cube, every marked coordinate inessential for F is inessential for H and
K. The standalone checker verifies these assertions directly on all cubes.
The dual graph has one SCC, which is harmless because the OR alternative
passes.

For every one-variable cofactor the checker supplies an actual pure term
and verifies its complete 1024-entry four-valued table. The terms are:

| Cofactor | Pure term (AND = inf; OR = sup) |
|---|---|
| a=0 | ((fb ed)∨c)∧(fe∨d) |
| a=1 | (d∨c)e∨dc∨f |
| b=0 | (((d∨c)e∨f)a)∨((fe∨d)c) |
| b=1 | ((d∨c)e(f∨a))∨fa∨dc |
| c=0 | ((fb ed)∨a)∧(ed∨f) |
| c=1 | (e∨a)f∨ea∨d |
| d=0 | (fa∨ec)∧(f∨a) |
| d=1 | ((ebf∨a)∧(f∨e))∨c |
| e=0 | fa∨dc |
| e=1 | (dbf∨c∨a)∧(f∨d∨ca) |
| f=0 | (ea∨dc)∧(d∨c) |
| f=1 | ((dbe∨c)∧(e∨d))∨a |

Juxtaposition in this table means iterated inf; use the fully parenthesized
strings in check.py when reproducing the checks. Further nonconstant
cofactors are realized by restricting these pure terms and simplifying
endpoint constants. Hence every proper cofactor satisfies the necessary
SCC alternative. There is no unverified enumeration premise in this claim.
