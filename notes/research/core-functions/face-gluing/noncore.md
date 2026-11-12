# A seven-row constancy law

Let the observer algebra have values `b,c,P,N`. Meet is minimum in
`b<P<N<c`, join is maximum in `b<N<P<c`, and observer union `⊔` has P
absorbing and `b⊔c=N`. Every full term below is constant-free and may use all
three operations.

Consider these seven input rows, with columns `A,B,C,D`:

| Row | A | B | C | D |
|---|---|---|---|---|
| E | c | c | b | b |
| M1 | N | c | P | b |
| M2 | c | N | b | P |
| M3 | N | P | c | b |
| M4 | P | N | b | c |
| M5 | N | b | c | P |
| M6 | b | N | P | c |

**Constancy law.** If a full term has no P output on `M1,...,M6`, then all
seven outputs, including the output on E, are equal to one element of
`{b,c,N}`.

The operation F in the README has output c at E and output N at every Mi,
so this law excludes a core realization. This proof does not assume that a
finite search enumerates any term clone.

## Boolean classification forced by the six marked cubes

For a pure meet/join term with Boolean function g, stable outputs satisfy:
`b` iff g is zero at the upper corner, and `c` iff g is one at the lower
corner. A P-marked coordinate essential for g on a cube forces output P:
choose an essential Boolean edge, evaluate on the chain `{b,P,c}`, and enlarge
the other free coordinates to their P/N inputs in observer-union order.
Both operations are monotone for that order and P is its top.

Thus absence of P at Mi makes its marked coordinate inessential. Write g(S)
for g at the characteristic vertex of S. The resulting equalities are:

| Row | Marked coordinate | Lower equality | Upper equality |
|---|---|---|---|
| M1 | C | g(B)=g(BC) | g(AB)=g(ABC) |
| M2 | D | g(A)=g(AD) | g(AB)=g(ABD) |
| M3 | B | g(C)=g(BC) | g(AC)=g(ABC) |
| M4 | A | g(D)=g(AD) | g(BD)=g(ABD) |
| M5 | D | g(C)=g(CD) | g(AC)=g(ACD) |
| M6 | C | g(D)=g(CD) | g(BD)=g(BCD) |

Consequently all seven values

```
g(A), g(B), g(C), g(D), g(AD), g(CD), g(BC)
```

are equal to one bit α, and all seven values

```
g(AB), g(AC), g(BD), g(ABC), g(ACD), g(ABD), g(BCD)
```

are equal to one bit β. Monotonicity gives `α≤β`. These are all the nonempty
proper Boolean vertices. Therefore g is one of

```
0, 1, AND(A,B,C,D), OR(A,B,C,D), f=AB∨AC∨BD.
```

For a constant-free pure term its endpoint values are zero and one, so the
constant cases are absent. This argument is uniform in the term: it is not a
truth-table search. The checker independently confirms the five-function list
among all 168 monotone Boolean functions.

## The P4 case is impossible for a safe pure term

Suppose a smallest pure term has Boolean function f and avoids P on all six
Mi. At a join root its child functions g,h are below f. A child owns a minterm
when it is true at the minterm's characteristic vertex. These implications
hold for each child:

| Ownership implication | Cube | Essential marked coordinate if it fails |
|---|---|---|
| AC→AB | M1 | C |
| BD→AB | M2 | D |
| AB→AC | M3 | B |
| AB→BD | M4 | A |

If an implication fails, the second minterm's characteristic vertex is a zero
of the child. Adding the marked coordinate contains the first minterm and
is a one. Both vertices lie in the indicated cube, so the child outputs P.
Its sibling cannot return c, since it is below f and f is zero at the lower
corner. The join would return P, contradicting safety.

Some child owns a minterm, hence all three, and therefore has Boolean function
f. It remains safe on all six Mi: each cube is nonconstant for f, so its
sibling cannot return c and mask an unwanted P. This contradicts minimality.

For a meet root, swap b,c and meet/join, leaving P,N fixed. The dual Boolean
function is `AB∨AD∨BC`, obtained from f by swapping C,D. The six Mi are closed
under the combined transformation. Apply the same join argument. The resulting
child has Boolean function f and remains safe on all six rows: the sibling is
above f, cannot return b at their upper corners, and cannot mask P. A variable
does not have Boolean function f. Thus the P4 case cannot occur.

## Pure and full constancy

The remaining pure Boolean functions are AND and OR of all four variables.
Every Mi has one fixed b and one fixed c. The AND case therefore returns b
on all six rows; the OR case returns c. At E their values are also b and c,
respectively. If constants were permitted, the two Boolean constant cases
would give the same conclusion. Hence every safe pure term is constant b or
constant c across these seven evaluations.

Meet and join separately distribute over observer union. Expand any full
term as a nonempty observer union of pure terms. If its outputs on the six
Mi omit P, each pure summand also omits P there, since P absorbs union. Each
summand is constant b or c on all seven rows. Their union is consequently
constant b, constant c, or constant N across all seven rows. This proves the
stated law.

The quotient of the full winner algebra for owner a sends every a-containing
menu to P, the two other singleton menus to b,c, and their union to N. Its
three choices induce meet, join, and observer union. The checker verifies
that F has quotient outputs `(c,N,N,N,N,N,N)` on the displayed matrix.
A core realizer would violate the constancy law, so F is not core.

[seven-relation.json](seven-relation.json) is an independent finite certificate
for the pure part of the law. It records 231 seven-tuples, contains all four
variable columns, and is closed under meet and join. The only recorded tuples
omitting P on the last six coordinates are the constant-b and constant-c
tuples. The checker verifies these facts directly; the same union-expansion
argument gives the full law. No completeness claim about the recorded states
is used.
