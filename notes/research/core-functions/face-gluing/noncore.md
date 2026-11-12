# A twelve-probe proof that F is not core

All positive realizability claims are checked by evaluating explicit terms.
Nonrealizability has the analytic proof below and an independent finite
pure-term relation certificate. Neither assumes a search enumerates the clone.

Observe owner `a`. The quotient sends every menu containing `a` to `P`, the
other-owner singleton menus to `b,c`, and their union to `N`. Its operations
are minimum in `b<P<N<c`, maximum in `b<N<P<c`, and observer union `⊔`, where
`P` absorbs, `b⊔c=N`, and `N` absorbs `b,c`. Call them meet, join, and union.
The three owned choices induce these three operations respectively.

The quotient of `F` is the canonical essential-source extension `D_f` for
`f=AB∨AC∨BD`. The checker verifies this on the full table. A core realization
of `F` would therefore give an observer-algebra term realizing `D_f`.
In fact the following twelve probes already exclude such a term:

* Require output `c` at the characteristic vertices of `AB,AC,BD`.
* Require output `b` at the characteristic vertices of `CD,BC,AD`.
* Forbid output `P` on the six mixed rows in
  [trace-obstruction.json](trace-obstruction.json).

The first three vertices are exactly the minimal true assignments of `f`,
and the next three its maximal false assignments. Every true assignment
contains a minimal true one; every false assignment is contained in a
maximal false one. Thus Boolean monotonicity uniquely forces `f`. The checker
also verifies this uniqueness among all 168 monotone four-variable Boolean
functions. Each of the six mixed rows is a nonconstant cube for `f` with
`D_f=N`.

Every pure meet/join formula with Boolean function `g` has two properties:

1. It returns `b` exactly when `g` is zero at the cube's upper corner, and `c`
   exactly when `g` is one at its lower corner.
2. A P-marked coordinate essential for `g` on that cube forces output `P`.
   Choose a witnessing Boolean edge and evaluate on the chain `{b,P,c}`.
   Enlarge the other free coordinates to their `P/N` inputs in observer-union
   order. Both operations are monotone in that order and `P` is its top, so
   the output remains `P`.

Suppose a smallest pure formula has Boolean function `f` and avoids P on all
six mixed rows. If its root is join, its Boolean child functions `g,h` are
below `f`. Say that a child *owns* a minterm when it is true at the minterm's
characteristic vertex. These implications hold for either child:

| Ownership implication | Partial input `(A,B,C,D)` | Marked coordinate |
|---|---|---|
| `AC→AB` | `(N,c,P,b)` | `C` |
| `BD→AB` | `(c,N,b,P)` | `D` |
| `AB→AC` | `(N,P,c,b)` | `B` |
| `AB→BD` | `(P,N,b,c)` | `A` |

If an implication fails, its second minterm's characteristic vertex is a
zero of the child; turning on the marked coordinate contains the first
minterm and is a one. Both vertices lie in the displayed cube. Thus the
marked coordinate is essential for the child, which returns `P` by property 2.
The sibling cannot return `c`, since it is below `f` and `f` is zero at the
lower corner. The root returns `P`, contradicting safety. The checker verifies
the four vertex/cube facts directly.

A child owns at least one minterm, hence all three, so its Boolean function
is `f`. It also avoids P on every one of the six mixed rows: at any such row,
`f` is zero at the lower corner, so the sibling cannot return `c` and mask a
P. That gives a smaller formula with the same properties, a contradiction.

A meet root is excluded by duality. Swap `b,c` and meet/join, leaving `P,N`
fixed. The dual Boolean function is `AB∨AD∨BC`, obtained from `f` by swapping
`C,D`. The four dual images of the displayed rows are among the six rows of
the certificate. Apply the same ownership argument. The resulting child has
Boolean function `f` and remains safe on all six rows: the sibling is above
`f`, cannot return `b` at their upper corners, and so cannot mask a P.
A variable does not have Boolean function `f`. This excludes all pure formulas.

Meet and join separately distribute over observer union. Expand a full term
as a nonempty observer union of pure formulas. A stable endpoint on each of
the six Boolean probes forces every summand to agree there. Monotonicity
forces each summand's Boolean function to be `f`. Since P absorbs observer
union, every summand avoids P on all six mixed rows. This contradicts the
pure-formula argument. Consequently no full observer term, and hence no core
winner-valued term, satisfies these twelve probes.

The independent [pure-relation.json](pure-relation.json) certificate records
603 twelve-tuples. It contains all four variable columns, is closed under
meet and join, and excludes the target `(c,c,c,b,b,b,N,N,N,N,N,N)`. The checker
verifies those facts directly. For a pure formula whose six endpoint outputs
force `f`, property 1 makes every mixed output either `P` or `N`; forbidding P
there forces the excluded target. Observer-union expansion gives the same
full-term conclusion. Closure of this explicit finite relation suffices;
there is no claim that it is a complete enumeration of term operations.
