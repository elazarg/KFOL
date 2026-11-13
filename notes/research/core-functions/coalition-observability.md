# Exactly which coalition powers descend to winner semantics

Written mathematical proof, not a Lean assertion. The report statement is
`context:prop:observable-coalitions` in `sections/appendix-contexts.tex`.

For a coalition Q, let E_Q^t(H) say it can force a terminal variable in H.
This reads a Q-owned gate as OR and every other gate as AND. For fixed
K>=3, this observation is determined by the full core operation exactly
when Q or its complement has at most one member.

For a singleton {r} it is the r-profile. For its complement it is the
Boolean dual of that profile. Empty/full coalitions give AND/OR over
support, which is also determined by the operation.

If a,b belong to Q and c,d to its complement, use

    U_(a,b;c)(x,y)=(x choice_a y) choice_c (x choice_b y).

All such U with three distinct owners induce set union. Q reads
U_(a,b;c) as OR and U_(a,c;d) as AND. Thus even the full guard table
cannot determine this coalition's power without a chosen tree.

Conversely, effectivity for every coalition does not determine the full
core operation. The two words

    x choice_a (y choice_b z),
    (x choice_a y) choice_b (x choice_a z)

have identical coalition powers by Boolean distributivity, but at
x={c}, y={a}, z={b} return {b,c} and {a,b,c}. At K=3 all coalition
powers are just the singleton profiles and their duals. At K>=4 the
two observations are incomparable.

Recording basic powers (the exact outcome range of a fixed strategy)
does not repair canonicity. For distinct a,b, put t=x choice_a y.
The words t and t choice_b t have equal winner operations by
idempotence. Coalition {a} has exact ranges {x},{y} in t, while the
second tree also allows {x,y}: its two copies use independent choices.
This uses the basic-power definition in
[van Benthem--Bezhanishvili--Enqvist, Definition 7](https://staff.fnwi.uva.nl/n.bezhanishvili/Papers/tark-proceedings-2017.pdf).

## Consequence for the game-form route

Abdou's rectangular-and-tight recognition concerns free perfect-information
presentations, whose terminal outcomes are distinct. Repeated variable
labels can destroy rectangularity on the original outcome set: the tree

    y choice_A (x choice_B y)

has normal game-form matrix [[y,y],[x,y]], whose y-fiber is not a rectangle.
Splitting the two y occurrences restores a free presentation but introduces
the auxiliary occurrence refinement we still need to eliminate. Ordinary
coalition powers cannot select that refinement, by the theorem above.

The precise equivalence relation in Abdou's 1998 full text was not inspected;
only its publisher abstract and the author's later definition of free games
were checked. No theorem from that paper is used in our proof.

Sources: [Abdou 1998, publisher abstract](https://doi.org/10.1287/moor.23.3.553);
[Abdou's later discussion of free games and rectangular fibers](https://citeseerx.ist.psu.edu/document?doi=2ae2a2dbb2eae357c1b24225b5f483f24cd29f5c&repid=rep1&type=pdf).
