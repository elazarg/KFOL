# Cograph recognition for canonical quadratic essential-source extensions

Let B={b,c,N,P}; inf is min in b<P<N<c and sup is max in b<N<P<c.
Union is the observer operation. For a monotone nonconstant Boolean f, let
D_f be its essential-source extension: at v∈B^V take the cube Q with fixed
b/c coordinates and free N/P coordinates. Return b/c when f is constant
0/1 on Q; otherwise P iff some P-coordinate is essential on Q, and N
otherwise.

## Theorem

For every finite simple graph G with at least one edge, put

    f_G(x)= OR_{ij∈E(G)} (x_i AND x_j).

Then the following are equivalent:

1. D_{f_G} is a constant-free pure bichain term operation.
2. D_{f_G} is a constant-free full (inf,sup,union) term operation.
3. G has no induced P4.
4. G is a cograph (built from singleton graphs by disjoint union and complete
   join).

Isolated vertices are permitted and ignored by f_G. The edgeless graph is
excluded because its extension is the constant b operation, which no
constant-free idempotent term can realize.

The equivalence of 3 and 4 is the standard cograph characterization. The
new content is its equivalence to 1 and 2 for the canonical D extension.
In particular, full union adds no realizability within this family.

## Construction from a cotree

For every nonempty vertex set W, let U_W be any iterated sup of its variables.
This realizes D_{OR_W}, since every free variable of a nonconstant OR is
essential.

Construct T_G recursively; omit a summand for an edgeless child instead of
introducing a constant.

* At a disjoint-union node with child graphs G_1,...,G_k, take sup of all
  nonempty T_{G_i}.
* At a complete-join node on disjoint vertex sets V_1,...,V_k, take

      T_G = sup( T_{G_i} for nonempty edge children i,
                 inf(U_{V_i}, U_{V_j}) for i<j ).

All joins here are bichain sup, all meets bichain inf. Every graph with an
edge has a nonempty list of summands, so this is genuine constant-free
syntax. Its Boolean endpoint function is f_G by the graph decomposition.

## A general fact about D extensions

Every pure bichain term t with Boolean endpoint function f has the stable
outputs prescribed by f: b iff f(upper corner)=0 and c iff
f(lower corner)=1. Moreover a marked coordinate essential for f on Q forces
t(v)=P. Proof: take an essential Boolean edge, assign that coordinate P and
all other free coordinates to its witness Boolean values; on {b,P,c} the
term evaluates by ordinary three-chain lattice semantics, hence gives P.
Enlarge the other input values in observer-union order; both basic
operations are monotone and P is its top, so the result stays P.

Thus to prove T_G=D_{f_G} it suffices to exclude an unwanted P output.

## Complete-join step: no spurious marked source

Let v be an input and L the vertices fixed to c, U those not fixed to b.
Assume f_G is not constantly 1, so L is an independent set. Suppose a
summand of T_G outputs P. Its Boolean function is below f_G, and it is not
masked by a c summand exactly when the complete result remains nonstable.
We show that a marked source responsible for that summand is essential for
f_G on [L,U].

First consider an internal summand T_{G_i}. By induction it supplies a
marked vertex p∈V_i essential for f_{G_i}.

* If no other block contains a vertex of L, choose all other blocks empty.
  The essentiality witness inside V_i is then also a witness for G.
* If another block contains a vertex of L, independence of L forces
  L∩V_i=∅ and forces all fixed vertices to lie in that other block. The
  baseline completion L has no edge. Turning p on creates a cross edge
  to that fixed vertex. So p is essential for G.

Next consider a cross summand inf(U_{V_i},U_{V_j}). The two blocks are
disjoint, so this term is exactly D_{OR_{V_i} AND OR_{V_j}}: disjoint
AND/OR composition commutes with D. A marked source p lies in one block,
say V_i; essentiality implies L∩V_i=∅ and that some vertex of V_j is
available in U.

* If any vertex of L is outside V_i, the baseline L is independent and
  adding p creates a cross edge to it.
* If L is empty, choose an available q∈V_j. The baseline {q} has no edge,
  and adding p creates one.

These two cases exhaust the possibilities, because L∩V_i=∅. Hence p is
essential for G in either case.

A sup of summands can output P only when one summand does and no summand
outputs c. The argument therefore excludes every unwanted P. Together with
the general fact above, it proves the complete-join step. The disjoint-union
step is easier: D commutes with disjoint OR composition, with a constantly
true child masking every other source. This completes the cotree induction.

## Induced-P4 necessity, including full union

If G contains an induced P4 on W, fix every vertex outside W to b. The
restricted canonical operation is exactly D_{f_{P4}}; isolated ignored
coordinates can also be removed. A hypothetical full term would give a
full polynomial in W with the sole constant b.

Distribute inf/sup over observer union, obtaining a nonempty union of pure
bichain polynomials. Endpoint laws simplify each pure summand to b or a
constant-free pure term. No constant-b summand can occur, since evaluating
all variables of W at c would then give N (or P) rather than the required c.
On every Boolean input, a union is a stable endpoint only when every summand
has that same endpoint. Consequently every remaining pure summand has
Boolean function f_{P4}.

Because P absorbs observer union, each summand's P trace lies below the
trace of D_{f_{P4}}. The general essential-source fact forces the opposite
inclusion. Hence any summand would realize D_{f_{P4}}, contradicting the
four-row pure-root obstruction in p4-base-obstruction.md. This
excludes full as well as pure realizability.

## Checks and scope

The executable cograph-essential-extension.py constructs the cotree formula
and compares its complete four-valued table to D_{f_G} independently:

    n=2:   1 nonempty-edge labeled cograph; all 4^2 inputs checked
    n=3:   7; all 4^3 inputs checked
    n=4:  51; all 4^4 inputs checked
    n=5: 471; all 4^5 inputs checked

These counts include isolated vertices and omit the edgeless graph. They
are corroboration; the cotree argument is the proof. No repository files or
manuscript were edited. This characterizes the canonical quadratic family,
not arbitrary bichain functions.
