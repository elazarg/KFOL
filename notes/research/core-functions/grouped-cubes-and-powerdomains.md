# Grouped ambiguity and the failure of powerdomain transfer

Mathematical research, without Lean claims. The aim remains a closed intrinsic
condition on jointly realizable guards. The results below identify information
that two possible approaches lose; they do not supply that condition.

Write B={b,c,N,P}, with meet the minimum in b<P<N<c, join the maximum in
b<N<P<c, and observer union merging b,c to N and absorbing P.

## Safe Boolean functions and their exact implication preorder

A marked cube z=(Q,j) fixes some Boolean inputs, leaves the rest free, and
marks one free coordinate j. Its B-input has P at j and N at its other free
coordinates. Let l_z,u_z be its Boolean lower and upper corners. A pure
meet/join formula is safe on a budget Z when it avoids P on every marked row.

Let L_Z consist of the Boolean functions of safe formulas, temporarily allowing
the two endpoint constants. It is a bounded sublattice of the monotone Boolean
functions: two P-free inputs to either operation cannot produce P. Constants
in a formula simplify away unless its function is itself constant, so adding
them does not change nonconstant realizability.

For Boolean vertices x,y, define

    x P_Z y  iff  g(x) ≤ g(y) for every g in L_Z.

L_Z consists exactly of the upper sets of this preorder. Indeed the
intersection of all members containing x belongs to L_Z and is the principal
upper set of x; every upper set is a union of these. Finiteness makes both
operations available inside L_Z.
Let M(Z) be the set of coordinates marked somewhere in Z, and put

    x F_M y  iff  x\M ⊆ y\M.

Then the following is exact:

    P_empty = Boolean inclusion;
    P_Z = F_M(Z) ∩ intersection_(z in Z)
              TC(P_(Z\{z}) union {u_z -> l_z}).                (1)

Proof. L_Z is generated as a lattice by its safe projections and the families

    L_(Z\{z}) ∩ {g : g(l_z)=g(u_z)}.                          (2)

Every generator is safe: equality of the endpoint values makes the formula's
output stable throughout that cube. Conversely, induct on a safe formula.
If both children are safe, use their lattice combination. Otherwise a child
has value P at some z. The safe root must mask it by the absorbing endpoint
b at meet or c at join. Thus the parent's Boolean function is constant on
Q_z, and the parent itself witnesses its membership in (2).

Safe projections are exactly those outside M(Z), giving F_M(Z). Intersecting
a function lattice with cube constancy adds the endpoint equality to its
implication preorder. Generating a lattice from families intersects their
preorders. These observations give (1).

This replaces searches over unknown Boolean child functions by canonical
pairs, but still has subset recursion. It is not the requested closed answer.

### Edgewise information cannot determine exact safety

Replace each marked cube (Q,j) by all of its j-edges, regarded as separately
marked one-dimensional cubes. Call this budget E(Z). The two budgets impose
exactly the same Boolean inessentiality equations. They have the same initial
implication preorder, the same marked coordinates, the same safe projections,
and the same edge data on every Boolean cofactor.

But for E(Z), every Boolean-admissible g has a safe realization: choose any
pure formula for g. Each marked edge is a constant cube for g, so stable
endpoint semantics forces b or c there, independently of the formula.
Consequently L_E(Z) is the entire initial upper-set lattice.

For the six grouped rows in [the gluing obstruction](face-gluing/noncore.md),
g=AB OR AC OR BD obeys every initial inessentiality equation but has no safe
pure realization. Thus L_Z is strictly smaller than L_E(Z).

Any exact criterion must retain which parallel edges belong to one common
nonconstant cube. No completion from the initial preorder and its cofactor
restrictions alone can be sufficient.

## The exact Smyth powerdomain identification

Let D={bottom,b,c} have the flat information order bottom<b,c. Its nonempty
upper sets are

    rho(P)=D, rho(N)={b,c}, rho(b)={b}, rho(c)={c}.

Under rho, bichain meet and join are upward-closed pointwise lifts of parallel
Boolean AND and OR. Observer union is set union. This is the finite Smyth
powerdomain presentation: reverse inclusion is its order and union its binary
meet. The general presentation is in Abramsky--Jung, *Domain Theory*,
[Theorem 6.2.14](https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf).

For any monotone Boolean f, let f_D be its ordinary three-valued lattice
polynomial on the truth chain b<bottom<c. Then its essential-source extension
satisfies

    rho(D_f(v)) = up { f_D(x) : x_i in rho(v_i) }.             (3)

Indeed, a bottom output occurs precisely when f varies on some Boolean
resolution of the P-marked coordinates. Such variation is equivalent to
essentiality of at least one of those coordinates. If no bottom occurs, a
nonconstant cube yields both endpoints, and a constant cube yields its unique
endpoint. These are exactly the defining cases of D_f.

Equation (3) does not transport term definability. Lifting fails to preserve
nonlinear substitution: flat absorption gives x meet (x join y)=x, whereas in
B at x=N,y=P the two sides are P and N. Repeated independent occurrences are
precisely where this transfer loses information.

### Even all naturally lifted flat invariants are insufficient

For R subset D^m, define its correlated powerdomain lift by

    Q(R) = { (up pi_i U)_i : empty != U subset R }.

If a monotone flat operation f preserves R, its pointwise Smyth lift preserves
Q(R). Given witness sets U_1,...,U_k, apply f coordinatewise to their Cartesian
product. The resulting nonempty set lies in R; monotonicity identifies its
upward-closed coordinate projections with the lifted outputs. Also Q(R) is
closed under observer union, witnessed by union of witness sets.

It follows that all flat parallel-AND/OR invariant relations yield bichain
invariants this way. Nevertheless every D_f preserves every one of them,
because f_D is already a flat lattice term. The nonterm P4 extension passes
the entire family. Thus lifting all base invariants does not recover the
missing nonlinear compatibility.

## What the literal Sieber schema characterizes here

For A subset B subset {1,...,m}, define the native bottom-or-equality relation

    S^A,B(x) iff (some i in A has x_i=P)
                    or (all coordinates indexed by B are equal).

This is the indexed shape of Sieber's presequentiality relations; see
Pucella--Panangaden, *On the Expressive Power of First-Order Boolean Functions
in PCF*, [Definition 3.1](https://arxiv.org/pdf/cs/0405085).
Here P is treated as bottom on the four-element flat order P<b,c,N.

An operation preserves every bichain-invariant intersection of such native
relations if and only if it is monotone for this four-element flat order.

The forward implication uses just S^{ {1},{1,2} }, which is exactly that order.
It is bichain invariant: a non-P meet or join output involving a P input is
fixed by a stable absorbing endpoint; observer union is non-P only when both
inputs are non-P. Thus all three operations are flat-monotone.
For the reverse implication, every S relation preserves constants and every
strict case selector: a selector returns P on selector input P, and otherwise
returns one designated argument according to whether its selector is b,c,N.
If the output has no P on A, the selector column is constant on B; the same
argument column is therefore used throughout B, where its own S condition
forces equality. The case A empty follows from equality directly. Hence
intersections preserve these operations as well.

Together with parallel AND/OR, these selectors and constants define every
finite flat-monotone operation f. For each minimal input trace u with non-P
output, test its non-P coordinates with strict equality tests and parallel
AND. Parallel-OR the tests for each output value. At an input where f returns
v, its v-test is true; tests for different outputs are false, since compatible
traces with different outputs would contradict flat monotonicity. Sequential
case inspection therefore returns v. Where f returns P it returns P, either
on an unresolved test or after all tests fail. The constant case is immediate.
Every bichain-invariant intersection of S relations consequently preserves f.

Each D_f is flat-monotone. If its output is non-P, every P-marked coordinate
is inessential on that cube; replacing it by N or either endpoint leaves the
output unchanged. Thus D_P4 also passes this whole native indexed/intersection
family. The proposed schema captures monotonicity, not the finer core clone.

The remaining problem is the same as before: a closed intrinsic condition on
the complete grouped guard data. The order recurrence and the powerdomain
identification explain two aspects of it, but neither removes that gap.
