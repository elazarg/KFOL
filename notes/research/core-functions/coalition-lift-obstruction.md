# Why the naive coalition lift does not inherit the additive theorem

Mathematical research, without Lean claims. Replacing variables by canonical
coalitions makes arbitrary owner-closure triggers look unary, but it does
not preserve the additive theorem's colored idempotence or monochromatic
SCC structure. A genuine three-variable source-separable core operation
already supplies an obstruction. This rules out the naive lift, not every
incidence-sensitive hypergraph construction.

## A genuine core example with a mixed coalition SCC

On V={X,Y,Z}, take owners 0,1,2 and the five-leaf word

    F=(X choice_0 (X choice_1 Y))
           choice_0 (Y choice_1 Z).

This is the asymmetric source-separable CNF from
[the closure class](closure-core-operations.md). Its owner-1 closure has
closed sets

    empty, {X}, {Z}, {Y,Z}, V.

Its owner-0 closure is

    c_0(E)=V if X in E or {Y,Z} subseteq E;
           E otherwise,

and c_2 is the identity. In particular,

    c_0({X})=V,   c_1({Y})={Y,Z},   c_0({Y,Z})=V.

On the nonempty coalition nodes define an r-colored arrow S->T by
T subseteq c_r(S). The displayed genuine core closures give the cycle

    {X} --0--> {Y} --1--> {Y,Z} --0--> {X}.               (1)

Thus a mixed-color SCC contains the disjoint coalition labels {X} and
{Y}. The failure is not confined to a pair of overlapping opposite arcs.
It occurs despite the original closure family satisfying every necessary
colored, hereditary-profile, and neutral-omission law of a genuine core
operation.

More explicitly, make the lifted closures additive on coalition nodes:

    c_hat_r(A)=UNION_(S in A) (nonempty subsets of c_r(S)).

Color the virtual node {Y} by 1 and {Y,Z} by 0. Starting with the single
virtual seed {Y}, the first colored closure contains exactly the nodes
{Y},{Z},{Y,Z}. The second adds {X}, through the 0-colored node {Y,Z}.
Hence the lifted colored closure is not idempotent.

This virtual coloring is impossible on the actual inputs: {Y} being the
1 atom requires Y=1, whereas {Y,Z} being the 0 atom requires Y=Z=0.
Treating coalition nodes independently has introduced an inconsistent
status assignment.

## Coherent coalition vectors are not gate-closed

There is a separate direct algebraic obstruction. Map an input valuation
v to its coalition unions

    nu(v)_S=UNION_(i in S) v_i.

Choose distinct owners r,s and two input positions x,y. Take

    v=({r},{s}),     w=({s},{r}).

Coordinatewise choice_r gives ({r},{r}), whose {x,y}-coalition union is
{r}. But both nu(v) and nu(w) have {r,s} at that coalition, and their
choice_r there is still {r,s}. Thus nu does not commute with the gates.

Indeed its image is not even a subalgebra when singleton coalitions are
retained. The coordinatewise product has {r} at both singleton nodes
but {r,s} at their union node; no coherent coalition valuation has these
three values. Equivalently, the conjunction identity for atomic flags,

    p_r(S union T)=p_r(S) AND p_r(T),

is not preserved by the owner-r OR gate when S and T are split between
the two operands.

Consequently the mixed-gate profile relation theorem cannot simply be
applied to independent virtual coalition coordinates. A successful lift
must retain how overlapping coalitions share and duplicate underlying
inputs. Neither ordinary colored SCCs nor merely allowing overlap on
opposite arcs supplies that missing composition data. No general
coalition-based realization criterion is excluded by these examples.
