# Exact safety on cubes through one Boolean vertex

This is a mathematical result, without Lean claims. It gives a closed
sufficient regime for the relative-safety problem and one normal form for
each Boolean anchor. It does not characterize arbitrary jointly realizable
source guards.

Let B={b,c,N,P}. Meet is minimum in b<P<N<c, and join is maximum in
b<N<P<c. A pure term uses only meet and join. Endpoint constants b,c are
temporarily allowed; they simplify out of any nonconstant Boolean function.

A Boolean cube Q fixes some coordinates to 0 or 1 and leaves the others
free. Its marked row (Q,j), with j free, has P at j, N at the other free
coordinates, and b,c at the fixed coordinates. A term is safe at that row
when its output is not P. A budget is a family of marked rows.

## A support interpretation of marked rows

After fixing the endpoint coordinates of Q in a pure term, repeatedly use

    b meet x=b,    c meet x=x,
    b join x=x,    c join x=c.

The result is either an endpoint constant or a constant-free pure term on
the free coordinates. A constant-free positive Boolean formula is
nonconstant, since it takes 0 at the all-zero input and 1 at the all-one
input. Consequently the residual is constant exactly when its Boolean
function is constant on Q.

On {N,P}, both meet and join return P exactly when at least one input is
P. Hence, when the residual is nonconstant, its output on a marked row is
P exactly when the marked coordinate occurs in that residual formula.
With several marked coordinates the output is P exactly when at least one
of them occurs. In particular, a variable essential for the Boolean
function on Q forces P in every realizing formula.

Write D_f for the canonical essential-source extension of a monotone Boolean
function f: it returns the appropriate endpoint on a constant cube, and on
a nonconstant cube it returns P if some P-marked coordinate is essential
for f there, and N otherwise.

## The common-vertex theorem

**Theorem.** Suppose that every cube in a budget contains one Boolean
vertex v. A monotone Boolean function f has a pure realization safe on the
whole budget if and only if each marked coordinate is inessential for f
on its cube.

Equivalently, for each f and v there is one pure term T(f,v) whose Boolean
function is f and which agrees with D_f on every B-input whose Boolean
cube contains v. If f is nonconstant, the term can be constant-free.

The following construction proves the stronger equivalent assertion. It
also gives a formula whose residual on every cube containing v has exactly
the essential variables of the corresponding Boolean cofactor.

### Explicit construction

Identify a Boolean vertex with its set of 1-coordinates. For constant f use
the corresponding endpoint. Otherwise distinguish the two cases below.
All minimal sets are inclusion-minimal.

If f(v)=0, let U range over the minimal subsets of the zero-coordinates
outside v for which f(v union U)=1. Each U is nonempty. Put

    T(f,v) = JOIN_U ( MEET_(i in U) x_i
                         meet T(f|_(U=1), v) ).                 (1)

In the recursive call the coordinates of U are removed from the domain;
the displayed v is its restriction to the remaining coordinates. Its
value under the cofactor is 1.

If f(v)=1, let W range over the minimal subsets of v for which
f(v\W)=0. Each W is nonempty. Put

    T(f,v) = MEET_W ( JOIN_(i in W) x_i
                         join T(f|_(W=0), v\W) ).               (2)

Every recursive call removes at least one coordinate. The index families
are nonempty because a nonconstant monotone function takes 0 at the
all-zero vertex and 1 at the all-one vertex. Thus the construction
terminates without empty meets or joins.

### Boolean correctness

For (1), each summand is at most f: when its monomial is true, the
cofactor equals f at that input. Conversely, if f(x)=1, monotonicity gives
f(v union (x\v))=1. Some minimal U is contained in x\v, so the
corresponding summand equals 1. This proves (1) as a Boolean identity.

For (2), each clause is at least f. If f(x)=0, monotonicity gives
f(x intersect v)=0. Some minimal W is contained in v\x, and its clause
equals 0. This proves the dual identity.

### Exact residual support

Induct on the number of coordinates. Fix a cube Q containing v and a
coordinate j inessential for f on Q. A constant cofactor needs no argument.
In the case f(v)=0, examine a summand in (1).

* If some coordinate in U is fixed to 0 by Q, its monomial simplifies to
  b and masks the whole summand.
* Otherwise every coordinate in U is free: Q cannot fix one of them to 1,
  since v has 0 there. The marked coordinate j cannot belong to U. If it
  did, compare the two vertices v union (U\{j}) and v union U, both in Q.
  Minimality of U gives their f-values 0 and 1, contradicting
  inessentiality of j.
* Fixing U to 1 now leaves a cube containing the restricted anchor v. The
  cofactor is still independent of j on that cube. By induction its
  residual formula omits j; the monomial on U also omits j.

Every summand therefore omits j after endpoint simplification, and so does
their join. For (2), if a coordinate in W is fixed to 1, the clause is
masked by c. Otherwise W is free, and j cannot belong to W: the witnesses
v\W and v\(W\{j}) would show essentiality. Apply the same induction to
the zero-cofactor and combine the clauses.

Thus every inessential coordinate is absent from the residual. Every
essential coordinate must occur in any formula for that cofactor, so the
residual support is exact. The support interpretation above gives equality
with D_f, including inputs with several P coordinates. Conversely, any
essential marked coordinate forces P in every realization, proving the
necessity in the budget formulation.

The endpoint constants introduced by recursive cofactors can be simplified
using the four displayed laws. If f itself is nonconstant, the final result
cannot be an endpoint constant, leaving a constant-free pure term.

## A finite cofactor diagram and the lower envelope

The construction has a compact circuit presentation. Fix the original anchor
v. Every recursive call fixes a subset S of the original coordinates to their
values opposite v and leaves all others free. Thus a state is determined by S;
there are at most 2^n states. Each transition chooses a nonempty set U disjoint
from S. Across all states there are at most 3^n-2^n such pairs (S,U), since each
coordinate is in S, in U, or in neither, and U cannot be empty. Minimality and
the required polarity only remove pairs.

Cache the cofactor output at each state. Also share each monomial MEET_U x_i
and clause JOIN_U x_i; all these can be built with O(2^n) gates by removing one
coordinate at a time. Each transition contributes one gate combining its
monomial or clause with the child output. Aggregating the transitions at each
state uses no more than one further gate per transition. Consequently the
anchored normal form has an O(3^n)-gate circuit. Unfolding sharing gives the
pure formula proved above. This is a construction bound, independent of the
number of terms in the unrestricted operation clone.

The family of all anchored realizations has a second exact description.
For fixed f, every pure realization has the same stable endpoint outputs;
on a nonconstant cube it returns N or P, and it must return P whenever D_f
does. At a given input choose any vertex v of its cube. The anchored term
T(f,v) agrees with D_f there. It follows that

    D_f = pointwise minimum_(v in {0,1}^n) T(f,v),

where N<P on the nonconstant cubes; all terms already agree on the constant
cubes. This minimum is an ambient operation on functions, not an extra
bichain term constructor. The four-row obstruction shows why taking it need
not preserve term realizability. The conclusion is a finite lower-envelope
representation, not a global realization of D_f.

[Anchor selection is not complete](anchor-amalgamation.md): the eight-variable
function (AB OR CD) AND (EF OR GH) has a seven-gate exact core realization,
but none of its canonical anchored forms is globally exact. The proof also
shows that neutralizing an independent factor commutes with the construction.

## Pairwise cube intersection is sufficient

Boolean cubes have the Helly property with Helly number two. If a family
has no common vertex, some coordinate is fixed to 0 in one member and to
1 in another, so those two cubes are disjoint. Therefore pairwise
intersection of the underlying cubes is equivalent to a common vertex.

The theorem consequently applies to every pairwise-intersecting budget:
Boolean inessentiality is its entire safety criterion. It also applies to
every nested family, and to every family of lower faces through all-zero
or upper faces through all-one. In the last two cases ordinary prime DNF
or prime CNF already gives the required realization.

For example, with f=xy OR xz and anchor (x,y,z)=(0,1,0), (1) first factors
out x. Its cofactor y OR z is realized by the dual construction, giving
x meet (y join z). This one term is exact on every cube through that
anchor, even though the expanded DNF xy OR xz has an unwanted marked-z
occurrence on the cube y=1.

A common monotone chain is a weaker geometric condition, and is insufficient.
The eight cubes of the [six-variable obstruction](essential-extensions/six-variable-counterexample.md)
all meet the chain obtained by switching on d,e,f,a,c,b in that order. Cubes
1,5,6,8 contain the all-zero vertex; cube 2 meets the chain after a, cube 3
after e, cube 4 after f, and cube 7 after c. Their marked coordinates are
individually inessential, but the descent proof excludes a common safe formula.
Thus an ordering of compatible resolutions does not replace a common resolution.

The theorem does not amalgamate different anchors. Incompatible fixed
literals are necessary for a safety obstruction, and two disjoint cubes
can already obstruct simultaneous safety. The arbitrary-budget and full
joint source-guard problems remain unchanged.
