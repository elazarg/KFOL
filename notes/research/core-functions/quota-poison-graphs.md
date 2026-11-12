# A closed poison-graph criterion for binary tight quotas

Mathematical research, without Lean claims. For tight quotas taking values
zero and one, one observer's entire poison projection has a short exact
graph criterion: its zero edges form a disjoint union of outgoing stars,
opposite pairs, and isolated vertices. This is an unbounded mixed-pattern
characterization, not a characterization of all independent-status
patterns. Active old observers have a different, rigid poison projection.

## Setting and statement

Let I be a finite old owner set with at least three elements. Choose an
active subset H of size m>=2 and n=m+1 variables V. Give active owners quota
one and all other owners quota zero. The maximal admissible profile tuple is

    Phi_r(A)=[|A|>=n-1],     r in H;
    Phi_r(A)=[A=V],          r outside H.

The [tight-quota theorem](near-unanimity-size.md) identifies the unique
ordinary winner operation U with these profiles.

Fix an observer k that is either fresh or an inactive old owner. At the
poison pattern E^(i), put E_r={i} for every old r!=k; ignore the own flag
when k is old. For j!=i define

    q_(j,i)(S)=C_(j,k)^S(E^(i)).

Record a zero coefficient as the directed edge j->i. These are loop-free
directed graphs on V.

**Theorem.** A directed graph D is exactly the poison-zero record of a word
with profiles Phi if and only if:

1. No vertex has two incoming edges.
2. There is no directed path u->v->w with three distinct vertices.

Equivalently, each weak component is an outgoing star, an opposite pair,
or an isolated vertex. Both the imposed zeros and every other poison bit
are realized by one word.

When every old owner is active, this applies to fresh observers with
n=|I|+1. For an active old observer every poison coefficient is instead
forced to one, as proved below.

## Zero edges propagate coatom profiles

The same-owner separator lemma from
[one-pattern interpolation](free-pattern-interpolation.md) gives, for every
old owner r and every word S,

    q_(j,i)(S)=0 implies
        Phi_r^S(V\{i}) <= Phi_r^S(V\{j}).                 (1)

Take A=V\{i}, B=V\{j}, and the zero-source set {j}. Their difference is
{j}. The r-flag {i}, when relevant, lies in B. Every foreign nonobserver
flag misses A. All separator alternatives are false, proving (1).

Thus a zero edge j->i propagates a positive coatom bit at i backwards
to j. The same holds along directed paths.

## Necessity of the two graph prohibitions

Suppose u->w and v->w are zero edges with u,v,w distinct. Assign the
coatom V\{w} to two different active owners. Assign the remaining m-2=n-3
active owners the coatoms omitting the remaining vertices of
V\{u,v,w}, once each. Inactive owners receive V. All these coalitions are
positive, and their intersection is {u,v}.

At E^(w), every nonobserver blocker is excluded: after removing any one
coalition, another of the two w-omitting coatoms still excludes w.
Common-source-set persistence from
[free-profile-nonattainment.md](free-profile-nonattainment.md) forces
q_(u,w) OR q_(v,w)=1. This forbids two incoming zero edges.

Now suppose u->v and v->w are zero edges with u,v,w distinct. Choose
different active owners a,b. Consider the following reduced positive
profile premise:

    owners a,b: Phi_r(V\{u})=Phi_r(V\{v})=Phi_r(V\{w})=1;
    each other active owner: Phi_r(V\{ell_r})=1,

where the ell_r enumerate V\{u,v,w}. Every word with profiles Phi satisfies
this premise.

Assume a word satisfying this premise and both zero queries exists; choose
one with the fewest gates. At each queried poison head i in {v,w}, owners
a,b both have positive coatom V\{i}. Therefore every owner's singleton
profile at {i} is zero: choose one of a,b different from that owner and
use cross-owner common-source persistence. At the root, its own-owner OR
profile makes both child singleton profiles zero at these heads. Hence
both zero queries pass to both children. An old observer-owned root is
unfiltered and has the same conclusion.

At an a- or b-root choose a child with its positive coatom V\{w}.
Equation (1) along u->v->w recovers all three required coatom bits for
that owner. Every other owner's premise passes by AND. At a root owned
by another active owner choose a child with its one required positive
coatom; the other premises again pass by AND. At an inactive owner's
root all active premises pass to both children, so choose either child.
In every case there is a smaller word satisfying the same premise and
both zeros. No leaf satisfies the premise, because its coalitions together
exclude every vertex of V. This contradicts minimality and forbids the
two-edge path.

These conditions give the stated component description. A vertex with
an incoming and an outgoing edge lies in an opposite pair, since any
other predecessor-successor choice would be a forbidden path. Such a
pair admits no additional incident edge. Every other nontrivial component
has one source and only sink leaves, hence is an outgoing star.

## A word imposing every allowed zero graph

Call a word D-zero when it has every zero edge in D, with no requirement
yet on its other poison bits. D-zero words are closed under every owned
choice, since each individual zero-coefficient class is gate-closed.

It suffices to realize every selection of at most one positive coatom
per active owner by a D-zero word. Indeed, a minimal infeasible collection
of positive demands cannot repeat an owner: owned choice of two witnesses
omitting one repeated bit each repairs both bits by OR and retains every
other owner's bits by AND. Thus every minimal infeasible positive premise
is rainbow. Realizing all these rainbow premises gives a D-zero word
having every active coatom positive. Its profile tuple dominates Phi,
and maximal admissibility then makes its complete profiles exactly Phi.

Fix a rainbow premise, writing its selected coatom at owner r as
A_r=V\{w_r}; an unselected owner imposes only its top bit. There are at
most m=n-1 selected owner labels w_r. Some weak component C of D therefore
contains fewer selected owners than vertices. Count owners with
multiplicity when several choose the same excluded vertex.

If C is isolated, its vertex is unselected and its projection works.

If C is an opposite pair, it contains at most one selected owner. Fold
its two variables by that owner's choice, or by any active owner's
choice if there is no selected owner in C. The selected owner's OR
profile remains positive after excluding either one of the variables.
All other selected owners exclude a vertex outside C. This fold is
D-zero: at either internal poison, its absorbing owner's flag kills the
other source. Sources outside C are absent.

Suppose C is an outgoing star. If an unselected leaf exists, its
projection satisfies every selected coatom. It is D-zero because the
leaf has no outgoing edge. Otherwise every leaf is selected. Since C
has fewer selected owners than vertices, each leaf is selected by exactly
one owner, those owners are distinct, and the centre is unselected.
Start with the centre variable and attach each leaf by its selecting
owner's choice, in any order.

Every selected profile bit stays positive. At the one gate whose leaf
is excluded by that owner, its own OR preserves the current true bit;
every foreign gate has a leaf inside its coalition. Owners selecting
outside C see only labels in their coalition. At poison i in a leaf,
the source-centre occurrence is blocked by the attached leaf at its
selecting owner's gate. Every such owner is active and differs from k.
These are all the required zero edges in C; other components' sources
are absent. The spine is therefore D-zero and satisfies the premise.

This supplies a D-zero word with complete profiles Phi.

## Filling every nonedge

Let T be the D-zero profile realizer just constructed. For any nonedge
p->i, choose an auxiliary D-zero word u with q_(p,i)(u)=1 as follows.

If p has no outgoing edge, its projection works. Otherwise p is a star
centre or belongs to an opposite pair. Every other vertex of its component
is an outgoing neighbour of p, so the nonedge head i lies outside that
component. Fold the whole component by any active owner's choice. This
fold is D-zero, because an internal poison absorbs all other component
sources. At poison i no input has any positive flag, so the source-p
coefficient is one.

Reset u against T: start with u and attach T once by every old owner's
choice. The final profiles are exactly those of T. Both operands at every
step are D-zero, so all required zeros remain. At E^(i), every rival
singleton profile of T is zero, so the positive source-p contribution
from u survives every attachment. The resulting word has profiles Phi,
is D-zero, and has q_(p,i)=1.

Combine these witnesses for all nonedges by any fixed owned choice.
Their profiles remain Phi, and at every poison all the sibling singleton
profiles are zero. Thus each poison coefficient takes OR, retaining every
filled nonedge and every required zero. The exact graph D is realized.

The construction can use only active owners. All rainbow witnesses and
repairs already do so. Reset may also fold only over the m active owners:
an active profile receives OR once and AND at least once, restoring the
target bit. An inactive profile receives only AND with the target's
unanimity bit. That bit is zero at every proper coalition and one at V,
where every input word has profile one, so unanimity is restored as well.
The final fold may use a fixed active owner.

Consequently one such word realizes the same allowed zero graph
simultaneously at every inactive old and every fresh observer: none of
their owned gates occurs, and the only relevant poison flags are those
at active owners. This is a simultaneous construction for a common
record, not a classification of separately prescribed records at several
observers.

## Active observers and the proposed sink criterion

If k is an active old owner, every q_(j,i) is forced to one. Choose a
bijection r->b_r from active owners to V\{j}, with b_k=i. Set
A_r=V\{b_r} at active owners and A_r=V at inactive owners. Their common
intersection is {j}. For active r!=k the intersection of the other
coalitions is {j,b_r}, which misses poison i. For inactive r!=k that
intersection is {j}, also missing i. Free singleton-source persistence
therefore forces q_(j,i)=1. Ignoring the own-observer flag is essential
to this argument.

For a fresh or inactive observer, merely requiring that no vertex be
reachable from every other vertex is insufficient. With n>=4, take the
two-edge path 1->2->3 and leave all other vertices isolated. There is no
globally reachable vertex, but the path prohibition excludes this record.
The theorem gives the exact replacement, with two local graph conditions.

For two active owners and an inactive old observer, n=3 and the allowed
graphs are precisely the thirteen records in
[the ternary classification](free-pattern-amalgamation.md). The theorem
extends that closed poison-projection criterion to arbitrarily many active
owners. It does not assert that these poison bits determine the entire
free extension when n is larger than three.
