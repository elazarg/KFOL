# Intrinsic recognition of primitive read-once operations

Mathematical research, without Lean claims. This gives a closed recognition
criterion for primitive read-once operations from their profiles and the
operation table. Its graphs have the original variables as vertices and
are computed canonically from the profiles: no occurrence graph or proposed
tree is an input. It does not characterize general overlapping input reuse.

Fix finite owners I with K>=3 and a finite nonempty variable support S.
Let A be the nonempty winner sets. A primitive read-once word uses only
owned choices and has each variable of S exactly once at its leaves.
Derived union is not a primitive node, since its implementation repeats
inputs. A candidate on a larger variable set can first be restricted to
its essential support S; this note treats F:A^S->A directly.

## The canonical graphs and the criterion

For each owner r define its profile by the usual probe:

    Phi_r(E) iff F(v)={r}, where
        v_i={r} for i in E, and v_i=I\{r} otherwise.

Require each Phi_r to be monotone, false at empty, and true at S. Let M_r
be its inclusion-minimal winning coalitions. Define a simple graph Q_r
on S by

    ij is an edge of Q_r iff some M in M_r contains i,j,
        for distinct i,j.

Let G_r be the complement of Q_r on pairs of distinct vertices. The
following are entirely canonical conditions on the given profiles:

1. M_r is exactly the family of maximal cliques of Q_r, for each r.
2. Every pair of distinct vertices belongs to exactly one G_r.
3. The resulting edge coloring has no triangle with three distinct colors.
4. Each G_r has no induced four-vertex path.

A singleton is a clique; in particular a one-vertex graph has its singleton
as its unique maximal clique. An unused owner may have G_r empty.

For completeness recall the closed profile lower envelope. At a winner
valuation w put W_k={i:k in w_i} and E_r={i:w_i={r}}. Let R_Phi(w)
contain k exactly when there are coalitions A_r subseteq S, one per owner,
such that

    Phi_r(A_r)=true for every r;
    empty != C=intersection_r A_r subseteq W_k;
    E_r intersects intersection_(s!=r) A_s = empty
        for every r!=k.                                    (1)

**Recognition theorem.** F is a primitive read-once operation with support
S if and only if its profiles satisfy the four graph conditions above,
are monotone and normalized as stated, and

    F(w)=R_Phi(w) for every w.                              (2)

When these conditions hold, the reduced owner-colored cotree is unique up
to ordering its children. Binary refinement of a node into gates of its
own owner does not change the operation. Thus its graph reconstruction
provides a realizing word but is not an additional witness in the criterion.

## Read-once profiles give precisely these graphs

At an r-owned node the r-profile is the OR of its child profiles. At any
other owner's node it is their AND. The child supports are disjoint.
For monotone functions on disjoint supports:

* Minimal winning coalitions of an OR are the minimal coalitions from
  either child. Their cooccurrence graph is disjoint union.
* Minimal winning coalitions of an AND are all unions of one minimal
  coalition from each child. Their cooccurrence graph is complete join.

At a leaf the sole coalition is its singleton. Induction therefore proves
that M_r consists exactly of the maximal cliques of Q_r. It also gives

    ij is an edge of Q_r
        iff the owner of their least common ancestor is not r.    (3)

Consequently the graphs G_r partition all variable pairs by their least
common ancestor's owner. No triangle has three colors: its three pairwise
least common ancestors reduce to at most two nodes.

For a fixed r, the graph G_r is complete join across an r-owned node and
disjoint union across another owner's node. These operations preserve the
absence of an induced four-vertex path. For disjoint union this follows
from the path's connectedness. For complete join use that the complement
of a four-vertex path is again a four-vertex path. Thus all four graph
conditions are necessary. Every variable is essential in every profile,
as is also immediate from the disjoint OR/AND recursion.

## Reconstructing a cotree without an occurrence witness

Here is an elementary decomposition proof of the graph implication used
for sufficiency.

**Lemma 1.** A complete edge-colored graph without a rainbow triangle has
a connected color graph.

For at least two vertices, choose a monochromatic connected component C
of largest possible cardinality, over all colors. Let its color be r.
If a vertex v lies outside C, none of its edges to C has color r. Along
an r-colored path in C, consecutive edges from v must have the same
color: otherwise the corresponding triangle is rainbow. Hence all edges
from v to C have one color s!=r. They form an s-colored connected set
C union {v}, contradicting maximality. Thus C is the entire vertex set.

**Lemma 2.** A connected graph on at least two vertices with no induced
four-vertex path has disconnected complement.

Choose a vertex v, write N for its neighbors, and M for its nonneighbors
other than v. If M is empty, v is isolated in the complement. Otherwise
let C range over the connected components of the induced graph on M.
Each vertex u in N is adjacent to either all of C or none: a transition
along a path in C would give an induced path v,u,x,y. Write A_C subseteq N
for the vertices adjacent to C. It is nonempty by connectedness.

Every u in A_C is adjacent to every w in N\A_C. Otherwise x,u,v,w is
an induced four-vertex path for x in C. The sets A_C are nested: if A_C
and A_D were incomparable, choose u in A_C\A_D and w in A_D\A_C.
They are adjacent by the previous observation, and x,u,w,y is an induced
four-vertex path for x in C and y in D.

Choose a smallest A_C, denoted A. It is nonempty and contained in every
A_D. Consequently it is complete to M, to N\A, and to v. Its complement
is also nonempty because it contains v. There are no complement edges
across this partition, proving the lemma.

Now suppose the four canonical graph conditions hold. If |S|>=2, Lemma 1
supplies a color r with G_r connected. Lemma 2 makes Q_r disconnected.
Use its connected components S_1,...,S_t, with t>=2, as the root blocks.
Every cross-block edge has color r. Restrict the coloring to each block
and repeat; all conditions concerning triangles and induced paths are
hereditary. Singletons terminate the construction. This gives an
owner-colored cotree realizing exactly the original edge colors.

The root color is unique. Once Q_r has at least two components, every
other color has edges only within those components and is disconnected.
Its root blocks are exactly the canonical components of Q_r. Recursive
uniqueness follows. Also an internal child cannot have owner r: within
a non-singleton Q_r component, the complement color graph G_r is
disconnected by Lemma 2 applied to the connected P4-free Q_r there.
Thus this construction gives the reduced cotree, with adjacent internal
nodes of different owners.

For the last observation Q_r is P4-free because its complement G_r is:
the four-vertex path is self-complementary. This argument is independent
of the supplied profiles once the edge coloring has been formed.

## Sufficiency and the complete winner operation

Implement each internal cotree node by a fold of its owner's choice over
its children. Owned choice is associative and commutative: if any operand
is the owner's singleton, the fold returns it; otherwise it returns the
union. Binary refinement therefore gives a primitive read-once word T.

By (3), T's r-profile has cooccurrence graph Q_r, and its minimal winning
coalitions are precisely the maximal cliques of Q_r. Condition 1 makes
these exactly M_r. Monotone Boolean profiles are determined by their
minimal winning coalitions, so T has the given profiles Phi.

The [read-once least-profile theorem](read-once-profile-minimum.md) says
that T(w) is exactly (1). Equation (2) therefore gives F=T. Conversely
that theorem supplies (2) for every primitive read-once T, completing the
recognition proof. Under the graph conditions, (1) is automatically
nonempty because the cotree provides this actual term operation.

If S={j}, every Q_r has one vertex and condition 1 says M_r={{j}}.
All the graphs G_r are empty and conditions 2--4 are vacuous. Formula (1)
is exactly the input menu w_j, so the criterion correctly returns the
projection. No branching node or exceptional singleton convention is
needed.

This is a positive structural theorem for a restricted regime. The
[prime obstructions](prime-obstructions.md) and the general source-guard
problem concern essential overlapping reuse; they are not decided by
this cotree criterion.
