# A universal realizer with one occurrence of each full type

Mathematical research, without Lean claims. This settles the occurrence
multiplicity question for one binary owned choice. It also gives
nonisomorphic universal realizers even after each full type has been
represented exactly once. It does not prove a multiplicity bound for
arbitrary mixed operations.

Fix K>=3 owners I, one distinguished owner r, and the operation

    F(x,y)=x choice_r y.

Use the full occurrence factors from
[source-type-pruning.md](source-type-pruning.md). At an x occurrence,
its factor B_s is an antitone predicate on the single rival-s flag y_s,
and B_s(empty)=true. At observer k that occurrence contributes
AND_(s!=k) B_s. Here y_s means that the other variable is the s singleton;
the flags for different owners are independent in the free extension.

## The complete actual type family

**Theorem.** The actual x types of F are exactly

    B_r=NOT y_r;
    B_s is either true or NOT y_s, independently for s!=r.   (1)

The y types are symmetric. Thus there are 2^(K-1) actual types per
source and 2^K in total.

First these are the only possibilities. An antitone predicate on one
Boolean flag, true at empty, is either true or its negation. Moreover
choose an observer k!=r and the source probe x={k}, y={r}. F returns
{r}, so every actual x occurrence contributes false at that probe.
All owner factors except B_r are evaluated at empty and are true.
Consequently B_r is false at y_r=true and must equal NOT y_r.

The construction below realizes every choice of the remaining factors
simultaneously. It therefore proves actualness as well as the count;
the argument is not a term-enumeration certificate.

## The increasing-owner construction

Order the owners as s_0=r,s_1,...,s_(K-1). Define words U_i backwards.
At its root, U_i folds choice_(s_i) over the children

    x, y, and U_j for every j>i.                           (2)

The fold can be refined into binary gates in any order. Every occurrence
of U_j in (2) is expanded independently; the construction is an ordinary
word, not a circuit with shared subexpressions.

Each U_i realizes x choice_(s_i) y. If either x or y is the s_i
singleton, its explicit root child absorbs the fold. Otherwise none of
its children can be the s_i singleton: an atomic output of a core term
requires an input equal to that atom. The root therefore unions its
children. Its explicit x,y children already give x union y, and the
other children contribute only subsets of that union by conservativity.
In particular U_0 realizes F.

In the unrefined tree, a root-to-leaf path visits a strictly increasing
sequence of owner indices starting at 0, then ends at an x or y child.
Thus for each owner subset T containing r there is exactly one x leaf
and one y leaf whose ancestor-owner set is T.

At an ancestor with owner h, consider the factor contributed to a marked
x leaf. All other x occurrences are omitted from the h-singleton probe.
The sibling branches include the explicit y child of that ancestor.
Their combined h-profile is exactly y_h: this explicit child makes it
at least y_h, and every other sibling is a core word on x,y whose profile
at x_h=false is at most y_h. Hence the factor at this owner is NOT y_h.
Owners absent from the path contribute true. Refining a fold into binary
gates merely partitions these sibling branches; their combined filter
is the same.

The full x type at the path T is therefore

    B_h=NOT y_h for h in T, and B_h=true otherwise.         (3)

The same proof with x,y exchanged gives the y type. Since T ranges over
all subsets containing r, (3) is exactly (1), with no repetitions.

If L_i is the number of leaf occurrences of U_i, then

    L_i=2+SUM_(j>i) L_j=2^(K-i).

So U_0 has exactly 2^K leaves, one of each actual type. This is optimal
for a universal realizer containing all actual full types: every distinct
type needs at least one occurrence. The operation F itself of course has
its ordinary two-leaf realization; the exponential count concerns full
type saturation, not the minimum size of an F word.

## Full type saturation still does not determine the graph

The construction depends on the order of the foreign owners. This is
not merely a change in the order of children. Choose distinct r,s,t,
and compare the constructions whose orders begin

    r<s<t<remaining owners,
    r<t<s<remaining owners.

Identify the unique x occurrence of type T={r,s,t} and the unique y
occurrence of type U={r,t}, using (3). In the first construction their
paths go through different root children U_s and U_t, so their least
common ancestor has owner r. In the second they both enter U_t, and
the y occurrence is its explicit y child while the x occurrence enters
its U_s child. Their least common ancestor now has owner t.

Consequently the edge between these same two full types has different
colors in the corresponding colored graphs. Both graphs realize F,
contain every actual full type exactly once, and induce the canonical
greatest term-induced free extension described in
[free-polarization-extrema.md](free-polarization/free-polarization-extrema.md).
They are not isomorphic as variable-labeled owner-colored graphs:
such an isomorphism preserves the unique actual type of each vertex and
would have to preserve the displayed edge color.

Thus the universal full-type family is canonical, but even successful
one-per-type realization does not give a unique colored graph. A
canonical graph construction would require additional choices or
additional structural information; the full types alone do not force
its individual edge colors.
