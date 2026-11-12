# Constructive quota words and their greatest free source extension

Mathematical research, without Lean claims. Tight owner quotas admit explicit
primitive words, canonical maximal occurrence factors, and a term-induced
greatest independent-status extension. This is a higher-arity positive
family; it does not characterize arbitrary mixed source guards.

Fix finite owners I with K>=3 and n input variables V. Let d_r>=0 satisfy
SUM_r d_r=n-1, and put t_r=n-d_r. The
[quota theorem](near-unanimity-size.md) identifies the unique full core
operation with profiles Phi_r(E)=[|E|>=t_r]:

    U_d(w)={r} if at least t_r inputs are exactly {r};
           UNION_i w_i otherwise.                         (1)

We construct a word for (1) without using profile synthesis as its
existence step.

## A recursive word with a chosen source occurring once

Choose a pivot variable j. Start R_d(V) with the leaf x_j. For every
active owner q, meaning d_q>0, attach by choice_q the sibling

    R_(d-e_q)(V\{j}),                                     (2)

where e_q is the unit quota at q. Attach these siblings in any order.
Each recursive call has one fewer variable. At zero quota the variable
set is a singleton and the word is its projection. Pivots in the
recursive calls may be chosen arbitrarily.

**Theorem.** R_d(V) realizes U_d. Its chosen pivot occurs exactly once.

Induct on n. For an owner r and a coalition E, write alpha=[j in E] and
a=|E intersect (V\{j})|. If r is active, the sibling attached at its own
r-gate has r-profile

    H_r=[a>=t_r].

Indeed that child has arity n-1 and r-quota d_r-1. Every sibling at a
different active owner's gate has r-profile

    L_r=[a>=t_r-1],

because its r-quota is still d_r. At an r-gate the profile update is OR
with H_r; every other gate takes AND with L_r. Since H_r implies L_r,
if there is another active owner these updates in any order give

    H_r OR (alpha AND L_r)=[alpha+a>=t_r].                 (3)

If r is the only active owner, t_r=1 and L_r is true, so its sole update
alpha OR H_r is still (3).

If r is inactive, t_r=n and all gates are foreign. Each child has the
unanimity r-profile on the remaining n-1 variables, so the result is
unanimity on V. The singleton base case is immediate. Thus the word has
exactly the prescribed profiles. The matching proof of the quota theorem
then identifies all its winner values with (1).

The pivot leaf is present only at the start of its spine; none of the
sibling calls contains it. Hence it occurs once. Each variable can be
made linear in its own realizing word, even when the operation has no
simultaneous primitive read-once realization.

## Canonical source coefficients and prime guards

Fix source j and observer k. At its canonical source probe put x_j={k},
and give each other input either a rival singleton or the neutral menu
I\{k}. Let E_r be the positions assigned singleton r, for r!=k.
Only a rival-owner quorum can remove k. Therefore

    c_(j,k)(E)=AND_(r!=k) [|E_r|<t_r].                    (4)

The formula is valid on the ordinary one-hot passive domain. It also has
an antitone interpretation when the sets E_r are independent and may
overlap.

An exclusion guard specifies, for each rival owner r, a set G_r of
positions required not to be the r singleton. It is sufficient for (4)
exactly when |G_r|>=d_r for every r!=k. Sufficiency follows from

    |E_r|<=n-1-|G_r|<=n-1-d_r=t_r-1.

Conversely, if |G_r|<d_r, at least t_r positions lie outside G_r. Give
those positions singleton r and every other passive input the neutral
menu. This satisfies every exclusion in the guard, including exclusions
of other owners, but violates (4).

Consequently the canonical prime guards are exactly

    choose G_r subseteq V\{j} with |G_r|=d_r for every r!=k;
    require input i not to be {r} for every i in G_r.      (5)

There is no restriction against using the same position in several G_r.
The exact number of prime guards at (j,k) is

    PRODUCT_(r!=k) binomial(n-1,d_r).

Zero quotas contribute empty exclusion sets. This argument proves both
exhaustiveness and minimality without enumerating terms or guards.

## One greatest actual full type at each source

Use the full occurrence factors of
[source-type-pruning.md](source-type-pruning.md). A source-j occurrence
has one antitone factor B_r(E_r) per owner, true at empty. At observer k
its contribution is the conjunction of the factors for r!=k.

**Theorem.** At source j, the unique greatest actual full factor vector is

    B^max_r(E_r)=[|E_r|<t_r] for every r.                  (6)

First any actual factor B_r is bounded above by (6). Choose an observer
k!=r, and use a pure-r source probe, with r atoms at E_r and neutral
menus everywhere else. All factors other than B_r are evaluated at
empty and are true. Formula (4) therefore forces

    B_r(E_r) implies |E_r|<t_r.

For the converse use the pivot-j word (2). At an active r's spine node,
its sibling has r-profile [|E_r|>=t_r] and contains no j occurrence.
The marked pivot's r-factor is exactly its negation. There is only one
r-owned node on this spine. At an inactive r there is none, giving true;
this is also (6), since t_r=n and E_r has at most n-1 positions. Thus
the one pivot occurrence attains all the coordinatewise upper bounds
simultaneously.

This is actual occurrence data, not merely the greatest arbitrary
completion of separate observer coefficients.

## The greatest free completion is term-induced

Interpret the source flags independently, as in
[free-polarization-extrema.md](free-polarization/free-polarization-extrema.md).
Every term realizing U_d has free coefficient bounded by

    C^max_(j,k)(E)=AND_(r!=k) [|E_r|<t_r].                 (7)

Choose a pivot-j word for every j. Combine these words by a fold of any
one fixed primitive owned choice. Every operand realizes U_d, so
idempotence preserves the operation. The maximal marked types from (6)
also persist. At a new macro gate of owner h its sibling has profile
[|E_h|>=t_h], whose exclusion is already the marked factor (6); adding
it is redundant. Thus the combined word attains (7) at every source
and observer at once.

Hence (7) is the greatest term-induced free source extension. The
construction only needs the maximal type at each source; it does not
assert that this particular word contains every weaker actual type.

Moreover (7) is the greatest arbitrary antitone extension of the one-hot
coefficient. If (7) is false at an independent flag tuple, some E_r has
size at least t_r. Keeping only that owner's flags gives a one-hot tuple
below it where (4) is false. Antitonicity forces any extension to be
false at the original tuple. When (7) is true it is already the maximum
possible Boolean value. Thus the natural greatest free completion is
integrable for this quota family, although it fails for general core
operations.

## Word size and a shared circuit

Let L(d) count leaf occurrences in a pivot word. It depends only on the
quota vector:

    L(0)=1;
    L(d)=1+SUM_(q with d_q>0) L(d-e_q).                   (8)

The initial pivot contributes one leaf and the siblings contribute the
displayed recursive terms. If m quotas equal one and all others vanish,
this specializes to

    L_0=1,       L_m=1+m L_(m-1)
                     =m! SUM_(i=0)^m 1/i!.

In particular L_2=5, L_3=16, and L_4=65. These are exact integer formulas
and counts of this construction, not assertions of optimality. For m=K
the operation's profile quotient is a (K+1)-ary near-unanimity operation;
the lower bound in [near-unanimity-size.md](near-unanimity-size.md) gives
2^K+1 leaves for every primitive word at that arity.

For a shared circuit, fix an ordered variable list and always choose its
first remaining variable as pivot. A recursive state is then determined
by the residual quota vector e with 0<=e_r<=d_r. Its remaining variables
are the suffix of length 1+SUM_r e_r, so two paths reaching the same e
give the same subproblem.

There are PRODUCT_r(d_r+1) such states. A state e has one local gate per
positive e_r. Sharing each state once therefore gives a circuit with

    SUM_e #{r:e_r>0}
      =SUM_q d_q PRODUCT_(r!=q)(d_r+1)
      <=K PRODUCT_r(d_r+1)

primitive gates. With all K quotas one, this is K 2^(K-1) gates. These
counts concern one pivot-word circuit; the separate fold retaining all
sources' maximal types can be built from the corresponding pivot words.

The normal form supplies an explicit higher-arity realization and exact
canonical source data in a genuinely overlapping family. Its independent
owner-threshold structure is special; it does not remove the unresolved
joint compatibility problem for arbitrary prime guards.
