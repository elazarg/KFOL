# An actual maximal type can require a repeated source

Mathematical research, without Lean claims. A canonical maximal full
occurrence type can be actual while having no minorant realization in
which its source occurs once. Thus maximal-type attainment does not imply
a source-linear insertion theorem, even for genuine source-separable
operations.

## The three-head family

Fix a finite owner set I with K>=3 and distinct owners r_i,r_j,r_k.
Let H={h_i,h_j,h_k} be three heads and A a disjoint finite set of
unconditional anchors. Choose nonempty contexts L_i,L_j,L_k subseteq A
such that

    L_i intersect (L_j union L_k)=empty,
    L_j intersect L_k != empty.                     (1)

For each l in {i,j,k}, write

    P_l=(H\{h_l}) union L_l.

The owner-r_l closure adds h_l exactly when P_l is contained in its
argument. All other owner closures are identities. Their separable
reconstruction is

    F(w)=UNION_(a in A) w_a
          union UNION_l (w_(h_l) unless every input
                         in P_l is the r_l singleton).    (2)

The [complete-head circuit theorem](complete-head-circuits.md) proves
that F is core for every such I. It also proves that the canonical
maximal full vector at the isolated head h_i is actual:

    D_(r_i)(E)=NOT[P_i subseteq E];
    D_s(E)=true for every s!=r_i.                   (3)

The shared context between j and k supplies the auxiliary circuit
that protects a marked h_i occurrence. That construction uses additional
occurrences of h_i.

## No source-linear minorant attains the vector

**Theorem.** There is no core word S with S<=F, with exactly one
occurrence of h_i, whose marked h_i occurrence has full vector (3).

Suppose such a word exists. Every sibling along the marked path omits
h_i. If a path gate has a foreign owner s!=r_i, assign the s singleton
to every passive variable. Its sibling then evaluates to the s
singleton by idempotence, making the marked s-factor false. This
contradicts D_s=true. Consequently every gate along that path is owned
by r_i. Orienting the marked subtree on the left, the word has the
spine form

    S=(...(h_i choice_(r_i) G_1)
                      choice_(r_i) G_2)... choice_(r_i) G_m,   (4)

where no G_l contains h_i. Write psi_l for its r_i-singleton profile.
The exact marked factor in (4) gives

    OR_l psi_l(E)=[P_i subseteq E].                 (5)

Thus every psi_l is bounded above by the conjunction on P_i, and at
least one sibling G has psi_G(P_i)=true.

Put N=I\{r_i}. Define two valuations u_j,u_k. At u_l put I on h_l,
the r_l singleton on P_l, and N on every remaining input. Neither
valuation has an r_i-singleton input. In (2) its only input containing
r_i is h_l, and that head is suppressed, so F(u_l) omits r_i.
No subword can evaluate to the r_i singleton without an r_i-singleton
input. Therefore every spine gate in (4) acts as union at both rows.
The bound S<=F forces every sibling, including G, to satisfy

    r_i notin G(u_j),
    r_i notin G(u_k).                               (6)

Apply the profile-passage lemma in the proof of
[feedback elimination](three-owner-exchange.md), with observing owner
r_i and the two queries

    A_profile=P_i;
    X_j={h_j}, query coalition P_j;
    X_k={h_k}, query coalition P_k.

Condition (1) gives the required covers

    P_i intersect P_j={h_k} subseteq X_k,
    P_i intersect P_k={h_j} subseteq X_j.            (7)

That word-level lemma uses only a positive r_i-profile at A_profile,
the omission budgets (6), and these differently colored covers. The
closure-spanning hypothesis in the subsequent closure formulation of
feedback elimination is not needed here. It yields

    psi_G(P_i\{h_j,h_k})=psi_G(L_i)=true.            (8)

But (5) bounds psi_G by conjunction of P_i, which is false on L_i.
This contradiction proves the theorem.

## Consequences

Every F realizer repeats h_i. Indeed, if a realizer had only one
h_i occurrence, a pure-r source probe would identify that occurrence's
r-factor with the canonical pure port of F, for each owner r: there
is no other h_i occurrence to supply the probe's observer winner.
Its full vector would therefore be (3), contradicting the theorem.

In particular (3) is an actual maximal full type, but every realization
of it below F repeats its source label. The smallest instance of this
construction has five variables:

    L_i={a}, L_j=L_k={b}.

This concerns an entire full occurrence vector. It does not exclude
source-linear minorants that supply individual winner queries, such as
the short safe spines used to construct F.
