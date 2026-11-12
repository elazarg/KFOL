# Minimal core operations from arbitrary loopless matroids

Mathematical research, without Lean claims. Every finite loopless matroid
gives an explicit core operation whose source coefficients separate by
owner. The operation is the closed lower envelope of its singleton
profiles and is therefore globally minimal. Uniform matroids recover the
two-owner quota family, while general matroids give minimal operations
strictly below their profile maxima.

Fix finite owners I with K>=3, two distinguished owners written 0,1, and
a finite nonempty variable set V. Let M be a loopless matroid on V, with
closure cl and positive rank rho. Spanning means cl(S)=V. Write C(M) for
its cocircuits, the complements of its hyperplanes. All winner menus are
nonempty subsets of I.

## Basic matroid facts used in the construction

The following statements also fix the roles of bases and cocircuits.

1. S spans if and only if it meets every cocircuit. A nonspanning cl(S)
   extends to a hyperplane H, whose complementary cocircuit misses S.
   Conversely a set missing V\H is contained in the proper flat H.
2. j is outside cl(S) if and only if some cocircuit contains j and
   misses S. For the forward direction extend a basis of S together
   with j to a basis B, and take H=cl(B\{j}). It is a hyperplane
   containing S and missing j. The converse follows because such a
   hyperplane contains cl(S).
3. If U spans, L subseteq U, and j in U\cl(L), there is a basis B
   contained in U that extends a basis of L together with j. The
   hyperplane cl(B\{j}) then contains L and misses j.

Looplessness makes every j eligible in statement 2 with S empty. Thus
every variable belongs to a cocircuit. The cocircuit family is nonempty,
and each of its members is nonempty.

## A canonical cocircuit CNF word

For each cocircuit C, fold choice_1 over its variables. Fold choice_0
over the resulting clauses:

    F_M = FOLD_choice_0_(C in C(M))
                    (FOLD_choice_1_(i in C) x_i).         (1)

All folds are nonempty. Association and order within the folds do not
matter. This is a primitive core word with

    SUM_(C in C(M)) |C|

leaf occurrences. This counts the canonical construction, not its minimum
word size.

The singleton profiles of (1) are

    Phi_1(E) iff E spans M;
    Phi_0(E) iff V\E does not span M;
    Phi_r(E) iff E=V, for every r notin {0,1}.             (2)

At owner 1 each inner clause takes OR and the outer fold takes AND:
the profile says that E meets every cocircuit. At owner 0 the inner
clauses take AND and the outer fold takes OR: some cocircuit is contained
in E, equivalently its complement V\E is nonspanning. At any other
owner every gate takes AND, and every variable occurs by looplessness.
This proves (2) directly.

In particular the profiles are admissible. This also follows from their
duality: a spanning coalition cannot be disjoint from a coalition whose
complement is nonspanning; the other owners contribute V.

## Exact full source coefficients

For a source j define its canonical owner factors on sets not containing
j by

    D_(j,0)(E_0) iff V\E_0 spans M;
    D_(j,1)(E_1) iff j notin cl(E_1);
    D_(j,r)=true for r notin {0,1}.                        (3)

They are antitone and true at empty. For every observer k, the source
coefficient of (1) is exactly

    c_(j,k)=AND_(r!=k) D_(j,r)(E_r).                      (4)

To prove this, consider an occurrence of j in a clause C. If k!=1,
its inner choice_1 fold preserves k exactly when C has no input that
is the 1 singleton. This is C intersect E_1=empty. Taking the OR over
all j-containing clauses gives j outside cl(E_1), by matroid fact 2.
At k=1 these inner gates add no filter.

If k!=0, an outer choice_0 gate absorbs exactly when some other clause
is the 0 singleton, meaning that every input in that clause is 0.
The marked clause contains j={k} and therefore cannot be such a clause.
Thus the common outer filter is that no cocircuit is contained in E_0,
equivalently V\E_0 spans. It is independent of which occurrence of j
was marked. At k=0 the outer gates add no filter.

Combining these observations proves (4). Pure-0 and pure-1 source probes
recover the two factors in (3), so they are canonical coefficient factors.
The displayed CNF need not put this whole factor vector at one marked
occurrence: it combines separate cocircuit contributions by OR. A
different chosen-source-linear realization does attain the whole vector;
see [minimal-cnf-matroids.md](minimal-cnf-matroids.md).

## A closed formula on arbitrary winner menus

At a valuation w put

    L={i:w_i={1}},      U=V\{i:w_i={0}},
    W_k={i:k in w_i}.

Formula (4) and source reconstruction give

    0 in F_M(w) iff some j in W_0 lies outside cl(L);
    1 in F_M(w) iff U spans and W_1 is nonempty;
    k in F_M(w) iff U spans and some j in W_k lies
                    outside cl(L), for k notin {0,1}.    (5)

Equivalently,

    F_M(w)={0}                         if U is nonspanning;
           {1}                         if L spans;
           ({1} if W_1!=empty else empty)
             union UNION_(j notin cl(L)) w_j otherwise. (6)

The first two cases cannot conflict because L subseteq U. If U is
nonspanning, some element outside cl(U) belongs to V\U and hence is
the 0 singleton; it is also outside cl(L), proving that (5) gives
exactly {0}. If L spans, it is nonempty and (5) gives exactly {1}.
In the remaining case cl(L) is proper and the displayed union has a
nonempty input menu, so (6) is nonempty. Nonemptiness also follows
immediately from the actual word (1).

## Canonical prime guards are bases and cocircuits

An exclusion guard G_0 subseteq V\{j} guarantees D_(j,0) exactly when
G_0 union {j} spans. Its inclusion-minimal possibilities are

    G_0=B\{j}, for a basis B containing j.                (7)

Indeed extend {j} to a basis inside G_0 union {j}; minimality forces
equality with that basis minus j. Conversely deleting a basis element
destroys spanning.

An exclusion guard G_1 guarantees D_(j,1) exactly when
j is outside cl(V\(G_1 union {j})). By fact 2 its minimal possibilities
are

    G_1=C\{j}, for a cocircuit C containing j.            (8)

Minimality follows also from the cocircuit antichain property: distinct
hyperplanes cannot properly contain one another.

For observer 0 only (8) is needed; for observer 1 only (7) is needed;
for any other observer choose both independently. No further prime
exclusions occur. If one component were insufficient, a passive input
with atoms only of that owner would satisfy all the other exclusions
while falsifying (4). Conversely sufficiency of both components proves
sufficiency of their conjunction. Thus componentwise minimality is
exactly minimality of the whole guard.

If b_j counts bases containing j and c_j counts cocircuits containing
j, the numbers of canonical prime guards are c_j at observer 0, b_j
at observer 1, and b_j c_j at every other observer. These are exact
structural descriptions, without an occurrence graph.

## Equality with the closed profile lower envelope

Let R_Phi be the closed rainbow lower envelope from
[read-once-profile-minimum.md](read-once-profile-minimum.md). Its
certificate for winner k consists of positive coalitions A_r with

    empty != C=intersection_r A_r subseteq W_k;
    {i:w_i={r}} intersects intersection_(s!=r) A_s = empty
        for every rival owner r!=k.                       (9)

**Theorem.** F_M(w)=R_Phi(w) for the profiles (2), on every valuation.
Consequently F_M is globally minimal among core operations under
pointwise inclusion.

The general lower-bound lemma gives R_Phi subseteq F_M, since (1) is
core with profiles (2). For the reverse inclusion take a winner k
described by (5), and choose a supplying position j.

* At k=0, j is outside cl(L). Extend a basis of L together with j to
  a basis B of M.
* At k=1, U spans and j is in U. Extend {j} to a basis B contained
  in U; this is possible by looplessness.
* At any other k, U spans and j is in U\cl(L). Extend a basis of
  L together with j to a basis B contained in U.

In each case let H=cl(B\{j}), A_0=V\H, and A_1=B. Take A_r=V
for every other owner. These coalitions are positive: H is nonspanning
and B spans. Their common intersection is {j}.

Whenever k!=0, B is contained in U and therefore avoids all 0-singleton
positions, supplying that rival exclusion. Whenever k!=1, H contains L,
so A_0 avoids all 1-singleton positions. At any other rival owner the
intersection of the remaining coalitions is {j}; its menu contains k
and cannot be that rival's singleton. Thus (9) holds and forces k into
R_Phi.

Finally a core operation below F_M retains every positive profile bit
in (2). The same lower-bound lemma puts R_Phi=F_M below that operation,
forcing equality. This proves minimality without a finite-poset choice.

The tuple (2) is also maximal admissible. A new positive bit at owner 0
or 1 conflicts with its dual coalition at the other owner. For a new
positive coalition A!=V at another owner, choose j outside A, a basis
B containing j, and the cocircuit V\cl(B\{j}). Their intersection is
{j}; adding A destroys it, contradicting the rainbow condition.

## Greatest free completion and extension rigidity

The coefficient calculation remains valid when E_0 and E_1 are
independent flag sets and may overlap. At an occurrence in a j-containing
cocircuit C, the marked clause still cannot be all 0, since j is excluded
from E_0. Its full 0-factor is therefore the common spanning predicate
in (3). Its 1-factor is C intersect E_1=empty. Taking the OR over all
such C pulls out that common 0-factor and gives exactly (4), even on
the free flag domain.

Every other old realizer's full factors at j are bounded by (3), by
pure-owner source probes. Hence the cocircuit CNF attains the greatest
term-induced free source completion. It is also the greatest arbitrary
antitone completion: if one of the two factors is false, keep only that
owner's flags. The resulting smaller one-hot input already has a false
coefficient, forcing any antitone extension to be false at the original
input. This is a greatest-completion assertion, not a uniqueness or
least-completion assertion. The displayed free calculation combines
occurrences; the chosen-source-linear construction separately puts
both canonical factors at one occurrence.

**Corollary.** Every old-owner word realizing F_M has the same operation
on every unowned role extension.

For a finite extension, its old singleton profiles remain (2). Every
variable is essential in the spanning profile, since every nonloop
belongs to a basis; thus every realizer has full support V. The profiles
at new owners are unanimity, because no gate is owned by a new role.
The extended profile lower-envelope theorem above consequently puts
the extended F_M below every such word.

For the reverse inclusion, each occurrence's old-owner factors are
bounded by (3), as just proved. The same occurrence-path formulas work
with unowned winners: an unowned singleton can never be an old owner's
absorbing singleton. Thus the free coefficient bound puts every winner
of the extended word in the cocircuit-CNF operation. The two operations
are equal.

The assertion for infinite extensions follows bit by bit through the
finite old/fresh observer quotients, as in the
[quota extension argument](near-unanimity-size.md). Hence this gives
another extension-rigid family beyond primitive read-once operations.

## Uniform matroids and primitive read-once recognition

For the uniform rank-rho matroid on n variables, (2) has thresholds

    t_1=rho,      t_0=n-rho+1,

and unanimity at every other owner. These are precisely tight quotas
d_0=rho-1, d_1=n-rho, with the other quotas zero. Formula (6) therefore
recovers the two-owner family of [quota operations](near-unanimity-size.md).

For general matroids there is an exact read-once boundary.

**Theorem.** F_M is primitive read-once if and only if M is a direct
sum of rank-one matroids, equivalently its parallel classes are mutually
independent.

The minimal winning coalitions of Phi_1 are the bases. Two distinct
elements occur together in a basis exactly when they are not parallel:
an independent pair extends to a basis. Hence their cooccurrence graph
is complete multipartite, with the parallel classes as its parts.
Its maximal cliques choose one element from every parallel class.

The necessary read-once criterion from
[read-once-recognition.md](read-once-recognition.md) says that the bases
must be exactly these maximal cliques. Thus the rank equals the number
of parallel classes. Representatives of those classes are independent,
and parallel substitution shows that M is their rank-one direct sum.
Conversely, in such a direct sum the cocircuits are the parallel classes.
They partition V, so the canonical CNF (1) uses each variable once.
This includes rank one and the one-variable case.

## A nonuniform example below its profile maximum

Take a rank-two matroid on a,b,c,d with a,b parallel and c,d in two
other parallel classes. Its cocircuits are

    {c,d},     {a,b,d},     {a,b,c}.

The three clauses in (1) give its explicit core word. At the winner
valuation

    w_a={2},   w_b={1},   w_c={0},   w_d={0,1},

L={b}, cl(L)={a,b}, and U={a,b,d} spans. Formula (6) gives {0,1},
while the full input union is {0,1,2}. No singleton profile is true,
so the greatest completion of those profiles gives the latter union.
Thus the matroid operation is strictly below its profile maximum.

This family therefore goes beyond the regime where arbitrary sound
types can be realized by completing against an input-union maximum.
It gives an intrinsic source-separable normal form for every finite
loopless matroid, not merely a proposed candidate or a scalar observer.
The broader [closure construction](closure-core-operations.md) supplies
core existence without matroid exchange; the basis/cocircuit certificates
here additionally establish the exact lower envelope and minimality.
It does not settle whether analogous closed conditions characterize all
source-separable operations, or the full mixed guard problem.
