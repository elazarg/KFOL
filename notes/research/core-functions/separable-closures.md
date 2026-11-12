# Source separation and canonical colored closures

Mathematical research, without Lean claims. Owner-shadow incidence is
exactly a closure-operator law. Every core operation has these canonical
owner closures, whether or not its mixed source coefficients separate.
For a source-separable operation they give a direct colored-closure
formula. The compatibility conditions making an arbitrary such system
core remain unresolved.

Fix finite owners I with K>=3 and a finite nonempty variable set V.
For core operations restrict to their essential support, so every
variable is active. A pure-r source coefficient D_(j,r)(E) uses source
j={k}, for some k!=r, r atoms at E subseteq V\{j}, and neutral
I\{k} elsewhere. For a core term it is independent of the chosen
observer k!=r: only its r-owned ancestor filters can be nontrivial.

Thus every owner r gives a family of antitone predicates D_(j,r),
with D_(j,r)(empty)=true. The following one-owner result applies to
any such normalized family, without assuming it arose from a term.

## Owner-shadow is precisely closure idempotence

Suppress r in the notation and define

    c(E)=E union {j notin E:D_j(E)=false}.                 (1)

This map is extensive and monotone, and c(empty)=empty. Monotonicity
follows directly from antitonicity of the D_j.

A prime avoidance guard G for D_j is an inclusion-minimal set of
variables, excluding j, whose avoidance by the atomic set guarantees
D_j. Equivalently D_j(V\(G union {j})) is true, and no proper subset
of G has this property. Put H=G union {j}. Owner-shadow incidence is

    D_i(V\H)=true for every i in H,
        for every prime guard G of every D_j.             (2)

**Theorem.** Equation (2) holds if and only if (1) is idempotent.
Consequently normalized owner-shadow families are exactly loopless
closure operators, with ports

    D_j(E)=[j notin c(E)] for j notin E.                  (3)

Suppose (2) holds and j is outside c(E). Choose a prime guard G for
D_j disjoint from E; one exists because D_j(E) is true. Its hyperedge
H=G union {j} is disjoint from E. By (2) and antitonicity, D_i(E) is
true for every i in H. Thus H is disjoint from c(E). The same guard G
still witnesses D_j(c(E)), proving j is outside c(c(E)). This gives
c(c(E)) subseteq c(E), and extensivity gives equality.

Conversely suppose c is a closure, and take prime G,H as above. Write
E=V\H. Then j is outside c(E). If some i in G belonged to c(E),
closure idempotence would give c(E union {i})=c(E). Hence
D_j(E union {i}) would remain true, saying that G\{i} was already
a sufficient guard. This contradicts primeness. Therefore H is
disjoint from c(E), which is exactly (2).

The operator determines every port by (3), so this correspondence is
one-to-one. The distinction from general closure operators with loops
is exactly the normalization D_j(empty)=true.

## Why every core pure-owner section is a closure

There are two concrete ways to obtain (2) for actual terms.

For the clique proof, a prime pure-r guard is the guard of an actual
occurrence: primes of the OR of occurrence factors are minimal guards
from those factors. Its hyperedge H is the label set of a maximal
r-clique through that occurrence. For any i in H, the i-labeled vertex
of the same clique survives a pure-r source probe with r atoms exactly
outside H. All other owner filters are empty. Thus D_(i,r)(V\H) is
true, giving (2).

An independent one-owner trace avoids occurrence graphs. Replace every
foreign-owned gate by derived union. This preserves the r-singleton
profile and all pure-r source coefficients: the profile update at
a foreign gate is AND, while its pure-r source update is OR, exactly
as for union. The resulting word uses only choice_r and union.
Distributing choice_r over union puts it into a union of r-folds over
nonempty hyperedges H. Its ports are

    D_(j,r)(E) iff some H containing j is disjoint from E.

Define the interior

    I_r(T)=UNION {H:H subseteq T}.

It is contractive, monotone and idempotent. Its complement-dual
c_r(E)=V\I_r(V\E) is the closure (1). Full variable support makes
I_r(V)=V and c_r(empty)=empty.

The same interior is the constant-r coloring section of
[colored-interiors.md](colored-interiors.md):

    C_r(J)=V\c_r(V\J).                                  (4)

Thus the closure law is also the complement-dual of the previously
proved constant-color outcast law.

At a profile probe with atomic set E, the trace's r-fold is the
r singleton exactly when its hyperedge meets E. Their union is r
exactly when every hyperedge meets E. Moreover an actual term's
r-singleton output depends only on its r-atomic input positions, by
the profile gate recursion. Therefore every core operation, including
a nonseparable one, satisfies the full factorization

    F(w)={r} iff c_r({i:w_i={r}})=V.                      (5)

The canonical owner closures refine the singleton profiles by retaining
their nonspanning closed sets and individual source ports.

## The source-separable reconstruction

Call a source-reconstructing candidate source-separable when it has
common normalized factors D_(j,r), independent of the observer, with

    c_(j,k)(E)=AND_(r!=k) D_(j,r)(E_r).                   (6)

Assume these factors obey owner-shadow, and use their closures c_r.
For a winner valuation w let E_r={i:w_i={r}} and W_k={i:k in w_i}.
Then (6) becomes the closed formula

    k in F(w) iff some j in W_k is outside
                          UNION_(r!=k) c_r(E_r).          (7)

Conversely a family of loopless closures defines (7), possibly with
empty values. At a canonical source probe only the marked source
contains k, so its coefficients are exactly (6), and its pure-owner
ports recover the original closures. If it is everywhere nonempty,
its pure-r singleton probes recover the spanning predicates c_r(E)=V.
This probe identity does not imply the full factorization (5) for an
arbitrary synthetic candidate. The forward implication c_r(E_r)=V
implies F(w)={r} holds by (7) and nonemptiness, but the converse can
fail on mixed atomic patterns. Full atomic-profile factorization must
therefore be imposed separately in a proposed core criterion.

This eliminates owner-shadow's hyperedge vocabulary in this regime.
It does not make arbitrary colored closure families realizable.

## Exact behavior on one atomic-status fiber

Fix disjoint atomic sets E_r, with J the remaining ambiguous positions.
Write C_r=c_r(E_r), and define

    T_j={r:j in C_r};
    A={r:E_r\UNION_(s!=r) C_s is nonempty};
    Q=V\UNION_r C_r.

Extensivity makes Q a subset of J. Formula (7) is exactly

    F(w)=A union UNION_(j in Q) w_j
          union {r:some j in J has T_j={r} and r in w_j}. (8)

An atomic source can supply only its own owner and contributes precisely
the set A. An ambiguous source with T_j empty contributes its whole
menu; with T_j={r} it contributes only the possible r; with two or
more owners in T_j it contributes nothing. This proves (8).

The canonical constant part in a whole-menu selector representation
would be exactly A: assign all ambiguous positions I\{k} to test
each k. For this fixed fiber the functional selector law holds exactly
when either |I\A|<=1, or every singly shadowed owner r outside A is
absent. Indeed outside A a Q-position supplies every winner coordinate,
whereas a position with T_j={r} supplies just that coordinate. If A
misses only r, this partial contribution equals whole-menu selection
modulo A, since A already contains every other winner.

There is a stronger necessary condition for an actual source-separable
core operation:

    T_j={r}, j in J implies r in A.                       (9)

For if r were absent from A, choose the j menu to contain r and every
other ambiguous menu to omit r. Equation (8) makes j the only ambiguous
source of the new r. In an actual term's whole-menu status selector, j
must therefore be selected. Some occurrence of it survives every atomic
absorption on that fiber. Each of its owner factors is true at the
corresponding E_s, so all the canonical pure-owner ports D_(j,s)(E_s)
are true. This means T_j is empty, a contradiction.

This argument uses the common source attribution of an actual word,
not just a functional representation on one fiber. When A misses one
winner, that distinction matters: the functional selector law alone
allows the masked partial contribution described above.

Under (9) all the last contributions in (8) are already contained in
A, giving the simpler actual-core form A union UNION_(j in Q) w_j.

## Side-effect constraints and an insufficient weak criterion

For an ambiguous source j in J, the canonical factor vector's failed
owner factors at this status pattern are exactly T_j. A possible stronger
all-source colored-closure condition is

    F(w) intersects T_j != empty whenever T_j!=empty.     (10)

It includes atomic sources: if j is the r singleton, extensivity puts
its own color r in T_j as well. That case is additional to the
ambiguous-source failed-factor interpretation and cannot simply be
dropped. Equation (8) makes this condition explicit in closure data.
The canonical vector need not already have been realized at one
occurrence, so the actual-type side-effect theorem cannot simply be
applied to it. Necessity of (10) for arbitrary source-separable core
operations is not proved here; neither is sufficiency of (10), full
atomic-profile factorization, profile admissibility and (9).

Closure laws, admissible profiles and everywhere-nonempty output alone
are insufficient. Take owners 0,1,2 and variables X,Y,Z,W. Let c_0
have parallel block {X,Y} and free elements Z,W; c_1 have parallel
block {Y,Z} and free X,W; and c_2 have parallel block {Z,X} and free
Y,W. These are loopless matroid closures. Each spanning predicate
requires W, so the pure-probe profile tuple has a common source and
is admissible.
Since W is free in every closure, its entire menu always survives in
(7), proving nonemptiness.

Nevertheless set X={2},Y={0},Z={1}. Substituting W=I\{k} gives
F=I\{k}: the three atomic inputs are each blocked by a rival closure,
and only W survives. The winnerwise neutral residual after deleting W
is therefore empty at this assignment. On all-ambiguous remaining inputs
it is their input union, so it is not the zero residual. This contradicts
the core neutral-elimination theorem.

The example also fails the stronger tests above. At Y={0},Z={1},W={1}
and X ambiguous, (8) gives

    F={1} union ({0} if 0 in X else empty).

The X source has T_X={0}, outside A={1}. This is not a whole-menu
selector and violates (10) when X={1,2}. It is therefore not a
counterexample to a criterion that includes those stronger side effects.
It also has a spurious singleton: with X={1,2} its output is {1},
but c_1({Z,W})={Y,Z,W} is proper, violating (5).

The constructive two-owner class
[closure-core-operations.md](closure-core-operations.md) realizes any
one loopless closure coupled to its associated spanning test. The
remaining question is a closed compatibility law for general colored
closures, and beyond them for nonseparable mixed guards.
