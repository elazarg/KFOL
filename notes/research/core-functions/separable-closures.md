# Source separation and canonical colored closures

Mathematical research, without Lean claims. Owner-shadow incidence is
exactly a closure-operator law. Every core operation has these canonical
owner closures, whether or not its mixed source coefficients separate.
For a source-separable operation they give a direct colored-closure
formula. The compatibility conditions making an arbitrary such system
core remain unresolved.

They also have a semantic definition: c_r(E) consists exactly of E
and the variables made inessential by fixing E to {r}. The
[cofactor-dependence theorem](cofactor-dependence-closures.md) proves
this for every core operation, without source separation, and obtains
the closure laws from a general fact about restrictions of functions.

For additive closures, the
[colored-preorder characterization](additive-closure-characterization.md)
settles this compatibility problem by two closed arrow laws and an
explicit source-linear-minorant construction. The results below apply
also to nonadditive closures, where that criterion is unavailable.

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

If r were absent from A, give every other ambiguous position I\{r}
and compare j=I with j=I\{r}. All statuses stay fixed. Equation (8)
makes r present only at the first valuation, since j is its sole
ambiguous source. But j in c_r(E_r) means that fixing E_r to {r}
makes j inessential in the entire function, by the cofactor-dependence
theorem. The two outputs must agree, a contradiction.

This uses full functional independence in a monochromatic cofactor,
not just a whole-menu representation on one status fiber. The latter
alone allows the masked partial contribution described above.

Under (9) all the last contributions in (8) are already contained in
A, giving the simpler actual-core form A union UNION_(j in Q) w_j.

## Admissible spanning profiles already guarantee nonemptiness

**Colorful-cover lemma.** Let the maps c_r be monotone and extensive.
Assume their spanning predicates Phi_r(E)=[c_r(E)=V] satisfy the
rainbow common-source condition. At every partial coloring, A or Q
is nonempty. In particular their source formula (7) is nonempty-valued.

Suppose A=Q=empty. For every position j choose a capturing owner r(j)
with j in c_(r(j))(E_(r(j))) and j outside E_(r(j)). Such an owner
exists: an atomic position has a different capturing owner because
its own color is absent from A, while an ambiguous position has some
capturing owner because Q is empty. Put

    B_r={j:r(j)=r},    A_r=V\B_r.

The B_r partition V and are disjoint from their respective E_r.
Thus E_r subseteq A_r. Monotonicity and extensivity give

    c_r(A_r) contains A_r union c_r(E_r)
                    contains A_r union B_r=V.

Every A_r spans, but their intersection is empty. This contradicts
rainbow common-source admissibility. Therefore A or Q is nonempty.
An atomic survivor in A or a whole menu at a position in Q supplies
a nonempty subset of (7). Neither source attribution nor a realizing
word is needed for this lemma.

## Omission independence recovers the full atomic-profile law

**Lemma.** For loopless closures, if the source formula (7) is nonempty
and satisfies omission independence, its singleton predicates are
exactly Phi_r(E_r)=[c_r(E_r)=V].

If c_r(E_r)=V, every potential non-r source is captured by r, so
nonemptiness forces F(w)={r}. Conversely suppose F(w)={r}. Successively
for each k!=r replace every k-containing input by I. Omission independence
keeps the output {r} at every step. The atomic r-set stays E_r;
every position outside E_r becomes I, and every other atomic set
becomes empty. If some j were outside c_r(E_r), it would be outside
E_r and hence have menu I at the end. Looplessness removes every
other owner closure there. This free j would supply all of I in (7),
contradicting the unchanged singleton output.

Consequently exact atomic profiles need not be imposed separately on a
candidate already satisfying admissible spanning profiles and omission
independence: the colorful-cover lemma supplies nonemptiness, and this
lemma supplies the exact profile law.

## Hereditary common-source admissibility

The owner closures of every genuine core operation satisfy a stronger
condition, whether or not its mixed source coefficients separate.
For each nonempty U subseteq V the restricted closures are

    c_r^U(E)=c_r(E) intersect U, for E subseteq U.

Their spanning predicates are admissible singleton profiles. To see
this, take the winnerwise neutral residual on U. Neutral elimination
makes it zero or a core word on U. It is nonzero and has full support:
on all ambiguous inputs each primitive gate takes union, and an
isolated marked source at any position in U still supplies its winner.
Its pure-owner ports are exactly the original ports with the deleted
variables neutral, hence its closures are the displayed restrictions.
The singleton-profile classification now gives their admissibility.

Equivalently, there is a direct hereditary common-source law with no
separate U parameter:

    U=UNION_r A_r is nonempty and U subseteq c_r(A_r)
    for every r imply INTERSECTION_r A_r is nonempty.    (H)

For necessity apply the restricted rainbow law on U. Conversely,
any failure on a larger U can be restricted to the nonempty union
of its witnessing coalitions; all those coalitions still span that
union. Thus (H) is exactly hereditary spanning-profile admissibility.

By the colorful-cover lemma it ensures that every nonempty neutral
restriction of the source formula is nonempty. Even when strengthened
by colored outcast, hereditary span-outcast and hereditary omission,
it does not ensure joint realizability. The prime obstruction in
[separable-closure-counterexample.md](separable-closure-counterexample.md)
satisfies all these conditions.

## All-source side effects

For an ambiguous source j in J, the canonical factor vector's failed
owner factors at this status pattern are exactly T_j. For an atomic
source, use the same definition T_j={r:j in c_r(E_r)}, including its
own color. There is a necessary all-source colored-closure law:

    F(w) intersects T_j != empty whenever T_j!=empty.     (10)

**Theorem.** Every source-separable core operation satisfies (10),
including at atomic source positions. No assumption that the canonical
full factor vector is an actual occurrence type is required.

Suppose the nonempty T_j is disjoint from F(w). If j is ambiguous and
T_j={r}, the source-attribution law (9) already gives r in A subseteq
F(w), a contradiction. If j is ambiguous and |T_j|>=2, its contribution
to (7) is empty for every ambiguous menu: omitting at most the observer's
own factor still leaves a failed one. We can therefore replace w_j by
the full menu I without changing the output or any atomic status.

Now apply omission independence successively to each r in T_j. At
each step replace every input containing r by I. Since the unchanged
output omits r, omission independence preserves the entire output.
Every atomic r-set for r in T_j is emptied, while all outside-T_j
atomic sets stay unchanged. If j was atomic initially, its own color
belongs to T_j by extensivity, so this process also replaces w_j by I.
In all cases not already excluded, the final j-menu is I.

At the end j lies in no owner closure. For r in T_j use looplessness
c_r(empty)=empty; for r outside T_j use the unchanged atomic sets and
the definition of T_j. Formula (7) now makes j supply every winner.
This contradicts the unchanged output omitting the nonempty T_j.
The proof is complete.

Thus the all-owner side-effect test holds for the canonical factor
vector even though its occurrence realization remains unproved.
The atomic-source part is additional to the occurrence theorem, whose
marked menu must be ambiguous. Source attribution, omission independence
and loopless separation suffice for the argument; sufficiency of these
laws for core realizability is not asserted.

## An insufficient weak criterion

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

The [three-owner feedback law](three-owner-exchange.md) adds a stronger
necessary interaction between closures. Even reciprocal shared-witness
tests do not suffice. The [complete-head family](complete-head-circuits.md)
has an exact realizability criterion and greatest core minorant. It
also gives genuine separable operations whose maximal head full types
are nonactual, while their greatest old-observer free coefficients
are attained. These results leave general mixed-guard compatibility open.
