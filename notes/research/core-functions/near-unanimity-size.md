# Near-unanimity size and rigid quota operations

Mathematical research, without Lean claims. The profile quotient has small
near-unanimity arity, but realizing it by primitive owned-choice gates
requires exponentially many leaf occurrences. Tight owner quotas also give
an explicit family of uniquely determined minimal full winner operations,
including operations with no primitive read-once minorant.

Fix K>=3 owners I. Let D_I have their K atoms and one ambiguity value *.
Choice r returns atom r if either input is r; otherwise it takes flat
union: equal atoms stay equal, different atoms merge to *, and * absorbs
all atoms. This is the profile quotient described in
[unowned-observer.md](unowned-observer.md).

An n-ary operation is near-unanimous when its output is x whenever all
but one input equal x, for every x and exceptional value y. A primitive
word is a binary tree with owned-choice nodes; variables may repeat.
Its size below counts leaf occurrences, not distinct variables or shared
subexpressions. A primitive read-once word has distinct variables at all
leaves.

## Every path must see every owner

**Lemma.** If a primitive word induces a near-unanimity operation on D_I,
every root-to-leaf path contains a gate of every owner.

Suppose the path to an occurrence of variable j omits owner r. Assign
variable j the ambiguity * and every other variable atom r. All subterms
then take values in {r,*}. At an owner different from r the operation
is their union, so * propagates along the selected path. There is no
r-owned gate on that path to absorb it. The root is *, contradicting
near-unanimity at the exceptional variable j. Repetitions of j elsewhere
cannot help: they only supply additional * values.

**Theorem.** Every primitive word inducing near-unanimity has at least
2^K leaf occurrences. If equality holds, the word is a perfect binary
tree of depth K, every owner occurs exactly once along each root-to-leaf
path, and every leaf has a different variable.

The lemma gives minimum leaf depth K. Thus all the nodes above depth K
are internal, giving 2^K nodes at depth K and at least as many leaves.
Equality forces all those nodes to be leaves. Each path then has exactly
K owner labels and must contain each owner once.

Suppose two leaves in this equality case carried the same variable j.
Let their least common ancestor be owned by h. No h-owned gate occurs
strictly below it along either chosen path, or strictly above it. Assign
j the ambiguity * and every other variable atom h. The two selected
occurrences propagate * to the two children of that ancestor; both inputs
to its h-owned gate are *, so its output is *. This propagates to the
root, again contradicting near-unanimity. Thus no variable repeats.

Consequently an n-ary near-unanimity word with n<2^K needs at least
2^K+1 leaf occurrences. Equality at 2^K would require 2^K distinct input
variables, even if some of its n available coordinates were unused.

The same proof applies if the required near-unanimity equations concern
only atom baselines from a set P of owners. Every leaf path must contain
those owners, giving at least 2^|P| leaves. Equality again forces distinct
leaf variables. No condition at the ambiguity baseline is needed for
these lower bounds.

## Exact primitive read-once near-unanimity arity

**Theorem.** The least arity of a primitive read-once near-unanimity word
on D_I is exactly 2^K.

The lower bound is already proved. For the upper bound take a perfect
binary tree of depth K, give its levels the K different owners, and put
different variables at its leaves.

If the common input value is an old atom r, the sole anomalous leaf meets
an r-owned ancestor. Its sibling subtree has only the common input r
and evaluates to r, so that ancestor absorbs the anomaly. Every higher
subtree then evaluates to r.

If the common input value is *, an anomalous old atom t is erased at any
ancestor whose owner differs from t, because its sibling subtree is *.
Such an ancestor exists since every path has all K owners. Once erased,
it remains *. An anomalous * requires no argument. This proves
near-unanimity for all inputs, including the ambiguity baseline.

## Comparison with unrestricted near-unanimity arity

The least near-unanimity arity without the read-once restriction is K+1.
For existence, on K+1 variables use the owner profiles

    Phi_r(E) iff |E|>=K, for every r.

They are admissible: K such winning coalitions omit at most K positions
in total and therefore have a common variable. Profile synthesis gives
a term whose D_I operation outputs atom r when r occurs at least K times,
and * otherwise. This is near-unanimous, including at the * baseline.

For nonexistence at an arity n<=K, a near-unanimity word would have
Phi_r(V\{j}) true for every owner r and coordinate j. Assign to the K
owners omitted coordinates that together cover V. The resulting K
winning coalitions have empty intersection, violating the common-source
condition for profiles.

Thus a near-unanimity operation exists at arity K+1, but every primitive
word for it has at least 2^K+1 leaf occurrences. The size bound is on
ordinary words; it does not count nodes in a circuit with shared
subexpressions.

## Tight owner quotas determine the entire winner operation

Return to the full winner carrier A_I of nonempty subsets of I. Let V
have n>=1 variables. Choose nonnegative integer quotas d_r, one per owner,
with

    SUM_r d_r=n-1,       t_r=n-d_r.

Define U_d on full winner menus by

    U_d(w)={r} if at least t_r inputs are exactly {r};
           UNION_i w_i otherwise.                        (1)

There is at most one owner in the first case: for distinct r,s,
t_r+t_s=2n-d_r-d_s>=n+1. Put Phi_r(E)=[|E|>=t_r].

**Theorem.** Phi is admissible and maximal admissible. U_d is a core
operation, is the unique full core operation with profiles Phi, and is
minimal among all core operations under pointwise inclusion.

Admissibility follows because a winning r-coalition excludes at most d_r
positions. The K coalitions exclude at most n-1 positions altogether and
therefore intersect. Profile synthesis supplies at least one core operation
G with these profiles.

For maximality, a new positive coalition A at owner r would have
|A|<=t_r-1=SUM_(s!=r) d_s. Partition A among the other owners into bins
B_s of sizes at most d_s. The already-positive coalitions V\B_s,
together with A at owner r, have empty common intersection. Thus no
additional positive bit can be admitted.

It remains to prove that all full values of G are forced. At a quorum
input, its profile already forces the corresponding singleton. Suppose
instead that there is no owner quorum. Choose any k in the full input
union and a position i with k in w_i. Partition the n-1 other positions
into bins B_r of sizes d_r. Call a position bad if it is in B_r, its
input is exactly {r}, and r!=k.

There is a partition with no bad positions. To see this choose one
minimizing their number. If a bad position p is in B_r, some position q
outside B_r is not the r singleton. Otherwise the (n-1-d_r) outside
positions, together with p, would give t_r copies of {r}, contrary to
the no-quorum assumption. Swap p and q. Position p is now in a different
owner's bin and cannot be bad; q is allowed in B_r because it is not
the r singleton. No new bad position is created, a contradiction.

For a bad-free partition take A_r=V\B_r. Every A_r has size t_r and
is positive. Their common intersection is {i}, which supplies k. For
r!=k, the intersection of all the other coalitions is {i} union B_r.
It contains no r-singleton input: i supplies k, while B_r is bad-free.
These are exactly the hypotheses of the closed profile lower bound in
[read-once-profile-minimum.md](read-once-profile-minimum.md). It forces
k into G(w). Conservativity gives the reverse inclusion, so G(w) is
the whole input union.

This proves G=U_d and hence both core realizability and uniqueness in
the complete profile fiber. In fact the closed positive-profile envelope
is also U_d. At a quorum for r the same partition argument works for
k=r, since its failure could only produce a quorum for a different owner;
the latter is impossible. Thus the envelope is nonempty there and is
exactly {r} by its soundness for G.

Finally, if a core H is pointwise below U_d, it retains every positive
profile bit of U_d. Maximality forces its complete profile tuple to be
Phi, and uniqueness forces H=U_d. This proves global minimality directly;
no choice of a minimal element in a finite poset is needed.

## Exact read-once classification within the quota family

**Theorem.** U_d is primitive read-once if and only if at most one quota
d_r is positive. If two or more are positive, it has no primitive
read-once core minorant.

If n=1, all quotas vanish and (1) is the projection. Otherwise a single
positive quota must be d_r=n-1. Its threshold is 1 and all other thresholds
are n. Formula (1) is precisely the owner-r fold of all the variables,
which is primitive read-once.

If at least two quotas are positive, choose an owner r with d_r>0.
Then 2<=t_r<n. Its minimal winning coalitions are all t_r-subsets of V,
and every pair of variables lies in some such coalition. Their
cooccurrence graph is therefore complete. Its only maximal clique is V,
whereas the minimal coalitions are proper subsets. This violates the
necessary clique condition for read-once profiles in
[read-once-recognition.md](read-once-recognition.md). Hence U_d is not
read-once. Its already proved minimality excludes any read-once core
operation below it, including operations ignoring some input variables.

Every primitive read-once operation is minimal by the
[read-once profile lower-bound theorem](read-once-profile-minimum.md).
The quota family gives explicit counterexamples to the converse, with a
closed formula for every full winner value.

**Quota word-size corollary.** Let p be the number of positive quotas.
Every primitive word realizing U_d has at least 2^p leaves. Equality
forces all leaf variables to be distinct; in particular if n<2^p,
at least 2^p+1 leaves are needed.

For every owner with d_r>0, its profile accepts V\{j} for every j.
Thus the word satisfies the atom-baseline near-unanimity equations for
those p owners. The earlier path and equality proofs apply with that
owner set, independently of any other owner's baseline behavior.

## Unique extensions and explicit colored interiors

**Corollary.** Every old-owner word realizing U_d has the same operation
over every ambient role extension, provided no new-owner gates are added.
It returns an old owner's singleton at its prescribed quorum and otherwise
returns the union of all inputs. In particular its operation on B_I is
unique: the same old-atom quorum rule, followed by flat union otherwise.

First let the larger role set be finite. The old-owner profiles are still
Phi_r, since their gate recursions do not depend on the ambient roles.
Every original variable is essential in each threshold profile, so every
realizing word has full support V. At a new owner there is no gate of
that owner, and its singleton profile is therefore unanimity on V. Give
each new owner quota zero. The enlarged quotas still sum to n-1, so the
uniqueness theorem applies on the larger winner carrier. A new-owner
unanimity case already equals the ordinary input union, proving the
displayed formula.

The assertion also holds for infinite ambient role sets, bit by bit. At
a new query winner k, send every k-containing menu to P, old singleton
menus to their atoms, and every remaining menu to N. This is a
homomorphism for all old-owner gates into B_I. For an old query k, send
k-containing menus to P, rival old singletons to their atoms, and every
remaining menu to N; this lands in its omitted-atom observer face. These
finite observers determine every winner membership. The formula already
proved on the finite common carrier therefore gives the same quorum or
input-union value on the infinite carrier.

In the notation of [colored-interiors.md](colored-interiors.md), its
selection map at any old-atom coloring a is explicitly

    C_a(J)=empty if some r has at least t_r positions
                           of color r outside J;
           J otherwise.                                  (2)

A quorum masks every ambiguous position. Without a quorum the B_I
operation is flat union, so each ambiguous position supplies its marker.
For the constant coloring r this becomes

    C_r(J)=empty if |J|<=d_r, and J otherwise.              (3)

Thus this non-read-once family has both a unique common observer
extension and a closed colored-interior description. Extension rigidity
is not limited to primitive read-once operations.

## An explicit ternary non-read-once example

For n=3 take d_a=d_b=1 at distinct owners a,b, with all other quotas
zero. U_d returns {a} or {b} when that singleton occurs twice, and
otherwise returns the full input union. It has the five-leaf word

    (X choice_a Y) choice_b (Z choice_a (X choice_b Y)).    (4)

Its a-profile is (X OR Y) AND (Z OR (X AND Y)), its b-profile is
(X AND Y) OR (Z AND (X OR Y)), and both are Boolean majority. Every
other owner's profile is X AND Y AND Z. The uniqueness theorem above
therefore proves (4) on all winner menus, not just on atoms.

Five leaves are optimal by the quota word-size corollary with p=2 and
n=3: four leaves would require four distinct variables.

Thus even a minimal ternary core operation need not be primitive
read-once. Arity two cannot supply such an example within this quota
family: its quota sum is one, so exactly one owner can have a positive
quota.

## Uniform quotas and near-unanimity

The D_I quotient of U_d is near-unanimous exactly when every d_r>=1.
The r-atom baseline with one exception is retained precisely when
n-1>=t_r, equivalently d_r>=1. If every quota is positive, each t_r>=K,
so a single anomalous atom at the ambiguity baseline cannot reach any
quorum and the output stays *. These observations prove both directions.

In particular let every d_r=d>=1. Then

    n=K d+1,       t_r=(K-1)d+1.

Formula (1) gives an explicit infinite family of minimal full core
operations with no primitive read-once minorant, while their profile
quotients are near-unanimous. At d=1 the quotient has the least possible
near-unanimity arity K+1, and every primitive word for it needs at least
2^K+1 leaves by the initial size theorem.

The full A_I operation is not asserted to be near-unanimous: for an
ambiguous common input its non-quorum value can be the union with the
exceptional menu. The near-unanimity statements concern D_I.
