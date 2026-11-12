# The separable upper hull of a core operation need not be core

Mathematical research, without Lean claims. Canonical pure-owner sections
give closure operators even when the original source coefficients do not
separate by owner. Taking the product of those sections gives a canonical
upper bound preserving the original singleton profiles and pure sections.
It need not be term-induced. Five variables and four owners suffice.

Fix a finite owner set I with at least three owners. Let F be a genuine
core operation on a finite full variable support V. At source j and an
owner r, let D_(j,r)(E) be its pure-r source coefficient, for E subseteq
V\{j}. One may use any observer k!=r: put j={k}, inputs in E equal
to {r}, and all other inputs equal to N_k=I\{k}. This coefficient is
independent of the choice of k!=r.

The [colored closure representation](separable-closures.md) gives

    D_(j,r)(E) iff j notin c_r(E)

for canonical loopless closure operators c_r. Define the separable hull
H, as a winner set, by

    k in H(w) iff some j has k in w_j and
        D_(j,r)(E_r(w)) for every r!=k,
    E_r(w)={i:w_i={r}}.                                  (1)

Whenever k belongs to w_j and r!=k, j is not in E_r(w), so every factor
in (1) is in its specified domain.

## Properties the hull always retains

**Lemma.** F(w) subseteq H(w). In particular H is nonempty-valued.
It has exactly F's singleton-output predicates, and its pure sections
are the same D_(j,r).

Every occurrence factor of source j at owner r is below the OR of all
such factors, namely D_(j,r). Its full contribution is therefore below
the product in (1). Taking the OR over supplying occurrences proves
F subseteq H.

If F(w)={r}, every potential source j for a different winner k has
j notin E_r(w). The pure-r source probe with that same E_r(w) still
has F-output {r}, since singleton profiles depend only on their owner's
atomic positions. Hence D_(j,r)(E_r(w)) is false and H cannot contain
k. Its nonemptiness makes H={r}. Conversely if H is a singleton, its
nonempty subset F is the same singleton. This proves exact agreement of
all singleton predicates, including their admissibility.

At a pure-r source probe, all other rival factors have empty atomic sets
and equal true. Thus H's pure section is precisely D_(j,r), as claimed.

The hull is inclusion-monotone: enlarging an input can add winner bits
and remove singleton statuses, so the antitone factors cannot change from
true to false. It is idempotent, because at an equal ambiguous input all
atomic sets are empty, and at equal atomic inputs only their common
winner is available.

It also has whole-input provenance. At an ambiguous source j, put
T_j={r:j in c_r(E_r)}. If T_j is empty, the whole menu w_j contributes.
If T_j is a singleton {r}, it can supply only r; but then E_r is nonempty,
since c_r(empty)=empty. The same winner is therefore covered by some
input equal to {r}. If T_j has at least two owners it supplies nothing.
Atomic sources are already whole singleton menus. Every output winner
can thus be covered by a whole input menu contained in H(w).

None of these properties proves joint source realizability.

## A five-variable counterexample

Now assume I contains four distinct owners 0,1,2,3. Take variables
X,Y,Z,Q,S and the primitive word

    F=((X choice_0 Y) choice_1 Q)
          choice_0 ((X choice_0 Z) choice_2 S).           (2)

Fix the atomic statuses

    Y=Z={0},     Q={1},     S={2},     X ambiguous.       (3)

At these statuses each inner 0-owned choice absorbs X. The left branch
then absorbs to 1, the right to 2, and the root returns {1,2}. Thus F
is constantly {1,2} throughout this status fibre.

For the hull the supplying factors at (3) are as follows. Only factors
relevant to the source's available winner are needed.

* At source X the 0-factor is false: both occurrences have a 0-owned
  sibling equal to {0}. Its 1-factor is true because the right occurrence
  has no 1-owned ancestor, and its 2-factor is true because the left
  occurrence has no 2-owned ancestor. Every other owner's factor is true.
* Source Y cannot supply 0: its unique occurrence has the 1-owned sibling
  Q={1}, so its 1-factor is false.
* Source Z cannot supply 0: its unique occurrence has the 2-owned sibling
  S={2}, so its 2-factor is false.
* Source Q supplies 1. Its only possible rival filter is the root's
  0-filter. On a pure-0 probe, the other branch has 0-profile
  `(X_0 OR Z_0) AND S_0`, which is false because S is not 0. Thus the
  0-factor is true; there are no other rival-owned gates on Q's path.
* Source S supplies 2 by the symmetric argument, using the other branch's
  0-profile `(X_0 OR Y_0) AND Q_0`.

Consequently (1) has the exact value

    H(w)={1,2} union ({0} if 0 in w_X else empty)          (4)

throughout (3). In particular,

    w_X={0,3} gives H={0,1,2};
    w_X={1,3} gives H={1,2}.                              (5)

Both outputs omit 3 while X contains 3 in both valuations. Omission
independence for every core operation says that changing such an input
arbitrarily cannot change the output. The differing values in (5)
contradict that law. Hence H is not a core operation.

Equivalently, the status-selector theorem already excludes (4). With
all other inputs fixed atomically and X ambiguous, a core operation is
a fixed atomic set, optionally unioned with the whole input X. It cannot
respond to 0 in X while ignoring 3 in that same menu.

The fourth owner is essential to this witness. The two fixed output
owners 1,2 mask every nonzero input bit when I={0,1,2}; (5) does not
give a three-owner counterexample. No three-owner hull theorem or
counterexample is asserted here.

Thus canonical closures, admissible singleton profiles, monotonicity,
idempotence and whole-input provenance do not make even this natural
upper completion integrable. Additional mixed-owner constraints remain
necessary, even when the closure data were extracted from an actual
core operation rather than supplied independently.
