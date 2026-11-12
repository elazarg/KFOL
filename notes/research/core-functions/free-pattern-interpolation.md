# Complete interpolation at one independent-status pattern

Mathematical research, without Lean claims. At one fixed independent-status
pattern, prescribed full singleton profiles and any prescribed source bits
have a closed feasibility criterion. For an admissible profile tuple, the
entire source-vector fibre has an explicit positive-clause presentation.
The result allows overlapping flags. It does not identify the compatibility
conditions between different independent-status patterns.

Fix finite variables V, at least three old owners I, and an observer k that
is either old or fresh. Fix independent flag sets E_h for old owners h!=k.
If k is old, set E_k=empty; its value is immaterial to the free coefficient
recurrence. Put

    L = V \ UNION_(h!=k) E_h.

These are the sources that can all be queried at the same E. Write c_j(S)
for the free coefficient C_(j,k)^S(E), j in L. The profiles Phi_h^S(A)
are ordinary singleton profiles. All words use only primitive old-owner
choices, variables, and no constants or role switches.

## A selected zero budget

For J subseteq L, call a word J-zero when c_j=0 for every j in J. The
aggregate OR_(j in J) c_j has the same recurrence as one source coefficient.
Consequently J-zero words are closed under every primitive owned choice.

For one owner r and coalitions A,B, define PairSafe_J(r;A,B) by the following
explicit disjunction, writing D=A\B:

    D\J is nonempty; or
    D is nonempty, r!=k, and E_r\B is nonempty; or
    D is nonempty and E_h intersect A is nonempty
        for some h outside {r,k}.                         (1)

**Separator lemma.** There is a J-zero word with Phi_r(A)=1 and Phi_r(B)=0
if and only if (1) holds.

For sufficiency the first alternative is a projection with label in D\J.
If it fails, choose d in D subseteq J. For the second alternative choose
l in E_r\B and use x_d choice_r x_l. For the third choose
l in E_h intersect A and use x_d choice_h x_l. In each case l is outside J,
and its h-flag blocks the only source from J. The displayed coalition
conditions give the requested positive and negative r-profile bits.

For necessity, if D is empty ordinary monotonicity already excludes a
separator. Otherwise failure of (1) gives D subseteq J, E_r subseteq B when
r!=k, and E_h intersect A=empty for all h outside {r,k}. Induct on a
separator word to show that its aggregate J-coefficient is one. At a leaf
its label lies in D. At an r-root choose a child with the positive A-bit;
both children have negative B-bits, so the sibling's r-profile at E_r is
zero. At a foreign h-root both children have the positive r-profile at A;
choose one with the negative B-bit. If h!=k, the sibling cannot have a
positive h-profile at E_h, since two differently owned winning coalitions
A and E_h would then have to intersect. Thus the selected child's aggregate
source survives at either kind of root. An observer-owned root is unfiltered.

For a rainbow family A_r, one coalition per old owner, put C=intersection_r A_r.
Define RainbowSafe_J(A) by

    C is nonempty, and either
    C\J is nonempty; or
    E_h intersect intersection_(r!=h) A_r is nonempty
        for some old h!=k.                                (2)

Here the final two alternatives are inside the condition following
"C is nonempty".

**Rainbow lemma.** There is a J-zero word satisfying all the positive
rainbow demands Phi_r(A_r)=1 if and only if (2) holds.

The first alternative uses a projection in C\J. Otherwise C is a nonempty
subset of J. If a blocker l in the last alternative exists, choose j in C
and use x_j choice_h x_l. The source-j contribution is blocked and l is
outside J. Conversely, if C subseteq J and every blocker intersection is
empty, the common-source-set persistence theorem in
[free-profile-nonattainment.md](free-profile-nonattainment.md) forces
OR_(j in C) c_j=1. An empty C is impossible by ordinary rainbow
common-source persistence.

## Complete profiles under the zero budget

Let Phi be a prescribed complete tuple of Boolean profile tables. A word
has profiles exactly Phi and is J-zero if and only if all three conditions
hold:

1. Phi_r(V)=1 for every owner r.
2. Every pair Phi_r(A)=1, Phi_r(B)=0 satisfies PairSafe_J(r;A,B).
3. Every rainbow selection with Phi_r(A_r)=1 for all r satisfies (2).

**Proof.** Necessity follows from the two lemmas and the top bits. For
sufficiency take the actual profile image of all J-zero words. It is closed
under the mixed profile gates. The restricted Horn classification of
[profile relations](profile-bounds.md) therefore gives exactly forced true
bits, same-owner implications, and rainbow conflicts. The separator lemma
describes precisely its same-owner implications. Forced true bits are
included by pairing a false prescribed bit with its owner's true top bit.
The rainbow lemma describes precisely its rainbow conflicts; partial
rainbows extend with top coalitions. Thus the prescribed tuple satisfies
the complete theory of that image and belongs to it. This argument also
handles an empty J-zero image, whose empty conflict is detected by extending
with top bits. QED.

There is no unknown profile realizer, supplied elimination order, or
auxiliary relation presentation on the right side of this criterion.

## Reset padding supplies the positive bits

Two elementary facts turn the zero-budget criterion into exact interpolation.

First, for h!=k and j outside E_h,

    Phi_h^S(E_h)=1 implies c_j(S)=0.                       (3)

Induct on S. At an h-root either absorbing child blocks the other source
contribution, and its own contribution is zero by induction. At every
foreign root the positive h-profile passes to both children, so induction
sets both source contributions to zero.

Second, take any word T and p in L. Start with u=x_p and, once for each
distinct old owner r, replace u by u choice_r T. Call the final word
Reset(p,T). Its complete profiles equal those of T. For a fixed profile
bit t, its own gate applies OR with t and every other owner's gate applies
AND with t. Since there are at least two owners, the resulting value is
t, independently of the starting leaf bit and the order of the fold.

Suppose Phi_h^T(E_h)=0 for every h!=k. At E, each intermediate word in this
fold also has foreign h-profile zero: the initial leaf has zero there
because p is eligible, and OR/AND with zero preserves zero. Every foreign
filter is therefore open. Consequently, for every j in L,

    c_j(Reset(p,T)) = c_j(T) OR [j=p].                     (4)

Thus reset padding adds one eligible source bit without changing any
other source bit or any profile. In particular it preserves every zero
budget not containing p.

**One-pattern interpolation theorem.** Let P,J be disjoint subsets of L.
There is a word with profiles exactly Phi, c_p=1 for p in P, and c_j=0
for j in J, exactly when:

1. The preceding closed zero-budget criterion holds for Phi and J.
2. If P is nonempty, Phi_h(E_h)=0 for every old h!=k.

Necessity uses (3). For sufficiency choose the J-zero profile realizer
supplied by the criterion and apply (4) successively for each p in P.
All earlier positive bits and every prescribed zero remain unchanged.

## A direct clause presentation of the entire fibre

Now assume Phi is an admissible full profile tuple. If some h!=k has
Phi_h(E_h)=1, equation (3) says that the only attainable vector on L is
the all-zero vector, and any word realizing Phi supplies it.

Otherwise the attainable vectors c in {0,1}^L are exactly the models of
the following two explicit families of positive clauses.

**Rainbow clauses.** For every selection Phi_r(A_r)=1 for all old owners
such that

    E_h intersect intersection_(r!=h) A_r=empty
        for every h!=k,

include the clause

    OR_(j in intersection_r A_r) c_j = 1.                 (5)

Admissibility makes this intersection nonempty, and the avoidance conditions
put it inside L.

**Separator clauses.** For every r,A,B with Phi_r(A)=1, Phi_r(B)=0, put
D=A\B. If D subseteq L,

    r=k or E_r subseteq B,
    E_h intersect A=empty for every h outside {r,k},

include the clause

    OR_(j in D) c_j = 1.                                  (6)

Ordinary profile monotonicity makes D nonempty.

To prove completeness, let J be the zero coordinates of a proposed vector.
A failed separator test is exactly a clause (6) whose entire support lies
in J. A failed rainbow test is exactly a clause (5) whose entire support
lies in J. The zero-budget theorem therefore gives a profile realizer
whose bits on J vanish. Equation (4) fills the remaining coordinates to
one without changing those zeros. Soundness follows from the same tests.

Hence, unless an absorbing rival profile forces the zero vector, the
fixed-profile source fibre is upward closed and has a complete positive
clause theory. The two-corner nonattainment law for ternary tight quotas
is one rainbow clause (5), rather than a missing compatibility test within
this one-pattern theorem. Simultaneously satisfying such theories at
several patterns requires further compatibility: reset padding can add
unwanted source bits at other patterns.

## Clauses for the joint profile/source image

Equivalently, the whole joint image at E, with the profile tuple allowed
to vary, has the following closed presentation. Require ordinary profile
admissibility: top bits, same-owner monotonicity, and nonempty intersection
for every positive full rainbow. Add these three clause families:

1. For j in L and h!=k, `c_j AND Phi_h(E_h)` is forbidden.
2. For every rainbow A_r obeying the geometric avoidance conditions of
   (5), all the bits `Phi_r(A_r)` together imply
   `OR_(j in intersection_r A_r) c_j`.
3. For every r,A,B obeying the geometric conditions of (6),
   `Phi_r(A) AND NOT Phi_r(B)` implies `OR_(j in A\B) c_j`.

These conditions characterize exactly the tuples of complete profile bits
and eligible source bits of one old-owner word. The first family handles
an absorbing rival profile. In its absence the other two families are
precisely the complete fixed-fibre clause presentation just proved.
All indexing coalitions, sources, and flag sets belong to the prescribed
variables and owners; no auxiliary realizing object is quantified over.
