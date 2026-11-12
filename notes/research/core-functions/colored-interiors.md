# Colored interiors and the outcast law

Mathematical research, without Lean claims. This gives a closed coupling law
between ambiguity patterns and selected input positions. The resulting
interiors do not characterize joint core realizability.

Use the common carrier B_I from [unowned-observer.md](unowned-observer.md):
there is an atom r for each owner r in the finite set I, together with N,P.
Flat union merges different atoms to N, N absorbs atoms, and P absorbs
everything. Choice r absorbs its atom r; otherwise it is flat union.
Assume K=|I|>=3. Let sigma:B_I->D_I identify N,P and keep the old atoms.

The [status-fiber selector theorem](status-selectors.md) concerns the original
winner carrier. Here an unowned observer keeps a selected source visible
even when every old owner is already present: a selected P still yields P.

## Selections at an atomic coloring

Fix a finite nonempty variable set V, a core term operation G on B_I, and a
full old-atom coloring a:V->I. For J subseteq V let e_J assign N to J and
atom a_j outside J. Define

    C_a(J)={j in J : G(e_J with input j := P)=P}.           (1)

At fixed singleton/ambiguous statuses, every subterm's singleton status is
fixed. An owned node either absorbs to its owner's singleton, or takes
flat union. Thus the P-output is the disjunction of a fixed set of ambiguous
input positions. In particular, for T subseteq J,

    G(e_J with P at every position of T)=P
        iff T intersects C_a(J).                          (2)

When T misses C_a(J), that output is exactly G(e_J). This follows by the
same induction: marked positions outside the selected set contribute
nothing, while the chosen positions all still have value N.

## A ternary invariant proving outcast

Define a relation R on three copies of B_I by

    (x,y,z) in R iff sigma(x)=sigma(y)
                       and (x!=P implies z=y).            (3)

**Lemma.** Every owned choice, and flat union, preserves R.

The equality of sigma-statuses is preserved because sigma is a
homomorphism. For a choice owned by h, consider the first output x.

* If x=N, neither first-coordinate operand can be P. A P would persist
  unless absorbed by atom h, which would make x atomic. Both input triples
  therefore have z=y, so the last two outputs are equal.
* If x is atom r and h=r, some first-coordinate operand is atom r. The
  corresponding second operand is also atom r by status equality, and its
  third operand equals it by (3). Both the second and third outputs are r.
* If x is atom r and h!=r, both first-coordinate operands are atom r.
  Their second and third coordinates are r as well, giving equal outputs.

There is no condition to check when x=P. For flat union, a non-P first
output forces both first operands to be non-P, so their last two
coordinates agree. This proves the lemma directly on B_I, without adding
fresh roles or invoking a general invariant-completeness theorem.

**Strong outcast theorem.** Suppose C_a(J) subseteq J' subseteq J. Replace
any positions in J\J' by arbitrary old owner atoms, retaining the original
atoms outside J and any chosen N/P markings on J'. This replacement
preserves the entire output of G.

Use three valuation rows. In the first, put P at all discarded positions
J\J' and N at the retained positions J'. In the second, keep N at the
discarded positions and give the retained positions their chosen N/P
markings. The third row is the second after the stated atom replacements.
Each input column lies in R: it is (P,N,atom r) at a discarded position,
(N,N,N) or (N,P,P) at a retained position, and (atom r,atom r,atom r)
outside J. By (2), the first output is not P: none of its marked positions
belongs to C_a(J). Preservation of R makes the second and third outputs
equal, as required.

## The selection maps are interiors

**Theorem.** C_a is a contractive, monotone, idempotent operator on the
subsets of V. Moreover,

    C_a(J) subseteq J' subseteq J
        implies C_a(J')=C_a(J).                           (4)

Contraction is part of (1). For monotonicity, increasing J changes some
old atoms to N in the flat-union order. Owned choices are monotone for
this order, so a P-output at a marked j persists. Hence J subseteq J'
implies C_a(J) subseteq C_a(J').

For idempotence take J'=C_a(J) in strong outcast, and mark one retained
j with P. Its output was P before replacement and remains P afterwards,
so every j in C_a(J) belongs to C_a(C_a(J)). Contraction gives the reverse
inclusion. Finally monotonicity between C_a(J), J', and J proves (4).

The fixed sets form a union-closed family containing the empty set. Indeed,
the union of fixed sets is contained in its own image by monotonicity,
and contraction gives equality. Conversely an interior is recovered by

    C_a(J)=UNION {S : C_a(S)=S and S subseteq J}.           (5)

The family is not generally an antimatroid. With two variables both colored
r, the term x choice_r y has just two fixed sets: empty and {x,y}. This
family fails accessibility.

There are elementary compatibilities between the colorings. If a,b agree
outside J, then C_a(J)=C_b(J), because the valuation rows in (1) are equal.
Also C_a(V) is independent of a: it is the variable support of G. On
all-N inputs there are no atomic absorbers, so a P at j survives exactly
when j occurs in the term.

## Relation to singleton profiles

Strong outcast gives

    G(e_J)=G(e_(C_a(J))).                                 (6)

If C_a(J) is nonempty, G(e_J)=N: its sigma-status must permit a selected
P, and e_J itself contains no P. If C_a(J) is empty, (6) says
G(e_J)=G(a). Thus if G(a) is atom r, emptiness of C_a(J) is equivalent
to G(e_J)=r. If G(a)=N, all the e_J have output N.

In particular, for the constant coloring a_j=r and the r-singleton profile
Phi_r of G,

    C_r(J)=empty iff Phi_r(V\J)=true.                     (7)

Equivalently, Phi_r(E) holds exactly when E meets every nonempty fixed
set of C_r. It suffices to test the inclusion-minimal nonempty fixed sets.
Singleton profiles therefore record this part of the interior, while larger
fixed sets can carry additional selection behavior.

## Every interior occurs at one constant coloring

**Theorem.** Let C be any interior operator on subsets of finite nonempty
V with C(V)=V. There is a full-support core term G whose selection map at
the constant old-atom coloring r is C.

For each nonempty fixed set S of C form the choice_r-fold of the variables
in S. Take the derived union of all these folds. The family is nonempty
because V is fixed, and derived union is core-definable for K>=3.

At e_J, a fold whose S is not contained in J has an atom-r input and is
absorbed to r, regardless of any P marks. A fold with S subseteq J has no
atomic input and takes flat union, selecting precisely its positions S.
The full union therefore selects exactly the right side of (5), which is
C(J). The occurrence of the fold for V also gives full support.

For every other constant coloring s!=r, this same construction has
C_s(J)=J: a nonambiguous input is atom s, never the absorbing atom r,
so all the folds take flat union and together use every variable.

Thus no further law on a single constant-color interior can solve the
global compatibility problem.

## A closed lower bound from the singleton profiles

There is a further necessary coupling between the interiors and the positive
profile bits. Let S be the nonempty variable support of G, and let Phi_r
be its old-owner singleton profiles, restricted to coalitions in S. For
an atomic coloring a and ambiguity set J, put

    E_r={i in S\J : a_i=r}.

Define L_(Phi,a)(J) to consist of the positions j in J for which there are
coalitions A_r subseteq S, one per old owner r, satisfying

    Phi_r(A_r)=true for every r;
    intersection_(r in I) A_r={j};
    E_r intersects intersection_(s in I, s!=r) A_s = empty
        for every r in I.                                (8)

All data in (8) come from the given profiles and atomic coloring; it asks
for neither a realizing word nor an auxiliary invariant relation.

**Theorem.** Every B_I core term satisfies

    L_(Phi,a)(J) subseteq C_a(J).

If G is represented by a primitive read-once word, equality holds. Here
read-once means distinct variables at distinct leaves and only primitive
owned-choice nodes. Derived union is not a primitive node, since its
implementation repeats inputs.

For soundness introduce one fresh, unowned role omega. Give input j the
singleton {omega}, every other input in J the ambiguous old menu I, and
every input outside J its old singleton {a_i}. The omega-observer quotient
of this actual winner valuation is e_J with P at j. The word uses only
old-owner gates, so its omega-profile is the conjunction of all its
support variables: the coalition A_omega=S is positive.

Use the old coalitions A_r in (8), together with A_omega=S. Their common
intersection is {j}, which supplies omega. At an old owner r, the atomic
positions are exactly E_r within S, and the last line of (8) is precisely
the rival-singleton exclusion in the positive-profile lower-bound lemma
from [read-once-profile-minimum.md](read-once-profile-minimum.md).
That lemma forces omega into the word's output. Its observer value is P,
so j belongs to C_a(J).

For exactness assume the primitive word is read-once and j is selected.
Apply the read-once theorem to the same winner valuation on I union
{omega}. Its strengthened certificate gives positive coalitions supported
in S, with common intersection {j} and the stated rival exclusions. The
positive omega-coalition must contain all of S, and is also contained in
S, so it is exactly S. Removing it leaves the old-owner intersection
{j} and gives precisely (8). Thus every selected position has the required
certificate.

The resulting formula is an exact interior description for this read-once
regime and a closed lower bound for every core term. It does not give a
sufficient integrability condition for general overlapping input reuse.

## Even the full ternary invariant does not characterize integrability

The dependence completion D_F in
[unowned-observer.md](unowned-observer.md) gives a stronger benchmark.
For v in B_I^V its cofactor domain Q(v) fixes old-atom positions and lets
N/P positions range over the entire old winner carrier. The completion
returns atom r when F is constantly {r} there, P when some P-position is
essential there, and N otherwise.

At an old coloring a its selection map is exactly

    C_a(J)=essential variables of F on Q_a(J).             (9)

These maps are interiors for any finite-domain F: essentiality persists
when a cofactor domain grows, and fixing all inessential variables
simultaneously does not change the function on the remaining variables.
Their dependence on a is automatically constant on colorings agreeing
outside J.

In fact D_F preserves the full relation R in (3). Given input columns in
R, the first two rows u,v have the same cofactor domain Q. If D_F(u) is
not P, F on Q is independent of all u-P positions. Only those positions
can differ between the second and third rows v,w. Such a difference may
fix an irrelevant variable to an old atom, or change its N/P marking;
it cannot enlarge Q. The restricted function therefore has the same
constant-atom behavior and the same essential variables and marks at all
other positions. Thus D_F(w)=D_F(v). The first two output sigma-statuses
also agree because they use the same Q. This is precisely preservation
of R.

Nevertheless the sharp K+1-variable example in
[unowned-observer.md](unowned-observer.md) has a dependence completion
which is not induced by any term. Choose distinct old owners a,b,c. Start
R with Z_a choice_c Z_b and append each remaining Z_r using choice_a,
including Z_c. Put

    T=(X choice_a Z_c) choice_b R.

For its old winner operation F, fixing Z_r={r} makes R the full old role
set I. The left child can never be {b}, for any old X: its absorbing case
is {a}, and otherwise it contains c. Thus the cofactor in X is constantly
I, and D_F returns N at (X=P, Z_r=atom r).

Every term realizing those old observer faces nevertheless returns P
there. The explicit rainbow certificate in
[unowned-observer.md](unowned-observer.md) uses positive owner coalitions
with common intersection {X} and excludes every rival atomic position.
The profile lower-bound lemma then forces a fresh winner supplied by X.
This proof allows the repeated use of Z_c and does not assume T is
read-once. Equivalently, with J={X} and the displayed old colors outside
J, (8) requires X to be selected, while the constant cofactor makes the
dependence completion's C_a(J) empty. Thus the closed profile lower law
strictly strengthens the ternary-invariant and interior tests.

Consequently this benchmark has correct core faces and singleton profiles,
is flat-order monotone, has the colored interiors above, and preserves the
entire ternary relation R, yet has no common term realization. The result
identifies a natural family of closed coupling laws; it does not supply
the remaining intrinsic criterion for joint source guards.
