# A mixed-color global minimum with nonmaximal profiles

Mathematical research, without Lean claims or enumeration. Work throughout
with exactly the three owners I={0,1,2} and their nonempty winner menus.
Terms use primitive owned choices, without constants or role switches.

The four-leaf word

    F=(X choice_1 Y) choice_0 (Y choice_2 Z)               (1)

is the least core operation in its exact singleton-profile fibre and is
globally minimal under pointwise winner-set inclusion. Its singleton
profiles are not maximal admissible, and its positive-profile lower
envelope is empty at one valuation. Every realizer must repeat Y.
Thus neither maximal admissible profiles nor linearizability of every
chosen input is necessary for a globally minimal core operation.

In tuples below, a digit denotes its singleton menu; 01 denotes {0,1},
and similarly for 02 and 12. Products such as XY denote coalitions,
not winner menus. Write N_k=I\{k}.

## The profiles and the critical bound

The singleton recursion gives

    Phi_0(E) iff Y in E and (X in E or Z in E);
    Phi_1(E) iff {Y,Z} subseteq E;
    Phi_2(E) iff {X,Y} subseteq E.                        (2)

These winning families all require Y. Consequently projection Y has
a strictly larger admissible profile tuple; in particular (2) is not
maximal admissible.

Put

    W=(1,0,2).

The two inner choices in (1) absorb to 1 and 2, so F(W)=12.

**Profile-retention lemma.** If a core operation S satisfies S<=F, then
its singleton profiles are exactly (2).

Inclusion retains every positive profile bit of F: at a singleton output
of F, the nonempty subset S must be that same singleton. Any further
winning coalition for S must contain Y. At owner 0, intersect the retained
coalitions YZ of owner 1 and XY of owner 2. Their intersection is {Y},
so rainbow common-source persistence excludes a new 0-winning coalition
missing Y. For owner 1 use the retained coalitions YZ at owner 0 and
XY at owner 2; for owner 2 use XY at owner 0 and YZ at owner 1. The
same argument applies.

It therefore suffices, by profile monotonicity, to exclude the extra bits

    Phi_0(Y),   Phi_1(XY),   Phi_2(YZ).                  (3)

The first would make S(W)=0, contradicting S(W) subseteq 12. For the
second, use positive coalitions A_0=YZ,A_1=XY,A_2=XY and the same bound
12 at W. Their common intersection is {Y}, whose input is 0 and hence
not allowed. The allowed owner-1 absorber would require X to belong to
A_0 intersect A_2={Y}, and the allowed owner-2 absorber would require
Z to belong to A_0 intersect A_1={Y}. Neither is possible. The rainbow
one-bound theorem therefore excludes this extra bit. For the third use
A_0=XY,A_1=YZ,A_2=YZ; the same two absorber intersections are again {Y}.
This excludes all of (3), proving the lemma.

We use the rainbow one-bound theorem in precisely the form stated in
[profile-bounds.md](profile-bounds.md): positive coalitions and a winner
bound require a common-source projection inside the bound or an allowed
owner's atomic input in the intersection of the other coalitions.

## Closed source coefficients of F

At a source-j, observer-k probe, j is {k}, every passive rival atom is
its singleton, and every neutral passive input is N_k. Only j contains
k, so the source coefficient is exactly output membership of k.

The occurrence-path calculation for (1) gives

    c_(X,0)=[Y!={1}];
    c_(X,1)=NOT(Y={0} AND Z={0});
    c_(X,2)=[Y!={1}] AND NOT(Y={0} AND Z={0});             (4)

and the Z-coefficients follow by swapping X,Z and owners 1,2. Source Y
has two occurrences, giving

    c_(Y,0)=[X!={1}] OR [Z!={2}];
    c_(Y,1)=true;
    c_(Y,2)=true.                                       (5)

For example the X occurrence has its inner 1-filter [Y!={1}] and
outer 0-filter excluding the other branch's 0-profile Y_0 AND Z_0.
The two Y occurrences have no rival-0 filter, because their source
status prevents the opposite clause from being the 0 singleton. One
has only the 1-filter [X!={1}], the other only the 2-filter [Z!={2}].
This proves (4)--(5).

## F is least in its exact profile fibre

**Theorem.** Every core operation S with the profiles (2) satisfies F<=S.

First the positive-profile lower bound already forces every coefficient
in (5). The following choices of
positive coalitions all have common intersection {Y}:

| Supplying winner or condition | A_0 | A_1 | A_2 |
|---|---|---|---|
| Y supplies 1 | XY | YZ | XY |
| Y supplies 2 | YZ | YZ | XY |
| Y supplies 0 and X!={1} | XY | YZ | XY |
| Y supplies 0 and Z!={2} | YZ | YZ | XY |

For the first two rows, every rival atomic-deviation intersection is
{Y}, which cannot be a rival atom when Y supplies the requested winner.
In the third row, the owner-1 intersection is XY and is safe because
X!={1}; the owner-2 intersection is just Y. The fourth row is symmetric.
Thus each row is a valid rainbow lower-bound certificate.

For source X it remains to check the following maximal positive passive
patterns of (4). Each row gives an owner r and coalitions A,B with
Phi_r(A)=true and Phi_r(B)=false in (2).

| Observer k | Source-probe tuple (X,Y,Z) | F value | r | A | B |
|---|---|---|---|---|---|
| 0 | (0,2,1) | 02 | 2 | XY | Y |
| 0 | (0,2,2) | 02 | 2 | XY | YZ |
| 1 | (1,0,2) | 12 | 0 | XY | Y |
| 1 | (1,2,0) | 12 | 2 | XY | Y |
| 1 | (1,2,2) | 12 | 2 | XY | YZ |
| 2 | (2,0,1) | 012 | 0 | XY | Y |
| 2 | (2,01,0) | 012 | 2 | XY | Y |

In every row the exact same-owner pair forces S to contain k. Suppose
instead that S is bounded there by U=I\{k}. All three PairSafe alternatives
from profile-bounds.md fail:

* A\B={X}, and X has menu {k}, outside U.
* If r is allowed by U, every r-atomic input lies in B, so E_r\B is
  empty. If r is not allowed, this alternative is unavailable.
* For every allowed owner s!=r, its atomic set E_s misses A.

These assertions follow directly from the displayed tuples; 01 in the
last row is ambiguous and has no atomic status. Therefore no term bounded
by U separates the positive r-bit at A from the negative r-bit at B.
The assumed profiles of S contradict that bound, proving k in S at every
listed probe.

Every positive passive pattern in (4) is obtained from one listed for
its observer by replacing some rival singleton inputs with N_k. Such a
replacement enlarges the actual menu. Monotonicity of core operations
therefore propagates membership of k from the listed source probes to
all positive patterns.

This proves that all X-source coefficients of S dominate those of F.
The operation (1) and the profiles (2) are invariant under simultaneously
swapping X,Z and owners 1,2, so the same proof handles every Z-source
coefficient. Together with the Y certificates, every source coefficient
of S is at least the corresponding coefficient of F. Source reconstruction
gives F<=S, proving the theorem.

**Corollary.** F is globally minimal. Indeed any core S<=F has the exact
profiles (2) by the profile-retention lemma, and the theorem then gives
F<=S. Hence S=F.

## Its greatest free completion and two-type source frontier

The displayed word also attains the greatest arbitrary antitone extension
of all its source coefficients. Interpret every rival atomic status flag
independently, allowing the same passive variable to have several owner
flags. Equations (4)--(5) remain its exact free coefficient formulas.
Their occurrence-path derivation used only the exclusion of the marked
source from each rival atomic set. For example, at a marked Y occurrence
the other branch's 0-profile contains the source flag Y_0, which is false
by definition; it did not use mutual exclusivity of different passive flags.

To see maximality, every zero in those free formulas has a one-hot zero
subpattern, obtained by erasing all flags except the indicated ones:

| Source and observer | Zero condition | One-hot zero witness |
|---|---|---|
| X,0 | Y_1 | Y_1 |
| X,1 | Y_0 AND Z_0 | Y_0,Z_0 |
| X,2 | Y_1 OR (Y_0 AND Z_0) | Y_1, or Y_0,Z_0 |
| Y,0 | X_1 AND Z_2 | X_1,Z_2 |
| Y,1 and Y,2 | Never | None needed |

The Z formulas and witnesses are symmetric. Each listed witness is a
valid ordinary passive pattern: its flags occur at different input variables
or all belong to one owner. In particular X_1,Z_2 is genuinely mixed
but still one-hot. Any antitone completion agreeing with the ordinary
coefficient is zero above a one-hot zero witness. It therefore cannot
exceed the displayed free formulas at any zero point. At every other
point those formulas already have the largest Boolean value, one.

Consequently the word (1) realizes the canonical greatest arbitrary
antitone source extension, and hence the greatest term-induced free
extension, simultaneously at all old observers. This is a greatest-extension
statement; it asserts neither uniqueness nor a least term-induced extension.

At the shared source Y, however, there is no greatest actual full occurrence
type. The two displayed Y occurrences have the exact full vectors

    B_L: B_1=[X!={1}], B_0=B_2=true;
    B_R: B_2=[Z!={2}], B_0=B_1=true.                      (6)

They are precisely the two maximal sound full types, and hence precisely
the two maximal actual full types at Y. Indeed the observer-1 and observer-2
source coefficients are unconditional. The observer-0 coefficient has only
one false ordinary passive pattern, namely X={1},Z={2}. A sound vector B
must therefore satisfy

    B_1({X})=false or B_2({Z})=false.                     (7)

Antitonicity makes the first alternative imply B_1<=[X!={1}], and the
second imply B_2<=[Z!={2}]. Thus every sound vector lies below B_L or
B_R coordinatewise. Conversely every vector below either is sound, since
that maximal vector is actual in (1). The two actual maximal vectors are
incomparable, proving the claimed maximal frontier.

A greatest actual vector would have to dominate both vectors in (6),
forcing all three factors true. That vector is unsound at X={1},Z={2}.
Thus the greatest free extension is attained here by the OR of two
incomparable actual occurrence contributions; it does not come from a
greatest single full type. The argument classifies the maximal frontier,
not the actualness of every sound vector strictly below it.

## The positive-profile envelope misses the minimum

Let R_Phi be the closed positive-profile lower envelope from
[read-once-profile-minimum.md](read-once-profile-minimum.md). Both F and
projection Y retain every positive bit of (2). Its universal lower-bound
property therefore gives

    R_Phi(W) subseteq F(W) intersect {0}=empty.

Thus R_Phi(W) is empty, while F(W)=12. A globally minimal core operation
need not equal the lower envelope of its positive profiles. Global
minimality alone therefore does not identify the operation with that
profile-defined lower bound. In fact the exact profile fibre has the
genuine least operation F, so its output intersection at W is 12 rather
than empty. The negative profile bits used by the PairSafe argument force
winners which positive-profile certificates alone cannot force.

## Every realizer must repeat the shared source

All pure-owner source sections at Y are true. For owner 0 use either
constant coefficient c_(Y,1) or c_(Y,2) from (5); for owner 1 use
c_(Y,2), and for owner 2 use c_(Y,1). On a pure-owner probe these
coefficients are precisely the OR of that owner's full factors over
the Y occurrences.

If a realizer had only one Y occurrence, every one of its full owner
factors would therefore be identically true. Its observer-0 contribution
would be unconditional. But F loses Y's 0 at W, where X=1 and Z=2.
This contradiction shows that every realizer has at least two Y leaves.
The variable is essential by (2), so it cannot be absent. X and Z are
also essential, and the displayed four-leaf word attains this leaf lower
bound.

In particular F is not one of the
[matroid operations](matroid-core-operations.md): those have maximal
admissible profiles and a
[realizer linear in every chosen source](minimal-cnf-matroids.md).
Nor can disjoint compositions of matroid operations
produce F. The chosen-input linearization property is preserved under
disjoint composition: choose a word linear in the selected block input
at the outer factor, and inside that single block occurrence choose a
word linear in the selected original variable. Repeating this along a
disjoint factorization tree gives a word using Y once, which F forbids.

## Its individual owner closures are not matroids

The pure-owner sections in (4)--(5) give the canonical closures

    c_0(E)=E union ({X} if {Y,Z} subseteq E else empty)
               union ({Z} if {X,Y} subseteq E else empty);
    c_1(E)=E union ({X} if Y in E else empty);
    c_2(E)=E union ({Z} if Y in E else empty).

None satisfies matroid exchange. For c_1, X is in c_1({Y}) but Y is
not in c_1({X}); c_2 is symmetric. For c_0, Z is in c_0({X,Y}) but
not in c_0({X}), while Y is not in c_0({X,Z}).

Thus the matroid classification of minimal two-owner CNFs cannot be
extended to arbitrary minima by imposing matroid exchange separately
at each owner. The mixed source correlations matter even when all
canonical individual closures are known.

This is a three-owner mixed-CNF minimum with essential overlap. It
excludes maximal-profile and matroid-only disjoint-decomposition routes
as universal accounts of global minimality; it does not classify arbitrary
mixed-color CNFs or jointly realizable source guards.
