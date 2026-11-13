# A forced profile beyond feedback with a fresh identity owner

Written mathematical proof, not yet formalized in Lean. A
nine-variable loopless closure tuple satisfies strong feedback elimination
both at its given owners and after adjoining a fresh identity owner. It
nevertheless has no common pure-port realizer. The obstruction is a
positive singleton profile forced by six capture constraints. Its proof
is a term induction using the rainbow-budget and feedback profile-passage
lemmas; no computation is used.

The example works for every finite owner set I containing three distinct
owners A,B,C. Other owner closures are identities. Its separable
reconstruction is nonempty, has exactly the specified dependence closures,
and satisfies pair-cut, reciprocal intersection and hereditary omission.

## The closure tuple

Take the eight variables from
[the three-color feedback example](feedback-three-colors.md), and add
an uncaptured variable W:

    V={uA,uB,uC,p,q,e,t+,t-,W}.

For each owner generate its closure by the rows of the following table.
Only the A0 premise has changed from the eight-variable construction.

| owner/query | premise P_i | captured block X_i |
|---|---|---|
| A0 | uB,uC,q,t-,W | uA,p,t+ |
| A1 | uB,uC,p,t+ | uA,q,t- |
| B0 | uA,uC,e,t+ | uB,p,t- |
| B1 | uA,uC,p,t- | uB,e,t+ |
| C0 | uA,uB,e,t- | uC,q,t+ |
| C1 | uA,uB,q,t+ | uC,e,t- |

Let H_s=X_(s0) union X_(s1). Directly from the table,

    c_s(E)=E union H_s if some s-owned P_i is contained in E;
           E otherwise,                             (1)

for s in {A,B,C}. Indeed H_s subseteq P_i union X_i for either
s-owned row, so the first firing already supplies every newly added
element of H_s. For all other owners c_s=id. These are loopless closures,
and W is never captured.

Write FE+ for strong (FE) both on this tuple and on the tuple obtained
by adjoining one fresh identity owner. Further identity owners add no
new nonempty captured blocks to any feedback test.

## Strong feedback holds at the supplied owners

First restrict to the three owners A,B,C. We use the exact
[three-owner conditional criterion](three-owner-exchange.md): strong
(FE) is equivalent to hereditary common-source profiles for the two
conditional foreign closures at every observer-independent base B,
with D=c_r(B)\B.

Let d_A,d_B,d_C be the original eight-variable closures, before anchoring
A0. Their conditional foreign pairs have the hereditary property, by
the independent-base analysis in the cited three-color construction.

For observing owner B or C, an independent base consists of an old
independent base, optionally with W adjoined. Its D is unchanged.
On a retained set containing W, every foreign spanning coalition must
contain W. On a retained set omitting W, the modified conditional A
closure is below its old counterpart; the other foreign closure is
unchanged. The old hereditary pair condition therefore still holds.

For observing owner A, an inactive independent base has D=empty.
The B,C pair then has hereditary common-source profiles directly from
the original three-color hereditary theorem; a retained W is again
common to all spanning coalitions.

An active A-independent base has one of exactly these forms:

    P_A1, optionally with e and/or W;
    P_A0, optionally with e.                         (2)

Here P_A0 already includes W. Any other old variable outside the
chosen premise belongs to its captured block, and would be redundant
in the base. In the first case D=X_A1; in the second D=X_A0.
After omitting W these are precisely the original active independent
bases, namely an old A-premise optionally with the opposite two-cycle
variable e. Thus their conditional B,C pairs are the old pairs, with
an optional uncaptured W. Their hereditary profile compatibility follows.

All observer-independent bases have now been covered, proving full
strong (FE) at A,B,C.

## A fresh identity observer adds no violation

We prove that the closure tuple admits no raw rainbow feedback.
The variable W cannot occur in any nonempty captured head. Since every
feedback premise must be covered by such heads, it cannot contain W
either. Thus A0 cannot fire in a raw feedback query.

Every remaining nonempty query can be replaced by one of the five
canonical rows A1,B0,B1,C0,C1. To see this, take its first-fired
canonical premise P_i. It is contained in the query premise, while
(1) and H_s subseteq P_i union X_i put its captured block inside X_i.
Shrinking the premise and enlarging the head preserve all existing
rainbow covers. Empty heads can be removed.

Neither B row has a cover using the available A,C heads. Premise B0
requires both e and t+. The only A head, X_A1, contains neither, and
no single C head contains both. Premise B1 requires p, which is in
neither X_A1 nor either C head. Hence no B query can belong to a
feedback configuration. Every remaining A or C premise contains uB,
which requires a B head to cover it. Therefore no nonempty feedback
configuration exists.

For an identity observing owner every independent base has D=empty;
its conditional feedback is a restriction of this raw feedback test.
For an observing owner A,B,C, additional foreign identity owners have
empty captured heads and cannot enlarge any cover. Consequently strong
(FE) holds after adjoining a fresh identity owner, and remains valid
after any further identity owners are adjoined. This proves FE+ uniformly
for all I containing A,B,C.

## Six captures force an additional A-profile

**Forced-profile law.** Every core word whose pure closures satisfy all
six displayed capture constraints has

    Phi_A({W})=true, equivalently c_A({W})=V.        (FP)

We prove persistence of this profile from the six scalar capture
budgets. Recall Q={0<a<b}, with join +=max and multiplication * equal
to 0 if either input is 0, and max otherwise. At coordinate s,
choice_s is * and every foreign choice is +.

For row i use its owner coordinate s_i and assign 0 on P_i, b on X_i,
and a elsewhere. Call the resulting scalar output U_i(T). The capture
constraint is exactly

    U_i(T)<=a,                                      (3)

because a b output means that some member of X_i survives its pure
s_i probe. Also U_i(T)=0 exactly when Phi_(s_i)(P_i) is true.

Suppose all six budgets (3) hold but Phi_A({W}) is false. We descend
to a smaller word with these same properties.

At a B-owned root, the A0,C1 budgets pass to both children because
those coordinates use join. Their head blocks cover either B premise:

    P_B0,P_B1 subseteq X_A0 union X_C1.

The rainbow-budget projection lemma therefore excludes a child with a
positive B-profile at P_B0 or P_B1. Neither child is zero on either
B row. Their B multiplication is consequently maximum, so both B
budgets pass too. All other budgets already pass by join. The A-profile
at {W} is an AND at this foreign root, so a false bit selects
a child with Phi_A({W}) false.

At a C-owned root the same argument uses A1,B1:

    P_C0,P_C1 subseteq X_A1 union X_B1.

Thus all budgets pass and a child retains a false A-profile at {W}.

At an A-owned root that profile is an OR, so its false value makes
both children have Phi_A({W}) false. All B,C budgets pass to both
children. Since

    P_A1 subseteq X_B0 union X_C0,

the rainbow-budget lemma excludes a zero child on row A1. If a child
were zero on A0, its A-profile would be positive at P_A0. Apply the
word-level feedback profile passage to that child using budgets B0,C0.
The two covers are

    P_A0 intersect P_B0={uC} subseteq X_C0;
    P_A0 intersect P_C0={uB,t-} subseteq X_B0.

It forces the child's A-profile at

    P_A0\(X_B0 union X_C0)={W}

to be positive, contradicting the child's inherited false profile.
This excludes the A0 zero child too. Thus both A budgets pass, and
either child retains the false profile required for descent.

Union roots and roots of any additional owner use join on all six
budget rows. Their A-profile is an AND, so they pass the budgets and
select a child with a false A-profile at {W}. At a leaf that false
profile means its label is not W. Every one of the eight old variables
lies in some X_i and hence has value b on a budget row. No leaf can
satisfy all six budgets. This completes the descent and proves (FP).
The argument uses only the budget and profile-passage lemmas, not any
finite relation enumeration.

The proposed tuple violates (FP): neither A premise is contained in
{W}, so c_A({W})={W}, a proper subset of V. No common pure-port
realizer exists. Together with the preceding sections, this refutes
FE+ sufficiency
for every fixed owner count K>=3.

## The separable reconstruction has the stated dependence closures

Define the candidate winner operation by its source products:

    k in F(w) iff some j with k in w_j lies outside
                         UNION_(s!=k) c_s(E_s(w)).   (4)

Every two different-owner premises share the third owner's star
variable. Hence two different owners cannot activate simultaneously
on a partial atomic coloring. With no active owner (4) is input union;
with one active owner s it is exactly that owner's canonical one-color
trace. Both cases are nonempty. On all-ambiguous inputs it is input
union, so every variable is essential.

If j in c_s(E)\E, choose an s-premise contained in E. Fixing E to
the s singleton disables every foreign trigger uniformly: the shared
premise variable is fixed to s and cannot be the foreign atom. The
whole cofactor of (4) is therefore the one-color operation for c_s,
whose dependence closure is c_s. In particular it is independent of j.
Conversely every j outside c_s(E) has its pure-source probe as an
essentiality witness. Thus the c_s are exactly F's monochromatic
dependence closures.

For omission independence, if k is absent from F but occurs in an
input, the unique active owner s differs from k, and every k-bearing
input is an s-captured head outside the fixed trigger premise.
Changing these inputs preserves that premise, keeps every foreign
trigger disabled, and leaves the one-color output unchanged.
In a winnerwise neutral restriction the surviving rules are exactly
those whose premises lie in the retained set; distinct-owner premises
still intersect, so the same argument applies there.

The tuple also satisfies
[pair-cut and reciprocal intersection](mixed-closure-outcast.md). For
colored idempotence, an active s-premise remains fixed while captured
heads are restored. It keeps every foreign trigger disabled, and the
s-closure's idempotence prevents additional s-captures. This is the
colored-closure form of pair-cut. For reciprocal intersection, the
shared third-owner star belongs to neither owner's captured head block.
Removing the two reciprocal heads therefore leaves this shared witness.

These compatibility properties do not repair the failed forced profile.
The reconstruction is a valid nonempty operation with exact closure
semantics, while its canonical guards have no core realization.
