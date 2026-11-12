# One observing owner tests all owner extensions

Mathematical research, without Lean claims. For a genuine source-separable
core operation, attainment of its canonical common-carrier completion is
equivalent to stability under adding just one owner. If that one extension
is core, a single old-owner word works over every larger owner set. This
does not identify which guard families have the property; it relates three
previously separate formulations of that question.

Fix finite I with |I|>=3 and a genuine source-separable core operation F
on finite nonempty essential support V. Write c_r for its canonical owner
closures. For any owner set J containing I define

    k in F^J(w) iff some j with k in w_j is outside
                       UNION_(r in I, r!=k) c_r(E_r(w)),
    E_r(w)={i:w_i={r}}.                             (1)

This is the separable reconstruction with the old closures at old
owners and identity closures at all additional owners. An identity
closure at a new owner contributes only positions whose input is that
owner's singleton; it never removes a source containing a different
queried winner, so the displayed simplified formula is equivalent.

Let B_I have old atoms a_r and two ambiguous values n,p, with flat union
a_r<n<p. Its old-owned operation absorbs its own atom and otherwise
takes flat union. This is the manuscript's native carrier D_I.
Use the canonical G_Q from
[common-carrier completion](canonical-separable-extension.md).

**Theorem.** The following are equivalent:

1. Some old-owner word realizing F induces G_Q on B_I.
2. For one new owner omega, F^(I union {omega}) is a core operation,
   allowing even omega-owned gates in its initial realization.
3. There is a single word using only owners in I whose interpretation
   on every J containing I is F^J, even when J is infinite.

Thus the choice of the new owner in (2) does not matter. Allowing its
owned gates gives no additional realizations, and testing larger owner
extensions gives no stronger condition.

## Selector form and old singleton profiles

For the old atomic sets E_r put

    Q=V\UNION_(r in I) c_r(E_r);
    A={r in I:E_r\UNION_(s in I, s!=r)c_s(E_s) != empty}.

Old source attribution says that an old-ambiguous position shadowed
by exactly one old owner r can contribute only a winner already in A.
This condition concerns just the disjoint sets E_r. It therefore
continues to hold when some of those old-ambiguous positions are new
owner singletons. Formula (1) consequently simplifies to

    F^J(w)=A union UNION_(j in Q) w_j.               (2)

The colorful-cover lemma gives A or Q nonempty, so every F^J is
nonempty-valued. It agrees with F when all menus use old owners.

Its old singleton profiles are unchanged:

    F^J(w)={r} iff c_r(E_r(w))=V, for r in I.        (3)

If Q is nonempty, a free position cannot have the old singleton {r}:
extensivity would put it in c_r(E_r). Thus (2) cannot be that singleton.
If Q is empty, its value is A, exactly as in the original old operation
at any valuation with those old atomic sets and ambiguous remaining
menus. The old profile theorem identifies this singleton with the
spanning condition. The reverse implication follows in the same way.
No claim about *new* singleton profiles is needed for a synthetic F^J.

## From one extension to the common carrier

Suppose (2) of the theorem holds, with a word U over I union {omega}.
Consider winner menus other than the singleton {omega}. They form a
subalgebra for these operations. No subword can become the omega
singleton without such an input, by the singleton-profile recursion.
Hence every omega-owned gate acts as union throughout this subalgebra.

Replace each such gate by the fixed derived-union word using three
old owners. This produces an old-owner word T with the same values
as U on that subalgebra, and in particular on the original old carrier.
Thus T realizes F there.

The observing quotient sends old singletons to a_r, ambiguous menus
omitting omega to n, and menus containing omega to p. It is onto B_I
on this subalgebra, using {r}, I and I union {omega} as input lifts.
It preserves union and every old-owned choice. Formula (2) identifies
the p-output precisely with a p-marked position in Q; (3) gives the
old atomic outputs. The quotient of F^(I union {omega}) is therefore
exactly G_Q. Surjectivity gives T interpreted on B_I equal to G_Q.
This proves (2) implies (1).

## One old word works for every extension

Suppose an old-owner word T induces G_Q. For a new observing owner
q in J\I, map a winner menu to its old atom if it is an old singleton,
to p if it contains q, and to n otherwise. This is a homomorphism
from the J-winner carrier to B_I for all old-owned choices. Its
non-atomic value n includes a new singleton different from q;
no gate of T is owned by that new singleton. Formula (2), together
with (3), says that the same quotient of F^J is G_Q. Consequently
T and F^J have identical membership bits for every new winner q.

For an old observing owner k, use instead its omitted-atom face:
all k-containing menus map to p, other old singletons to their atoms,
and all remaining menus to n. There is no a_k in this face, so
choice_k acts as flat union there, exactly as required by the quotient.
Every other old choice retains its own-atom absorption. The old
singleton outputs (3) and the k-source formula (1), which ignores
c_k, identify the quotient of F^J with the prescribed old face of
G_Q. Hence T and F^J have the same old winner bits too.

All winner memberships agree, so T realizes F^J for every J. This
proves (1) implies (3); the implication (3) implies (2) is immediate.

## Consequences and scope

The disjoint-context, full-owner
[complete-head operations](complete-head-circuits.md) fail (1)-(3):
their first new owner already witnesses failure, although the original
operation is core. Any context overlap in that family supplies a
uniform old-owner word and satisfies all three conditions.

This equivalence concerns disjoint atomic statuses on B_I. Attaining
every canonical full occurrence vector is sufficient for (1), by
marked coextension, but a converse is not established here. Nor should
this criterion be identified with greatest independent-flag coefficients
at the original observers: the disjoint-context examples attain those
coefficients while failing (1).
