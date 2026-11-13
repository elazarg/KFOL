# Exact lower-arity normal forms for a retained source

Written mathematical proofs, without new Lean claims. The statements and
complete inductions are `core:lem:winner-erasure`,
`core:thm:retained-source`, `core:lem:owner-face-erasure`, and
`core:thm:retained-profile-reduction` in
[the report source](../../../sections/appendix-core-retained-sources.tex).

Fix finite K>=3. A core operation F(X,v) retains X if X subseteq F(X,v)
at every valuation. Equivalently its canonical X-source coefficients
are all identically true. This is a condition on the full source array,
not on one occurrence's type in a chosen word.

## Fixed-menu erasure

For any fixed ambiguous menu A, ordinary neutral elimination already
supplies the same lower-arity erasure C=partial_X t: C<=t(A,v) and the
outputs agree outside A. The local ghost/profile induction additionally
shows that C preserves every nonzero singleton predicate of this cofactor.
This is uniform in A; there is no need to choose a different erasure for
different ambiguous menus. The residual is zero only when no passive input
occurs, in which case the cofactor is constant A.

Singleton menus need a different erasure. For ANY core word t(X,v) and
owner q, put h(v)=t({q},v) and
C=partial_X t. Either h is constantly {q}, or a lower-arity core g has

    g subseteq h intersection C,
    g minus {q} = h minus {q}.

The constructive induction also preserves every singleton predicate of h
that is not identically false. This qualification is essential: removing
q may turn an original {q,r} into {r}, introducing an artificial absorber.
For erasures g,h at a root r different from q, inspect whether each
original child's r-profile is nonzero:

| Left profile | Right profile | New core word |
| --- | --- | --- |
| nonzero | nonzero | g choice_r h |
| zero | zero | g union h |
| zero | nonzero | (g union h) choice_r h |
| nonzero | zero | g choice_r (g union h) |

At a q-root use g choice_q h. A constant-q child makes a q-root constant;
at another root discard that child. Foreign profiles conjoin, and the
one-zero row uses (g_r AND h_r) OR h_r = h_r at its root owner.
Thus nonzero profiles remain exact. The same absorber check against
the unowned-ghost evaluation proves g<=C. No empty winner value or
unproved empty-set unit is used in the core construction.

The motivating exhaustive binary experiment agreed with this lemma,
but the induction establishes it at every arity without an enumeration
premise.

## Complete retained-source normal form

Every core F>=X is either projection X, or has lower-arity core C and
optional lower-arity cores g_q<=C such that

    F({q},v) = {q} union g_q(v),
    F(S,v)   = S union C(v) when S is ambiguous.

The baseline C is intrinsically partial_X F. The optional g_q need not
be unique; their non-q parts are determined by the cofactor. Omission
means that cofactor is constantly {q}. Conversely every such choice
of C and g_q gives a core operation.

For sufficiency, Reset(C,X) is the baseline piece. For each g_q attach
X at all owners except q, starting from g_q. This selector returns X
at atoms other than q, and X union g_q at q and on ambiguity. There
are at least two distinct attachment owners; the second restores the
union if the first absorbed the starting singleton. The union of these
pieces is exactly F, using at most K+K(K-1)=K^2 copies of X with named
union.

There is a sharper primitive implementation than expanding those unions:
fold all pieces at owner a, and again at owner b, then combine the folds
at c, where a,b,c are distinct. On ambiguity both folds equal F. At
X={q}, the a-fold equals F unless q=a, in which case the reset piece
forces it to {a}; symmetrically for b. The final c-choice gives F in
all cases. Each piece occurs twice, hence at most 2K^2 primitive X
occurrences, independently of arity and helper complexity.

## Owner-directed contractive erasure

There is now a second erasure, directed by one owner a. Partition the input
set as W disjoint-union R, and suppose a core H has a nonzero a-profile
after all R flags are set to zero. There is a core G on W with

    Phi_a(G)(E) = Phi_a(H)(E),
    Phi_s(G)(E) >= Phi_s(H)(E union R) for EVERY s != a,
    G(w) subseteq H(z,w) whenever each z_j != {a}, j in R.

The foreign-profile inequality sets ALL deleted s-flags to ONE. This is
stronger than preservation of their zero sections and preserves every actual
foreign absorber throughout the owner-avoiding face.

The compiler marks subwords active if their deleted a-profile is nonzero.
An a-node is active iff either child is; a foreign node is active iff both
are, since two nonzero monotone profiles meet at their top coalition.
At an active a-node discard inactive children; at an active foreign node keep
both children and its original gate. All remaining leaves are in W.
Profile induction gives the two displayed assertions. On the non-a face,
actual a-absorbers are preserved by the exact deleted profile; foreign
absorbers are preserved by the stronger one-section domination. Inactive
a-children cannot absorb there. At every other node the original value is
union and contains the compiled child values. This proves contraction.

The construction handles simultaneous deletion directly and agrees with
successive deletions: a branch already inactive stays inactive after more
flags are deleted. It is a contractive profile erasure, not the entire
ordinary neutral residue.

## Exact profile reduction below a retained upper bound

Let F be ANY monotone winner correspondence retaining every input in a
nonempty R; F need not be core. Put

    D_a^R(w) = INTERSECTION_(q in (I\{a})^R) F(({q_j})_j,w).

For every nonzero prescribed a-profile f on W, these are equivalent:

1. Some core H<=F has deleted a-profile f.
2. Some lower-arity core G<=D_a^R has a-profile f.

Necessity is contractive erasure. Conversely attach the a-fold of R
to G by a-choice. If a retained input is atom a, the result is a and is
contained in F by retention. Otherwise choose a non-a atom from each
retained menu; monotonicity gives G<=F at that input, and F already contains
the retained union. Thus

    H'=G choice_a (a-fold of R) <= F.

This preserves all requested a-profile bits on coalitions avoiding R, so the
same equivalence handles one positive query or a same-owner positive/negative
pair. It gives the greatest monotone extension f OR OR_(j in R) x_j for every
attainable zero section f. For the zero function that extension is the
retained fold itself. Only (K-1)^|R| atomic cofactors are needed; ambiguous
cofactors follow by menu-inclusion monotonicity.

This explains the positive gluing counter. Its retained bound D has cofactors

    D(z=b,x,y) = {b} union (x choice_a y),
    D(z=c,x,y) = {c} union (x choice_b y).

Their intersection is {b} at (a,b) and {a} at (a,c). Any common lower-arity
core would therefore have b-winning coalition {y} and a-winning coalition
{x}, contradicting common-source admissibility. The earlier tree-descent
proof of this positive-only counter is superseded by this reduction in the
report (`core:prop:positive-profile-gluing`).

## Relation to the full target

This settles the normal-form and bounded-reuse question for globally
retained inputs. It does not give a fixed-copy bound for arbitrary
positive guards: [the rectangle hierarchy](rectangular-source-complexity.md)
already disproves that. Nor does it justify replacing an arbitrary
actual full type by a one-source spine; source-linear minorants can fail.
The remaining step is to localize the new positive normal form to
nonconstant guard regions while preserving the other regions' outputs.

The [prime Gray obstructions](prime-obstructions.md) show that taking all
retained extensions cannot finish the recognition problem: F_d union
projection_j is core for every j, while their intersection is noncore F_d.
These extensions are exactly the existing source-bundle deletion-patch
unions, so this limitation needs no new counterexample construction.

Further [guarded-source gluing data](guarded-source-gluing.md) isolate the
remaining interface conditions. Even in the retained class the cofactor
erasure is not canonically the literal intersection h intersection C.
