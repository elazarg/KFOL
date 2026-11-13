# Exact lower-arity normal forms for a retained source

Written mathematical proofs, without new Lean claims. The statements and
complete induction are `core:lem:winner-erasure` and
`core:thm:retained-source` in
[the report source](../../../sections/appendix-core-retained-sources.tex).

Fix finite K>=3. A core operation F(X,v) retains X if X subseteq F(X,v)
at every valuation. Equivalently its canonical X-source coefficients
are all identically true. This is a condition on the full source array,
not on one occurrence's type in a chosen word.

## Fixed-winner erasure

For ANY core word t(X,v) and owner q, put h(v)=t({q},v) and
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
