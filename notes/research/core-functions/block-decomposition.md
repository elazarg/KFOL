# Canonical disjoint-block decomposition of the full core

This is a mathematical reduction for full winner-valued operations, not just
one observer. It uses the neutral-source elimination theorem already proved
in the library. It does not settle the remaining prime operations.

Fix a finite role set I with K>=3, and let A be its nonempty subsets. Partition
the input variables into nonempty disjoint blocks V_1,...,V_m. All operations
below are nonempty-valued. An operation G is idempotent when G(X,...,X)=X
for every X in A.

## Neutral sections recover every active input

For k in I put N_k=I\{k}. For an operation H on m inputs define its
winnerwise neutral section at input i by

    k in delta_i H(X)  iff
        k in H(N_k,...,N_k,X,N_k,...,N_k).                 (1)

For a core operation H, this section is the identity if input i is essential,
and is identically empty if it is inessential.

Here is the elementary proof for a term containing i. If k is absent from X,
it is absent from every input and hence from the output. If X is ambiguous
and contains k, all inputs are ambiguous; no owned choice can absorb, so the
term is their union and retains k. If X={k}, every subterm value lies in
{N_k,{k},I}. The first value is ambiguous because K>=3, so no foreign-owner
singleton can absorb. Presence of k at a node is exactly its presence in
at least one child. Thus it reaches the root precisely when i occurs.
The constant assignment of all inputs to N_k gives no k, so an occurrence
also witnesses essentiality. This proves both assertions.

More generally, for a block B define

    k in Gamma_B F(x_B)  iff
        k in F(x_B, all inputs outside B := N_k).         (2)

The library's neutral elimination theorem says that for core F this is zero
or a lower-arity core operation. If B contains any essential input, it is
the latter: giving every input of B the same X reduces (2) to the preceding
argument, so Gamma_B F(X,...,X)=X. In particular it is nonempty-valued,
idempotent, and surjective onto A.

## Exact factorization theorem

**Theorem.** Let each G_i:A^(V_i)->A be idempotent and let H:A^m->A use
every input essentially. Put

    F(x)=H(G_1(x_(V_1)),...,G_m(x_(V_m))).

Then F is a core operation if and only if H and all G_i are core operations.
Moreover, whenever F is core, these factors are uniquely determined by F
and its partition:

    H(X_1,...,X_m)=F(x_j := X_i for j in V_i),             (3)
    G_i=Gamma_(V_i) F.                                   (4)

The reverse direction is composition of terms. For the forward direction,
identify all inputs inside each block. Idempotence of G_i recovers (3),
so H is a core minor of F. At a query winner k, set every variable outside
V_i to N_k. Each other G_j evaluates to N_k by idempotence. Since H is
core and its i-th input is essential, (1) recovers precisely membership of
k in G_i. Thus (4) holds. Neutral elimination now makes G_i core; its
nonempty values exclude the zero alternative. Equations (3) and (4) also
prove uniqueness. If H has ignored inputs, the same conclusion applies to
its essential inputs; an ignored factor is unconstrained.

The essential-outer-input condition matters only to avoid claiming anything
about ignored factors. Idempotence supplies both the diagonal sections in
(3) and the neutral values of the other blocks in (4). Neither step assumes
that the originally supplied factors were core.

## Intrinsic recognition of a block decomposition

For core F with every input essential, all its nonempty block sections are
already nonempty and idempotent. Define H_P by the block-diagonal minor (3).
The partition is a disjoint idempotent decomposition exactly when the
following identity holds:

    F(x)=H_P(Gamma_(V_1) F(x_(V_1)),...,
             Gamma_(V_m) F(x_(V_m))).                     (5)

Necessity is the uniqueness theorem; sufficiency uses the displayed factors.
Thus no search over unspecified inner or outer operations is needed.

For an arbitrary candidate F, form the same canonical sections and minor.
If the sections are nonempty and idempotent, the minor uses every block,
and (5) holds, the factorization theorem reduces membership in the core
exactly to membership of these canonical smaller operations. The core
assumption above guarantees the section conditions; it is not needed to
apply this reduction once those conditions have been checked directly.

The recovery formula (4) in fact requires only that H be core with the
indicated input essential, together with idempotence of the other factors;
F itself need not yet be core. Its proof uses only (1) and those neutral
values. This stronger form is useful when ruling out decompositions of a
candidate noncore operation.

There is also a condition for one block B using contexts. Write

    x_B equivalent_B y_B  iff
        F(x_B,z)=F(y_B,z) for every outside assignment z.

Context equivalence always implies equality of Gamma_B, by (2). The block
can be replaced by its single A-valued summary Gamma_B exactly when the
converse holds as well. If several blocks have this property, replace them
one after another by the constant block Gamma_B(x_B). Idempotence keeps
the summary unchanged, and contextual equivalence preserves the output.
After all replacements the result is (5).

For core F with B active, or whenever the candidate section has been checked
to be nonempty and idempotent, Gamma_B is surjective. Its kernel then has
exactly |A| classes. Context
equivalence refines that kernel. Consequently the single-block condition
is equivalent to having exactly |A| distinct context functions

    z |-> F(x_B,z)

as x_B varies. This is a closed property of the operation table. It detects
whether an entire block carries precisely one winner-set state to the rest
of the operation.

## The canonical factors are visible in the source guards

Write c^F_(j,k)(p) for the coefficient of source j at observer k, with each
passive input either a rival-owner singleton or neutral. For B containing j,
the coefficient of Gamma_B F is simply

    c^(Gamma_B F)_(j,k)(p)
        = c^F_(j,k)(p extended by neutral outside B).      (6)

This follows directly from the winnerwise definition (2) and does not
require an unknown term. For the diagonal minor H_P, suppose F has the
source-reconstruction property, as all core operations do. Then

    c^(H_P)_(i,k)(p)
        = OR_(j in V_i) c^F_(j,k)(expanded_i(p)).          (7)

Here expanded_i(p) puts neutral at every other input in V_i and copies the
passive status of block l to every input in V_l for l!=i. To prove (7), set
all inputs in V_i to {k}. The only possible k-sources of F are in V_i;
their other same-block inputs are neutral in the passive source observation,
while every other block has its prescribed rival singleton or neutral menu.
Source reconstruction gives exactly the displayed disjunction.

Thus both canonical factors are computed by restriction and merging of
the given guard bits. Their mathematical definitions do not introduce
auxiliary occurrence graphs, candidate terms, or clutter presentations.

These facts reduce any available disjoint decomposition to canonical smaller
core-membership questions. They do not assert that every core operation
has a proper disjoint decomposition: repeated use of overlapping inputs is
exactly what this reduction leaves to the global characterization problem.

The [four-variable gluing obstruction](face-gluing/README.md) is already
prime in this sense. A proper decomposition means a partition with
2<=m<|V|, so both its outer factor and all inner factors have smaller
arity. The example differs from its atomic realizer only at tuples
with four distinct inputs, so every proper identification minor is core.
All its proper neutral sections are core as well. A proper disjoint
idempotent decomposition would therefore have core outer and inner factors,
contradicting its non-realizability. This supplies a fixed prime benchmark
for any criterion proposed after factoring the canonical blocks.
