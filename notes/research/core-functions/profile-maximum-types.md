# Every sound full type is actual at a profile maximum

Mathematical research, without Lean claims. The greatest operation in a
singleton-profile fiber has a particularly simple actual-type theory:
soundness is a separate condition at each owner, and every sound type
occurs in a realizer. Each canonical maximal vector already has a
minorant in which its source occurs exactly once. Its greatest arbitrary
antitone source extension is also term-induced. These assertions concern
profile maxima; they do not hold for arbitrary core operations below them.

The [capture-trigger interval theorem](capture-trigger-normal-form.md)
extends the source-linear maximal-vector construction to every separable
operation above a profile maximum. The direct construction here uses just
one attachment per active owner.

Fix a finite owner set I with K>=3 and a finite nonempty full variable set
V. Let Phi be an admissible singleton-profile tuple. Its greatest
completion E on this specified variable set is

    E(w)={r} if Phi_r({i:w_i={r}}) is true;
         UNION_(i in V) w_i otherwise.                    (1)

At most one owner can satisfy the first case. The profile-maximum theorem
gives a core realization of (1), with exactly the profiles Phi. All its
variables are essential: on all-ambiguous inputs it is literal input
union. The full variable set matters; (1) does not drop a variable merely
because it is absent from some or all of the singleton profiles.

For an occurrence labeled j, a full factor vector B has one antitone
predicate B_r on subsets of V\{j} for each owner r, with B_r(empty)=true.
Its contribution at observer k is AND_(r!=k) B_r(E_r), where E_r is the
set of passive inputs that are r singletons. A type is sound when its
contributions are contained in E's canonical source coefficients on
every one-hot passive pattern. It is actual when it is the exact full
factor vector of some marked occurrence in a term realizing E.

These are the types of
[source-type-pruning.md](source-type-pruning.md), including all owner
factors of the same occurrence, not a separate choice at each observer.

## Source coefficients factor owner by owner

At a source-j, observer-k probe, the source is {k}; every other input is
a rival singleton or the ambiguous neutral menu I\{k}. The only way
to lose k is a rival singleton profile. Hence

    c^E_(j,k)(E)=AND_(r!=k) NOT Phi_r(E_r).                (2)

Here each E_r is a subset of V\{j}. The same formula makes sense with
independent, possibly overlapping owner flag sets.

Define the canonical full vector at source j by

    M_(j,r)(A)=NOT Phi_r(A),   A subseteq V\{j}.           (3)

It is antitone and true at empty.

**Soundness lemma.** A full vector B is sound for E if and only if

    B_r(A) implies M_(j,r)(A)
        for every owner r and every A subseteq V\{j}.     (4)

For necessity choose any observer k!=r. Give exactly A the r singleton
and make every other passive input neutral. All the other factors are
evaluated at empty and equal true. Equations (2) and soundness therefore
force B_r(A) to imply NOT Phi_r(A). Conversely the conjunctions in
(2) immediately prove soundness from (4).

Thus soundness of an entire full type already separates into its owner
coordinates in this regime.

## A source-linear minorant with the whole maximal vector

**Theorem.** For every source j there is a core word S_j<=E in which j
occurs exactly once, and that occurrence has the entire vector M_j
from (3). Thus one source-linear minorant supplies every contribution
of source j, at every observer and every independent flag pattern.

If V={j}, take S_j=j. Otherwise put W=V\{j} and define, for A subseteq W,

    f_r^0(A)=Phi_r(A);
    f_r^1(A)=Phi_r(A union {j}).

Call r active when f_r^0(W)=true. For each active r prescribe a sibling
profile tuple on W by

    beta_r^(r)=f_r^0;
    beta_q^(r)=f_q^1 for q!=r.                      (D)

This tuple is normalized. Its own coordinate has true top by activity.
Every foreign top is Phi_q(V)=true. If a foreign bottom were true,
Phi_q({j}) and Phi_r(W) would be two disjoint winning coalitions,
contradicting common-source admissibility. All bottoms are therefore
false. Monotonicity is inherited from Phi.

It is also admissible. Given a positive rainbow for (D), use its
r-coalition A_r unchanged in the original tuple Phi, and adjoin j to
every foreign coalition. The original common intersection is nonempty.
Since A_r excludes j, that intersection is exactly the common
intersection of the passive coalitions themselves. The profile theorem
therefore supplies a j-free core word G_r with profiles (D).

Start at j and attach G_r by choice_r once for every active r, in any
order. This is S_j. Only the r-owned stage changes its marked r-factor,
and that stage adds NOT f_r^0. An inactive f_r^0 is identically false,
so omitting its stage gives the same factor true. The marked full vector
is consequently exactly M_j, and j occurs once.

It remains to prove S_j<=E; the factor calculation alone would not
control contributions of auxiliary sources. At any profile coordinate q,
the own stage, when present, applies OR with f_q^0; every foreign active
stage applies AND with f_q^1. These updates commute because f_q^0<=f_q^1.
If there is a foreign active stage, the final profile is exactly

    f_q^0 OR ([j is a q atom] AND f_q^1)=Phi_q.

Here an absent own stage means f_q^0=false. If no foreign stage exists,
the final profile is [j is a q atom] OR f_q^0 when q is active, and
just [j is a q atom] when there are no active owners. In both cases it
contains Phi_q by the same monotone Boolean decomposition. Thus every
profile of S_j extends the corresponding prescribed profile Phi_q.

Where E returns the singleton {q}, this extension makes S_j return
that same singleton. Everywhere else E is the full input union, which
contains S_j by conservativity. This proves the required bound. The
argument includes zero or one active owner; it does not require a
foreign active stage to obtain the inclusion.

## A completion that restores the whole profile maximum

Fix a word realizing E, and let T be any core word on V. Choose an order
r_1,...,r_K of the owners, each occurring once. Starting at T, attach
one copy of E by each successive owned choice:

    T_0=T;
    T_l=T_(l-1) choice_(r_l) E,       1<=l<=K.             (5)

**Completion lemma.** T_K realizes E.

At a valuation where E={q}, its q-owned gate in (5) absorbs to {q}.
Every later gate combines {q} with the same {q}, so the final value is
{q}.

At an ambiguous E, formula (1) says E is the full input union U.
Conservativity gives T_0 subseteq U and keeps every later value inside U.
If T_0 is not the first owner's singleton, the first gate unions it
with U and returns U. Otherwise it can remain that singleton at the
first gate, but the second owner is different and its gate unions it
with U. After these first two gates the value is U and remains U.
There are at least two distinct owners because K>=3.

The use of the full input union is essential. For a general target whose
ambiguous value omits an input winner, conservativity does not place an
arbitrary T inside that target, and this restoration argument fails.

## Realizing any sound full type

**Theorem.** Every sound full type B at source j is actual in an E term.
Consequently (3) is the unique greatest actual full type at j, and all
actual types are exactly the coordinatewise weakenings in (4).

First make a spine u_B with just one marked j leaf. For each nontrivial
factor B_r, choose a core sibling on V\{j} whose r-profile is NOT B_r,
and attach it by choice_r. Such a sibling exists constructively: NOT B_r
is a monotone Boolean function, false at empty and true at the full set.
Write its monotone DNF; implement OR by choice_r and AND by any fixed
other owner's choice. No constants are needed. A true B_r needs no node.
If V\{j} is empty, every B_r is true and the spine is just j.

The marked leaf's exact full vector is B, since its r-owned spine node
adds precisely the factor B_r. There is at most one such node per owner,
and none of the siblings contains j.

Apply completion (5) to u_B. At a newly attached r-owned gate, the
sibling E has r-profile Phi_r(A), with source j excluded from A. The
marked occurrence acquires the extra factor NOT Phi_r(A)=M_(j,r)(A).
By (4) this does not change B_r. Every other factor is unchanged as well.
Thus completion restores E and preserves the marked full vector exactly.
This proves actualness.

The source-linear construction above already gives M_j in a minorant;
completion (5) preserves it and gives an E realizer. It bounds all other
actual vectors by (4). The result does not claim that one realizer can
contain every actual type exactly once: the spine completion can introduce
many other occurrences and types.

## The greatest free source completion is term-induced

Now let the rival-owner atomic flags be independent. A term's free source
coefficient is the OR of its marked occurrence contributions, each the
product of the appropriate full factors. By (4), every E realizer has

    C^free_(j,k)(E)<=AND_(r!=k) NOT Phi_r(E_r).             (6)

For each j complete its source-linear minorant above, realizing the
maximal full vector M_j. Combine these E realizers by a fold of one fixed
primitive owned choice. Idempotence preserves E. The marked maximal types survive each
macro gate: the added sibling profile is Phi_h, whose exclusion is already
the marked factor M_(j,h). Therefore the resulting term attains the right
side of (6) for all sources and observers simultaneously.

It follows that

    C^greatest_(j,k)(E)=AND_(r!=k) NOT Phi_r(E_r)           (7)

is the greatest term-induced free extension. The same expression is the
greatest arbitrary antitone extension of (2). If it is false at an
independent flag tuple, some owner r has Phi_r(E_r)=true. Erase all
other owners' flags. This is a one-hot tuple below the original one,
and its coefficient is false by (2). Antitonicity forces every extension
to be false at the original tuple. If (7) is true, no Boolean extension
can exceed it.

This is a greatest extension, not a uniqueness or least-extension claim.
Already binary input union is a profile maximum, and its term-induced
free extensions have no least element; the symbolic six-bit proof is in
[free-polarization-extrema.md](free-polarization/free-polarization-extrema.md).
Thus a canonical greatest extension and many other term-induced
extensions can coexist.

## Where the general obstruction remains

The [quota normal form](quota-normal-form.md) is a more explicit subclass
of this result. It supplies pivot-once recursive words, exact cardinality
prime guards, and word/circuit size formulas. The argument here instead
works for every admissible profile tuple, gives source-linear minorants
for its maximal vectors, and classifies all its maximum's sound full types.

For a general core operation F, a sound type need not satisfy owner-shadow
or drift compatibility, and need not occur in any realizer. The sample
F=(X choice_r Y) union Z from
[source-type-pruning.md](source-type-pruning.md) lies outside the present
class: at distinct singleton inputs X={r},Y={s},Z={t}, it returns
{r,t}, an ambiguous proper subset of the full input union. Completion
(5) can then add the omitted s and cannot be used to restore F.

Likewise the global source-guard problem cannot be replaced by the type
criterion (4) for arbitrary functions below their profile maxima. The
theorem identifies a broad regime in which independent owner completion
is integrable, and precisely the semantic property used to make it so.
