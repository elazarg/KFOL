# Five-variable terminal obstruction beyond identity-stable feedback

Written mathematics, not a Lean claim. The complete proofs are
`core:thm:terminal-separable-obstruction` in
[appendix-core-terminal-obstruction.tex](../../../sections/appendix-core-terminal-obstruction.tex)
and `core:thm:identity-stable-feedback` in
[appendix-core-feedback.tex](../../../sections/appendix-core-feedback.tex).
The unrestricted joint-guard characterization remains unresolved.

## Explicit operation

Fix distinct owners a,b,c. On four passive inputs put

    D=(x choice_b y) choice_a (x choice_b z) choice_a (y choice_b z);
    C=D choice_a t.

D is the greatest profile completion with majority-2 profiles at a,b
and unanimity at the other owners. C is a genuine separable core baseline.
Define F(X,w)=C(w) when y=z=t=c, and C(w) union X otherwise.
Its new source is a sink with one owner box, not(y_c z_c t_c).

The passive closures are

    c_a(E)=W if t in E or |E intersect {x,y,z}|>=2, else E;
    c_b(E)={x,y,z} union (E intersect {t})
           if |E intersect {x,y,z}|>=2, else E;
    c_s(E)=E for all other owners.

The terminal extension adds X to c_c(E) precisely when {y,z,t} is
contained in E; it changes no passive closure. Both terminal subset laws
hold: a coalition disjoint from {y,z,t} is contained in {x}, which every
old closure fixes. Hence F has full colored-cofactor independence.
Every proper nonempty neutral residual is core.

## Why no term can realize even the pure ports

Suppose a core T bounded by F supplies c at X=c and all passives=a.
Marked linearization gives a one-X spine S bounded by T+partial_X T,
hence bounded by F. Its passive helpers are all a on that diagonal, so
S has no a-owned gate. At any C=a valuation, putting X=a gives S=a;
therefore every helper inherits all positive a-profile bits of C.
In particular it is a-positive on {x,y} and on {t}.

The pure-c negative trigger with X=a forces a c-owned helper G whose
c-profile is positive on {y,z,t}. At

    (x,y,z,t)=(b,a,b,{b,c}),   X={b,c},

C=F={b,c}. The positive quorums a:{x,y} and c:{y,z,t} force a in G:
their intersection is {y}, its menu is a, and the c-atomic set is empty.
This is the exact one-bound profile criterion.
But every helper's a-winning coalition {t} excludes a foreign-owner
winning coalition omitting t. Since t is ambiguous at this row, no
helper can absorb at any spine gate. The prefix starts ambiguous and
all gates union, so G's a leaks to the root, a contradiction.

Any pure-port realizer lies below its separable hull F, while its new
source port at the all-a probe must supply c. Thus the closure tuple
has no joint core realizer, including nonseparable ones.

## Why every identity-extension feedback test still passes

A proper closed support inherits feedback from its core proper neutral
residual. Only full-span independent bases require a check.

- Observer a: the bases are {t,X} or J union {X}, where J is an old
  triangle pair. The b-conditional closure acts only on old base elements
  and ignores X; the c-conditional closure only adds X from a nonempty
  old premise. These loopless closures have no disjoint mutual capture.
- Observer b: the bases are J union {t,X}; the same argument applies
  with a as the old-element closure.
- Observer c: the base is the old passive support, and the foreign
  closures are exactly those of the genuine baseline C.
- An identity observer has the whole support as its only full-span base.
  A b-query head has at most one triangle point; a c-query head is X
  and needs y,z,t. An a-query without t in its premise needs at least
  two triangle premises, so its rainbow cover by at most one b-head
  and one c-head is impossible. Hence no head can contain t, eliminating
  c-queries, then a-queries, then b-queries.

Identity-colored queries have empty disjoint heads and cannot assist
any cover. Thus the same proof works after every unused-owner extension.
