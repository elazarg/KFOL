# Two reciprocal capture rules and a prime separable obstruction

Mathematical research, without Lean claims or term enumeration. Two
reciprocal capture rules have an exact common-context criterion below;
families of such rules have an exact cross-intersection criterion.
For every finite owner set with at least three owners, four variables
give the same source-separable noncore operation with loopless owner
closures, every colored-closure idempotence, admissible
spanning profiles on every restriction, and omission independence on every
neutral restriction. Every proper neutral face and every proper
identification minor is core. The operation is also prime under proper
disjoint idempotent factorization.

An analytic three-row source-persistence law excludes a realization. Thus
the failure is joint guard compatibility, despite all the hereditary
closure/profile/omission conditions and core proper input reductions.

Fix finite I containing distinct owners 0,1,2. Digits
in valuation tuples mean singleton menus; 01 means {0,1}, and similarly
for other digit strings. Put N_2=I\{2}. All core
words use primitive I-owned choices without constants or role switches.
Derived union is used as a core abbreviation.

## A common-context criterion for two reciprocal rules

First allow any finite nonempty variable set V with distinct heads x,y,
and put U=V\{x,y}. Choose context sets L,M subseteq U. Define

    d_0(E)=E union ({y} if L union {x} subseteq E else empty);
    d_1(E)=E union ({x} if M union {y} subseteq E else empty);
    d_r(E)=E for all other owners.

These are loopless closures. Let G be their raw source reconstruction,
initially permitting empty values:

    k in G(w) iff some j with k in w_j is outside
                           UNION_(r!=k) d_r(E_r(w)).

Every context input is unconditional; only x can be captured by owner 1
and only y by owner 0.

**Two-rule characterization.** G is a core operation if and only if
L intersect M is nonempty.

### A shared context gives a realizing normal form

Suppose z belongs to L intersect M. Define

    S_y=y choice_0 (FOLD_choice_1_(i in L union {x}) x_i);
    S_x=x choice_1 (FOLD_choice_0_(i in M union {y}) x_i).

The occurrence of y in S_y is unique. Its full vector has precisely the
canonical factor NOT(L union {x} subseteq E_0), with every other factor
true. In S_y the only auxiliary head is x. If its target owner-1 factor
fails, all M union {y} are 1 atoms. In particular the shared context
z is 1, so the inner choice_1 fold absorbs to 1 and blocks every non-1
contribution from x. Winner 1 is already supplied unconditionally by z.
Thus this auxiliary occurrence is sound for G. Context occurrences are
always sound because their whole menus belong to G. Hence S_y<=G.
The symmetric argument gives S_x<=G, with its unique x occurrence
attaining x's whole canonical vector.

Consequently

    G=UNION_(i in U) x_i union S_x union S_y.

The right side is contained in G by the preceding occurrence bounds.
Conversely each possible source is covered with its exact canonical
factors: context sources by their projections and the heads by their
marked spines. This proves equality and core realizability. Every fold
is nonempty, including the context union because a shared context exists.
The same proof applies with any distinct owners in place of 0,1.

Each source therefore has a source-linear minorant with its canonical
full vector. Marked-union restoration and primitive coextension, as in
[the additive construction](additive-closure-characterization.md), make
all these maximal types actual simultaneously in one G realizer. Thus
this class also attains its greatest independent-flag product completion
and its canonical common-carrier extension. The raw union abbreviation
alone is not asserted to preserve those marked types.

### Disjoint contexts give a three-row obstruction

Suppose L intersect M is empty. With N_2=I\{2}, use these rows, assigning
all inputs in each context group the displayed menu:

| Row | L | x | y | M | Other context inputs |
|---|---|---|---|---|---|
| u | N_2 | 2 | 1 | 1 | 0 |
| v | 0 | 0 | 2 | N_2 | 0 |
| q | 0 | 2 | N_2 | 1 | 0 |

The rows are consistent exactly because the contexts are disjoint.
They are genuine canonical source probes at observer 2: u and q have
source x, while v has source y.

**Persistence lemma.** Every core term satisfies

    2 in output(q) implies 2 in output(u) or output(v).

To prove it, use the observer-2 values 0,1,N,P: singleton 0 or 1 keeps
its atom, every other menu omitting 2 maps to N, and a 2-containing
menu maps to P. Choice 0 is minimum in 0<P<N<1, choice 1 maximum in
0<N<P<1, and choice 2 is flat union, with P absorbing and 0 union 1=N.
No extra owner has a singleton input on these rows. The singleton-profile
recursion prevents its singleton at every subterm, so any extra owner's
gate also acts as union on all three rows.

A pure term uses only choices 0,1 and has a monotone Boolean function f,
with these choices interpreted as AND,OR. Its lower Boolean corner is
the set of fixed 1 positions and its upper corner all positions not fixed
to 0. The corner maps are homomorphisms: a Boolean-constant cube gives
the same stable output 0 or 1. A P-marked coordinate essential for f on
the cube forces output P. Indeed put P on an essential Boolean edge and
fix the other inputs to that edge; its output is P on the three-chain
0<P<1. Increasing the other free inputs from Boolean atoms to N/P in
flat-union order preserves P, by monotonicity and P being its top.

Thus a pure term with no P at u has its x coordinate inessential on
that cube. Fix all L inputs to 0 to obtain

    f(M union {y})=f(M union {x,y}).

No P at v makes y inessential; fixing all M inputs to 1 gives

    f(M)=f(M union {y}).

These equalities identify q's lower and upper Boolean corners. The pure
term's q-output is therefore stable 0 or 1. Every full term expands into
a finite nonempty flat union of pure terms, since choices 0,1 distribute
over union. If its u,v outputs omit P, every pure summand omits P there,
so every summand is stable at q. Their union cannot contain P, proving
the lemma for arbitrary terms.

The raw G violates this law. At u owner 1 captures the only 2-source x;
at v owner 0 captures the only 2-source y. At q neither rule captures x,
so 2 survives from it. All other inputs omit 2. This proves noncoreness
for disjoint contexts, including empty-context cases. When L=M=empty
and U is empty, G can even have an empty value; no nonemptiness assertion
is made in this negative case. The two-rule characterization is proved.

## Families of reciprocal rules

The same classification extends to arbitrarily many rules at each of
the two owners. Let nonempty families of contexts Lcal,Mcal consist
of subsets of U=V\{x,y}, and define

    l(E)=[some L in Lcal satisfies L subseteq E];
    m(E)=[some M in Mcal satisfies M subseteq E];
    d_0(E)=E union ({y} if x in E and l(E) else empty);
    d_1(E)=E union ({x} if y in E and m(E) else empty).

Other closures are identities. Let G be their raw separable reconstruction.
Then

    G is core iff L intersect M is nonempty
                   for EVERY L in Lcal, M in Mcal.     (F)

For necessity, a disjoint L,M violates the reciprocal-cut law (C2):
the two full premises capture their opposite heads, while contexts
alone capture neither. The three-row proof above gives the same
contradiction directly. Additional rules cannot restore a suppressed
source at the two negative rows, and at the positive row both head
prerequisites are non-atomic, so neither family captures a head.

For sufficiency prescribe a sibling B_y on V\{y} with profiles

    Phi_0(E)=[x in E and l(E)];
    Phi_1(E)=m(E);
    Phi_r(E)=[E=V\{y}] for all other owners r.

These are normalized monotone profiles. Their rainbow common-source
condition is precisely (F): a minimal 0-coalition is {x} union L,
a minimal 1-coalition is M, and their intersection is L intersect M.
The singleton-profile theorem therefore constructs B_y. Put

    S_y=y choice_0 B_y.

Its marked y has the exact canonical full vector: its only filter
is NOT(x in E_0 and l(E_0)). Context sources from B_y are always
safe. Its only other head x is safe too: if x is captured in G,
then y={1} and m(E_1) holds, making B_y={1}; hence S_y={1} and
no incorrect x-contribution escapes. This proves S_y<=G.

Symmetrically synthesize B_x on V\{x} with owner-1 profile
[y in E and m(E)], owner-0 profile l(E), and unanimity at other
owners. Then S_x=x choice_1 B_x is a minorant with x's canonical
vector. Consequently

    G=UNION_(i in U) x_i union S_x union S_y.

Every context is nonempty under (F), so the context union is present.
Marked-union restoration and coextension give simultaneous greatest
full types, the greatest independent-flag product completion, and
the common-carrier maximum exactly as in the single-rule case.

Thus pairwise cross-intersection completely solves this two-head
family, even with unbounded numbers of minimal captures. It does not
extend to arbitrary sets of heads: the
[three-owner obstruction](three-owner-exchange.md) passes all reciprocal
pair tests and fails a higher feedback-elimination law.

## The greatest core minorant for nonempty contexts

Assume now that both L and M are nonempty; they need not be disjoint.
There is an explicit greatest core operation below the raw reconstruction
G. Put

    Lbar=FOLD_choice_1_(i in L) x_i;
    Mbar=FOLD_choice_0_(i in M) x_i;
    Z=UNION_(i in U) x_i.

Thus the 0-profile of Lbar is l=[all L inputs are 0], and the 1-profile
of Mbar is m=[all M inputs are 1]. Define the core word

    R=Z union (x choice_1 Mbar) union (y choice_0 Lbar)
        union ((x choice_1 y) choice_0 Lbar)
        union ((y choice_0 x) choice_1 Mbar).             (R)

Every displayed term is contained in G. Context sources are unconditional.
In the first head term the 1-filter NOT m is stronger than x's target
filter NOT(m AND y_1); the second term is symmetric. In the third term,
x's 1-filter excludes y_1 and y's 0-filter excludes l, both stronger
than their respective target filters. The fourth term is symmetric.
These occurrence bounds prove R<=G.

More precisely, at an observer k outside {0,1}, its head coefficients are

    C_x,k=NOT m OR (NOT y_1 AND NOT l)
         =NOT(m AND y_1) AND NOT(l AND m);
    C_y,k=NOT l OR (NOT x_0 AND NOT m)
         =NOT(l AND x_0) AND NOT(l AND m).

At observers 0,1 the own-owner filters are omitted, and their coefficients
are unchanged from G. Hence

    R(w)=Z(w) if all L inputs are 0 and all M inputs are 1;
         G(w) otherwise.                                (R-value)

On the first case Z already contains both 0 and 1 because L,M are
nonempty, so their own-observer bits are masked by the context union.
If L and M intersect, that case is impossible and R=G.

**Greatest-minorant theorem.** Every core operation S<=G satisfies S<=R.
Thus (R) is the greatest core minorant, not merely a chosen repair.

It is enough to consider a bad context in (R-value) and a winner k outside
Z(w). Such k differs from 0,1. Enlarge both head inputs to I, and enlarge
every context input outside L union M to N_k=I\{k}. These are input
enlargements because the unused context menus omit k. Core inclusion
monotonicity would retain any k originally supplied by S.

Neutralize the unused context variables. The resulting S' is core or
zero, by core neutral elimination, and S'<=G' on L union M union {x,y}
by the winnerwise definition of neutral residuals. The two negative
persistence rows u,v for G' omit k. Both enlarged heads are ambiguous,
so extra-owner gates still act as union. The same Boolean endpoint
argument used above therefore also forbids k when both free heads are P: its
cube has the same endpoints M and M union {x,y}, regardless of whether
the second head is N or P. The zero residual satisfies this conclusion
too. Thus S' has no k at the enlarged row, contradicting monotone
retention from w. No winner outside Z(w) can be supplied by S there,
which proves S<=R.

Finally R retains every pure-owner port of G. In a pure-1 probe l=false
because L is nonempty, so the x coefficient reduces to NOT(m AND y_1),
its original port. In a pure-0 probe m=false because M is nonempty,
so x is unfiltered, again as in G. The y calculation is symmetric;
context ports stay unconditional. The singleton profiles also agree:
(R-value) changes outputs only where the context already contains 0,1.

Consequently G is exactly the separable upper hull of the genuine core
word R. For disjoint nonempty contexts this hull is not core. The
specialization below gives this failure on four variables for every
K>=3, including three owners. See also
[separable-hull-failure.md](separable-hull-failure.md).

## A uniform prime instance

Now return to V={A,B,C,W}, and take x=B, y=C, L={A}, M={W}.
The contexts are disjoint, so the theorem already excludes a core
realization. The remaining sections verify the stronger hereditary,
minor, and primeness properties of this particular instance.

## Two nonadditive owner closures and their guards

Define

    c_0(E)=E union ({C} if {A,B} subseteq E else empty);
    c_1(E)=E union ({B} if {C,W} subseteq E else empty);
    c_r(E)=E for every r outside {0,1}.                  (1)

These maps are extensive, monotone, loopless, and idempotent. Each adds
one head whose presence cannot enable a further application of that same
rule. They are nonadditive: for example C belongs to c_0({A,B}) but not
to c_0({A}) union c_0({B}).

Take their source-separable reconstruction

    k in F(w) iff some j with k in w_j is outside
                           UNION_(r!=k) c_r(E_r(w)),
    E_r(w)={i:w_i={r}}.                                  (2)

The anchors A,W are never generated by any foreign closure, so their
whole menus always survive. The only possible suppressions are B by
owner 1 and C by owner 0. Their same-owner residual contributions are
already supplied by the anchors. Thus (2) has the elementary full formula

    F=A union W
        union (B if NOT(C=W={1}) else empty)
        union (C if NOT(A=B={0}) else empty).             (3)

The two suppressions may occur together; their residual winners are then
still supplied by A={0} and W={1}.

Pure-owner source probes recover exactly the closures (1). Their ports
are all true except

    D_(B,1)(E)=NOT({C,W} subseteq E);
    D_(C,0)(E)=NOT({A,B} subseteq E).                     (4)

Consequently the canonical prime source guards are explicit. At sources
A,W every observer has the empty guard. At B, observer 1 has the empty
guard, while observers 0,2 have the two alternatives [C!={1}] and
[W!={1}]. At C, observer 0 has the empty guard, while observers 1,2
have alternatives [A!={0}] and [B!={0}]. These are genuine normalized
monotone source coefficients and reconstruct (3).

These are also the actual
[cofactor-dependence closures](cofactor-dependence-closures.md) of this
synthetic operation. Fixing A=B=0 makes the whole output 0 union W,
independently of C: suppressing B cannot matter because A already
supplies 0. Fixing C=W=1 similarly makes the output A union 1,
independently of B. These prove all nontrivial closure consequences.
Conversely, when a pure port is true, varying its marked input from
{k} to I\{k} changes the k-bit by source reconstruction and
conservativity. Every input outside the displayed closure is therefore
essential in that monochromatic cofactor.

Thus even this full functional-dependence interpretation holds. It also
gives full old-value outcast: every canonically blocked ambiguous input
is inessential under its capturing atomic coalition, so simultaneous
arbitrary menu changes there preserve F. Source separation then gives
the atomic-survivor outcast of
[mixed-closure-outcast.md](mixed-closure-outcast.md). Neither condition
detects the three-row obstruction below.

## Every colored union is a closure

For a full coloring alpha:V->I put

    d_alpha(T)=UNION_r c_r(T intersect alpha^(-1)(r)).

Its only possible new points are C from 0-colored A,B and B from
1-colored C,W. If a newly added C activates the second rule, its
consequence B was already a seed of the first rule. If a newly added
B activates the first rule, its consequence C was already a seed of
the second. A second application therefore adds no new point. Every
d_alpha is extensive, monotone, empty-preserving, and idempotent.

By [the colored-closure equivalence](mixed-closure-outcast.md), the full
Q-outcast law holds, including initially saturated patterns. The equivalent
pair-cut law holds as well:

    r!=s, A_0 intersect B_0=empty, i outside A_0 union B_0,
    i in c_r(A_0)
       implies c_s(B_0 union {i})
                    subseteq c_r(A_0) union c_s(B_0).

Here A_0,B_0 denote arbitrary premise sets, not winner menus or the
named input A. In this example the implication is also immediate:
each rule's new head is already a premise of the other rule.

Strong source attribution follows directly. If ambiguous B is singly
shadowed, it is shadowed by owner 1 because C=W=1, and free anchor W
already supplies 1. If ambiguous C is singly shadowed, A=B=0 and free
anchor A supplies 0. The anchors themselves have no ambiguous shadow.

## Exact profiles and omission independence

Formula (3) makes F nonempty and gives its exact singleton predicates

    Phi_0(E)=[{A,B,W} subseteq E];
    Phi_1(E)=[{A,C,W} subseteq E];
    Phi_r(E)=[E=V] for r outside {0,1}.                  (5)

Indeed a singleton output forces A=W=r. The operation at those fixed
anchor values is the following core polynomial in B,C:

    A=W=0:  0 union B union (B choice_0 C);
    A=W=1:  1 union C union (B choice_1 C);
    A=W=r, r outside {0,1}: r union B union C.           (6)

The first is singleton 0 exactly when B=0, the second singleton 1
exactly when C=1, and the last singleton r exactly when B=C=r.
This proves (5), including the full atomic-profile law
F={r} iff c_r(E_r)=V. Its profiles are admissible: every winning
coalition in (5) contains both A and W.

**Omission lemma.** F satisfies global omission independence.

Suppose F(w) omits k. Every k-containing input j is captured by some
foreign owner r!=k, by the product source formula (2). The original
r-atomic inputs omit k, so they stay fixed under all permitted changes.
The cofactor-dependence property proved above makes j inessential
uniformly while those atomic inputs remain fixed. Apply this to the
changed coordinates one at a time. It preserves the entire output,
not only the absence of k. This proves omission independence for every
ambient K>=3, without an assumption that the anchors cover all other
winners.

## All proper neutral faces are core

For a retained variable set U, the winnerwise neutral residual is defined
by putting I\{k} outside U when querying winner k. Those outside inputs
are ambiguous and omit k. Formula (2) therefore shows directly that this
residual is the source reconstruction of c_r restricted to U. No core
assumption on F is needed for this calculation.

Deleting any one variable gives the following core words:

| Retained variables | Neutral residual |
|---|---|
| A,B,C | A union B union (C choice_0 (A choice_1 B)) |
| B,C,W | C union W union (B choice_1 (C choice_0 W)) |
| A,C,W | A union C union W |
| A,B,W | A union B union W |

For the first row, A choice_1 B is the 0 singleton exactly when
A=B=0. Otherwise its contribution is covered by A union B, and the
outer expression retains C. This is precisely the first closure rule
alone. The second row is the owner-swapped counterpart. The last two
rows have no surviving closure rule. On every set of at most two retained
variables all closures are identities, so the residual is input union.
Singleton faces are projections; the empty face is zero.

Thus every proper nonempty neutral restriction is a genuine core
operation, and every nonempty neutral restriction is nonempty. Every
restricted spanning-profile tuple is admissible: proper ones come from
these words, and the full tuple is (5). Omission independence holds on
every neutral restriction, by the omission lemma for the full operation
and core realizability for all proper ones.

## Hereditary span-outcast also holds

For the full variable set, a blocked restoration cannot change the atomic
statuses of A,W. They are free whenever ambiguous and hence cannot be
restored as blocked positions; atomic anchors stay fixed.

A new owner-0 span would require A=W=0 already and B to be restored
to 0. But ambiguous B can be blocked only when C=W=1, incompatible
with W=0. A new owner-1 span similarly requires A=W=1 and a blocked
C, whereas C can be blocked only if A=B=0. A new span at an owner r outside {0,1} would
require every remaining position to become r. With A=W=r neither
nontrivial rule can block an ambiguous position, so that cannot occur.
Existing spans persist by monotonicity. This proves full span-outcast.

Proper neutral restrictions are core, so the law holds on them as well.
Equivalently the hereditary mixed-loop coalition test holds:

    r!=s, A_0 intersect B_0=empty, i outside A_0 union B_0,
    i in c_r(A_0), A_0 subseteq c_s(B_0 union {i})
       implies i in c_s(B_0).

Thus neither the pair-cut nor the hereditary mixed-loop formulation
detects this obstruction.

## The three canonical witness rows

The general persistence lemma specializes to

    u=(N,P,1,1),   v=(0,0,P,N),   q=(0,P,N,1)

in the observer-2 view and variable order A,B,C,W. The actual values are

| Row | A | B | C | W | F |
|---|---|---|---|---|---|
| u | N_2 | 2 | 1 | 1 | N_2 |
| v | 0 | 0 | 2 | N_2 | N_2 |
| q | 0 | 2 | N_2 | 1 | I |

Formula (3) gives these values directly. They violate persistence for
every fixed K>=3. Each row is a genuine canonical source probe at
observer 2: u and q have source B, and v has source C. Thus a positive
q guard bit must force one of the u,v bits positive for every term,
whereas F's guard bits are respectively positive, negative, negative.
No finite term-table enumeration is assumed in that universal law.

## Every proper identification minor is core

Five identifications have these explicit core words:

| Identification | Minor |
|---|---|
| A=B=U | U union W union (C choice_0 U) |
| C=W=U | A union U union (B choice_1 U) |
| A=C=U | U union W union (B choice_1 (U choice_0 W)) |
| B=W=U | A union U union (C choice_0 (A choice_1 U)) |
| B=C=U | A union U union W |

They follow from (3): an identified anchor restores its copied input,
and the remaining single suppression has the displayed one-owner word.
When B=C, one of the two copies always survives, giving full union.

For the sixth identification A=W=U, the minor is

    0 if U=B=0;
    1 if U=C=1;
    U union B union C otherwise.                        (9)

The contexts now share U. The positive construction above gives the
explicit core word

    U union (B choice_1 (U choice_0 C))
      union (C choice_0 (U choice_1 B)).                 (10)

This has value (9), either by the common-context theorem or by the
three cases in (9). Every further identification is a minor of one of
these words, so every proper identification minor is core.

## Support, provenance, and disjoint primeness

The operation is inclusion-monotone. Enlarging a menu removes rival
singleton flags and adds membership; the antitone closure filters in
(2) cannot turn a surviving contribution off. It is idempotent because
it is conservative and contains the full anchor menu A on a diagonal.
Formula (3) supplies whole-input provenance: every output winner is
covered by one of the whole input menus retained in that formula.

On all-ambiguous inputs every closure seed is empty, so F is full input
union. Every variable is therefore essential: put the other inputs at
I\{k} and vary the selected one from I\{k} to I, keeping every input
ambiguous. Its k-bit changes.

Suppose F had a proper disjoint idempotent decomposition through a
partition of V into between two and three nonempty blocks. Its outer
operation is the block-diagonal identification minor, hence core by the
preceding section. It uses every block essentially because F has full
support. The [canonical factor-recovery theorem](block-decomposition.md)
then identifies each inner factor with the corresponding proper neutral
face, which is core. This recovery only requires the outer operation
core and the inner operations idempotent; it does not assume F core.
Composition would make F core, contradicting (8). Thus no such proper
disjoint idempotent decomposition exists.

## The individual type tests and the common-carrier candidate

At each source j the canonical full vector

    B^(j)_r(E)=[j notin c_r(E)]

is normalized, sound, and satisfies owner-shadow because c_r is a closure.
Its products are exactly the source coefficients, so these four vectors
cover all positive guard bits. They also obey all-owner side effects:
the only nontrivial ambiguous failures are C shadowed by 0, with free
anchor A=0, and B shadowed by 1, with free anchor W=1. For atomic
sources either their own winner survives or a foreign capturing rule's
anchor supplies an owner in the failed set. Causal drift is a special
case. Thus all these individual-type necessary tests pass, without a
common core realization. This does not refute a conditional actual-type
theorem assuming an independently known core target.

The canonical common-carrier G_Q also has the structural properties in
[canonical-separable-extension.md](canonical-separable-extension.md): it
is flat-order monotone, agrees with the synthetic old observer faces,
and preserves the full ternary outcast invariant, by Q- and span-outcast.
It cannot be term-induced, since its old faces would then realize F.
The faces here are synthetic restrictions; no claim that all those
common-carrier faces are core is needed.

The example disproves sufficiency of hereditary spanning-profile
admissibility, all colored-closure idempotences, hereditary omission,
hereditary span-outcast, and core proper neutral faces, even together
with core proper identification minors. It is a prime nonadditive
source-separable obstruction. The full intrinsic joint guard criterion
therefore needs compatibility beyond these closed hereditary laws.
