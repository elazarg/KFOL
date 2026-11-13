# Complete-head circuits: realizability and a failure of maximal types

Mathematical research, without Lean claims. This family has an exact
all-arity classification, an explicit greatest core minorant, and a sharp
failure of maximal occurrence-type attainment. In particular a genuine
source-separable operation need not have a greatest full occurrence type
at a source. The canonical common-carrier completion can fail to be
term-induced even when the original operation is core.

## The family and its greatest core minorant

Let I be a finite owner set with K>=3. Take n>=2 distinct owners r_i
and heads h_i, with H={h_1,...,h_n}. Let A be a disjoint finite
**nonempty** set of unconditional anchor inputs. For each i choose a
context L_i subseteq A, allowing empty contexts. The anchor assumption
ensures that the functions below always have nonempty winner sets,
including when every context is empty. The closures have just these
nontrivial captures:

    (H\{h_i}) union L_i =>_(r_i) h_i.                (1)

Each closure adds only its own head; all other owner closures are
identities. Their source-separable reconstruction is

    F(w)=UNION_(a in A) w_a
          union UNION_i (w_(h_i) unless
               every input in (H\{h_i}) union L_i
               is the r_i singleton).               (2)

The anchors make this nonempty. Write Z(w)=UNION_(a in A) w_a and

    bad(w) iff every L_i consists of r_i atoms.      (3)

The following function is the greatest core operation below F:

    R(w)=Z(w) if bad(w), and F(w) otherwise.         (4)

Thus the classification is

    F is core iff {r_i:L_i is nonempty}=I
                 OR some L_i intersect L_j != empty
                    for distinct i,j.               (5)

In particular disjoint contexts are realizable exactly when every
owner has a head with a nonempty context. Disjoint nonempty contexts
lose realizability after adding an observing owner. Any one context
overlap makes the operation core for every
ambient owner set containing the head owners; the context-intersection
graph need not be connected.

### Short safe spines

For p, an anchor a in L_p, and an ordered list J of at most two distinct
head indices other than p, form T_(p,J,a): start at h_p, attach each
h_j in order using choice_(r_j), and finally attach a using choice_(r_p).
These words have at most four leaves. Let R_0 be their union together
with every anchor projection.

Each word is below F. If rule p fires, the final anchor is r_p and
absorbs the entire prefix. Otherwise h_p survives. If a listed head
h_j is suppressed, all preceding heads are r_j, so their prefix is
r_j. Attaching h_j at owner r_j absorbs its possibly unsafe menu.
Every later listed head is also r_j, and this winner is safe because
it occurs in the surviving h_p. The final anchor is unconditional.
If no listed head is suppressed, every input used by the word is
already safe. This argument also covers simultaneous triggers when
n=2; a suppressed head absent from the word contributes nothing.

At a bad valuation every such word ends in its absorbing own-owner
anchor, so R_0=Z. At any other valuation choose p and a in L_p with
w_a!={r_p}. A winner already in an anchor is supplied directly.
Otherwise let k be a winner of F outside Z, supplied by an unsuppressed
head h_i.

If some b in L_i is not {r_i}, the direct word h_i choice_(r_i) b
retains k. Here k!=r_i if that distinction is needed; if k=r_i the
owned operation retains it automatically. Otherwise all L_i are
r_i atoms. Since h_i is not suppressed, some other head differs
from {r_i}.

If p=i, the chosen off-owner anchor already gives the direct word.
If p!=i and w_(h_p)!={r_i}, use

    (h_p choice_(r_i) h_i) choice_(r_p) a.

If instead w_(h_p)={r_i}, choose j different from i,p with
w_(h_j)!={r_i}, and use

    ((h_p choice_(r_j) h_j) choice_(r_i) h_i)
                                      choice_(r_p) a.

The first prefix is not {r_i}: either its r_j operation absorbs to
r_j, or it includes a non-r_i winner from h_j. Thus attaching h_i
does not erase k. The final operation cannot erase k either, since
its anchor is not its owned singleton; if k=r_p, absorption would
retain k anyway. This proves R_0=F off bad and hence R_0=R everywhere.

There are at most

    sum_p |L_p| * (1+(n-1)+(n-1)(n-2))

short spines. Derived union is available because K>=3. This gives
a polynomial-size circuit; no exhaustive term generation is used.

If a pair of contexts intersects, bad is impossible. If the owners
of the nonempty contexts exhaust I, bad implies Z=I, so F=R there
as well. These prove the positive directions of (5).

### A uniform observer obstruction

Assume the contexts are pairwise disjoint. Add a fresh owner omega,
write J=I union {omega} and N=I, and interpret any old-owner word on
this enlarged carrier. Use n negative rows u_i and one query q:

* At u_i put J on h_i, {r_i} on every other head and on L_i,
  and N on every other anchor.
* At q put J on every head, {r_i} on L_i, and N on anchors outside
  all the contexts.

For a word T write U_i=T(u_i) and Q=T(q). Each U_i belongs to
{{r_i},N,J}. At q a value without omega is an atom r_i or a union
of old atoms; a value containing omega is J. Other owners, including
omega, have no singleton input on any row and act as union at every
subword. An r_j gate acts as union on u_i whenever i!=j.

The following three simultaneous invariants hold for all core words:

    U_i={r_i}, U_j={r_j}, i!=j
        imply omega in some U_l with l outside {i,j};       (A)

    all U_l omit omega and U_i={r_i} imply Q={r_i};         (B)

    omega in Q implies omega in some U_i.                 (C)

A head projection h_i has U_i=J, U_j={r_j} for j!=i, and Q=J.
An anchor in L_i has U_i={r_i}, all other U_j=N, and Q={r_i}.
An unused anchor has every U_i=Q=N. These establish the leaf cases.

For (A), at a root i or j choose the child with that owned singleton;
both children have the other required singleton, and a witness at
any third row persists through the root. At a different head owner p,
both children have the two required singletons. Each has a witness
outside {i,j}. Any witness outside p persists. If both children have
only p as a witness, both U_p contain omega, so neither is {r_p}
and they cannot absorb one another. A root of any other owner is union.
For n=2 the conclusion has an empty index set, so (A) simply excludes
its pair of singleton premises.

For (B), at owner i choose a child with U_i={r_i}. Every other
negative row passes to that child, so induction gives its Q={r_i},
which absorbs at the root. At a different owner p both children have
U_i={r_i}, and every budget except possibly U_p passes to both. If
one U_p containing omega were erased by the sibling's U_p={r_p},
that sibling would satisfy (A) for i,p. Its witness outside {i,p}
contradicts a budget that already passed. Thus all budgets pass to
both children; both Q-values are {r_i}. Other owners act as union.

For (C), suppose Q contains omega and all U_i omit it. At owner p,
choose a child whose Q contains omega. Induction forces a witness
at U_p, since every other negative row passes. Erasing that witness
requires the sibling's U_p={r_p}. The sibling satisfies all negative
budgets, so (B) makes its Q={r_p}, which would erase omega at the
root query too. This is a contradiction. Other owners are union and
pass all the negative budgets. The simultaneous induction is complete.

### Greatestness with empty contexts

Let T be any core operation with T<=F, and extend its old-owner word
to J. Its enlarged outputs omit omega at every u_i. To see this,
choose an old observer s!=r_i. On the corresponding old source probe,
h_i={s}, all other heads and L_i are {r_i}, and the remaining anchors
are I\{s}. The function F suppresses h_i and omits s everywhere else,
so T omits s too. An occurrence supplying omega at u_i would have
all old-owner path factors true; omitting the s factor would then
supply s on this old probe, a contradiction. Thus (C) makes T(q)
omit omega. This argument does not require L_i to be nonempty.

Now take a bad old valuation w and k outside Z(w). A nonempty context
L_i has its atom r_i in Z(w), so r_i!=k. Empty contexts impose no
anchor atom. Decrease every unused anchor at q from I to I\{k},
leaving the heads J and the context atoms unchanged; call the result
q'. Inclusion monotonicity preserves omega-absence.

At q', k and omega belong to exactly the same input menus, namely
all heads. Neither has a singleton input. No subword can create either
singleton without one initially. Thus every old-owned gate treats
their membership identically: a k-owned gate acts as union, and every
other absorption removes both winners. Since omega is absent from
T(q'), k is absent as well. The original w is coordinatewise contained
in q', so monotonicity gives k notin T(w). Hence T(w) subseteq Z(w).
Off bad the bound T<=F=R suffices. This proves that (4) is the greatest
core minorant. If contexts overlap there are no bad valuations.

For the negative direction of (5), if the contexts are disjoint and
their nonempty-context owners do not exhaust I, choose k outside
that owner set. Give every head I, each context its own atom, and
each unused anchor I\{k}. This is bad and its anchor union omits k.
No rule fires because n>=2 and all heads are ambiguous, so F contains
k whereas R omits it. Therefore F is not core.

If at least two contexts are nonempty, R and F have the same pure-owner
ports and singleton profiles. A head-source monochromatic probe cannot
be bad: those contexts would require two different anchor atoms.
Anchor-source ports are unconditional in both functions, including a
probe where bad happens to hold. At bad both functions contain at least
two anchor owners, so their singleton profiles agree too. This assertion
is not made when fewer than two contexts are nonempty.

## Which pure closures are jointly realizable

The closure tuple (1) is the pure-owner data of some core operation
if and only if at least two contexts are nonempty. This asks only
for the ports, not necessarily for the separable reconstruction F.

With at least two nonempty contexts, R is the required realizer by
the pure-port agreement above. If at most one context is nonempty,
choose p so L_j is empty for every j!=p. Apply
[feedback elimination](three-owner-exchange.md) at observing owner r_p
with

    A_profile=(H\{h_p}) union L_p;
    X_j={h_j}, P_j=H\{h_j}, owner r_j, for j!=p.

Each displayed capture is required by (1), and their sets lie in
c_(r_p)(A_profile), which contains all heads. Their rainbow covers are

    A_profile intersect P_j=H\{h_p,h_j}
        subseteq UNION_(l!=p,j) X_l.

Feedback elimination therefore gives

    c_(r_p)(A_profile)=c_(r_p)(L_p).

The left side contains every head; the prescribed right side equals
L_p and contains none. This contradiction handles empty L_p as well.
Thus the strengthened feedback law exactly detects the nonrealizable
pure tuples in this family. General pure-port sufficiency remains open.

## A context overlap restores maximal full types

If some contexts overlap, every head's canonical full vector is actual,
including a head whose own context is isolated from all others.

First suppose L_i intersects L_j at a. Order the other heads as
v_1,...,v_m with v_m=j. Form the chain

    C=(...(h_(v_1) choice_(r_(v_1)) h_(v_2))
                    choice_(r_(v_2)) ...)
                    choice_(r_(v_m)) a,

where for m=1 this is h_j choice_(r_j) a. Union C with all the
anchor projections in L_i to form G_i, and put

    S_i=h_i choice_(r_i) G_i.

Every inner owner is foreign to r_i, so Phi_(r_i)(G_i) is exactly
conjunction of (H\{h_i}) union L_i. Each auxiliary head in C is
protected against its own capture by the next head in the chain;
the final head is protected by shared anchor a. Thus S_i<=F and
its unique h_i occurrence has the canonical full vector.

If i is isolated, choose an edge j-k with a in L_j intersect L_k.
Let D be the four-input circuit operation on h_i,h_j,h_k,a with
contexts empty,{a},{a}, respectively. By (5) it is core because its
two nonempty contexts overlap. Its profiles are

    Phi_(r_i)=h_j h_k a;
    Phi_(r_j)=h_i h_k a;
    Phi_(r_k)=h_i h_j a.

Choose B_i with owner-r_i profile conjunction of its premise, for example
a fold of that premise at any foreign owner. Start at marked
h_i choice_(r_i) B_i. For each l outside {i,j,k}, append at owner r_l
the sibling h_i choice_(r_i) h_j. Then append D at owner r_j and again
at owner r_k.

Under rule i, D contains only r_i and the safe anchor a. Under rules
j,k it is exactly r_j,r_k, respectively, so the corresponding final
stage absorbs any unsafe head contribution. Under any other rule l,
the early l stage already absorbed, and D adds only r_l and a.
Thus the whole word is below F. Both appended profiles at r_j,r_k
require h_i, so they are false on the marked-source-not-owner probe.
The early foreign profiles likewise require h_i. The marked full
vector therefore has only the required r_i factor. Restoration and
coextension give actual maximal types simultaneously at all sources.
The repeated marked label is sometimes necessary: with three heads,
L_i={a} and L_j=L_k={b}, no source-linear minorant attains i's maximal
vector, and every F realizer repeats h_i. The
[isolated-head theorem](isolated-head-source-linearity.md) proves this
using the two-query feedback lemma.

## A genuine separable operation without greatest full types

Now let the head owners exhaust I, with K=n>=3, and take pairwise
disjoint nonempty contexts. By (5), F is a genuine core operation.
At head h_i its canonical full factor vector is

    B_(r_i)(E)=NOT[(H\{h_i}) union L_i subseteq E];
    B_s=true for every s!=r_i.                       (6)

**No marked occurrence in any F realizer has vector (6).** Extend
the same syntax to the owner set I union {omega}. The pure ports
are unchanged: only atom-status profiles determine them. Therefore
the extended word omits omega at all the negative rows u_i above.
At q, however, all heads are ambiguous and only the contexts have
atomic statuses. Every factor of (6) is true: the r_i premise
requires other heads as atoms, and all its foreign factors are true.
A marked occurrence with vector (6) would emit omega at q, violating
(C). This argument handles repeated occurrences of h_i in siblings;
it does not assume a monochromatic marked path.

There are explicit actual types whose coordinatewise join is this
nonactual vector. Choose j!=i and a_j in L_j. Let B_i be a fold
of (H\{h_i}) union L_i at any owner other than r_i, so its r_i
profile is conjunction of that whole premise. Start at

    h_i choice_(r_i) B_i,

marking the initial h_i. For every l outside {i,j}, append at owner
r_l the sibling h_i choice_(r_i) h_j. Finally append at owner r_j
the sibling

    (h_i choice_(r_i) h_j) choice_(r_j) a_j.          (7)

This word is below F. Under rule i, its initial part and intermediate
siblings are r_i, and the final sibling adds only that safe owner and
an unconditional anchor. Under rule l outside {i,j}, the l stage
absorbs to r_l; later siblings use only r_l and anchors. Under rule j,
the final anchor makes (7) the r_j singleton and the last gate absorbs.
If no rule fires, F is the whole input union. For n>=3 rules are
mutually incompatible.

Its marked full vector has the canonical r_i factor, the extra factor

    B_(r_j)(E)=[a_j notin E],

and all other factors true. Indeed a rival r_l sibling has profile
h_i,r_l AND h_j,r_l, which vanishes on the marked-source-not-r_l
probe. At the final sibling its r_j profile is
(h_i,r_j AND h_j,r_j) OR a_j,r_j, leaving exactly a_j's filter.
Marked-union restoration with F preserves this sound vector and
makes it an actual type in an F realizer.

Choose two different indices j,l other than i. The coordinatewise
OR of their two actual vectors is exactly (6), which is nonactual.
It is globally sound, since F is source-separable. Moreover there
is no greatest actual type at h_i: pure probes bound every actual
vector by (6), while the two displayed vectors already join to it.
This is a failure inside the genuine separable class, strengthening
the earlier [general side-effect obstruction](actual-type-side-effects.md).

## Old-observer and common-carrier completions differ

For these genuine base operations the canonical common-carrier G_Q is
not term-induced. On the extension with a new observer its query q
retains a head source, whereas every realizer must omit that observer
by (C). The short-spine word instead attains the greatest core minorant
(4) on the enlarged owner set.
It also gives a closed formula for the **greatest term-induced**
common-carrier extension of the base operation:

    H_F=G_Q off bad;
    H_F=flat union of the anchors on bad.             (8)

The short-spine coverage proof works for a fresh winner whenever
some anchor is off its own owner. On bad, an anchor carrying the fresh
winner supplies it directly. Otherwise enlarge all heads to the fresh
top P and unused anchors to N; invariant (C) forbids P in every
realizer's extension. Distinct context owners ensure that the anchor
union there is N. Pure-port bounds give the common upper bound G_Q
off bad. The short-spine word attains (8), and every realizer lies
below it.

In contrast, their greatest product completion at the **old observers**
is term-induced, even on arbitrary independent owner flags. At observer
k=r_j!=r_i, the protected type (7) has only an extra r_j factor, which
that observer ignores. It therefore attains the whole canonical
coefficient for source h_i. At the own observer k=r_i, the safe direct
word h_i choice_(r_i) a_i has no foreign factor, giving its required
unconditional coefficient. Anchor projections supply all anchor
coefficients. Marked restoration and coextension put these finitely
many actual types in one F realizer. Pure probes bound every other
realizer's factors by the canonical ones, so this realizes the greatest
old-observer independent-flag product.

Thus old-observer product attainment, greatest full occurrence type,
and canonical common-carrier product attainment are different assertions.
This family has the first and fails the latter two. Its strictly smaller
greatest term-induced common-carrier extension is attained by (8). It
does not refute old-observer product attainment for general genuine
source-separable targets.

Thus ordinary source separation does not imply maximal-type attainment
or owner-extension stability. The full intrinsic characterization of
arbitrary jointly realizable source guards is still unresolved. The
classification (5) and the obstruction above solve this specified
circuit family and the proposed maximal-type shortcut, respectively.
