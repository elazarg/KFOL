# A closed characterization for additive colored closures

Mathematical research, without Lean claims. For source-separable operations
whose canonical owner closures are additive, two closed conditions on the
owner preorders are necessary and sufficient for core realizability. The
proof constructs finitely many component spines. Each chosen source has a
linear subordinate word carrying its complete canonical factor vector.
Marked completion then realizes all maximal vectors simultaneously and
attains the greatest free extension.

This is a characterization of the additive source-separable subclass.
The general colored-closure and joint prime-guard problems remain open.

## The two graph conditions

Fix finite owners I with K>=3 and a finite nonempty variable set V of size
n. Let c_r be loopless additive closure operators on V:

    c_r(E)=UNION_(i in E) c_r({i}),    c_r(empty)=empty.

Write i ->_r j when j belongs to c_r({i}). Each relation is a preorder.
The orientation is from an atomic source i to the dependent point j it
closes. Define the source-separable reconstruction, initially allowing
empty outputs, by

    k in F(w) iff some j with k in w_j is outside
                           UNION_(r!=k) c_r(E_r(w)),
    E_r(w)={i:w_i={r}}.                                  (1)

At a pure-r source probe, only its marked source contains the observer
k!=r and every other owner has empty atomic set. Its coefficient is
therefore exactly [j notin c_r(E)]. Thus if F is core these are its
canonical owner closures. On all-ambiguous inputs (1) is full input
union, so every variable belongs to its essential support.

Consider these conditions:

    (D) If i!=j and i ->_r j, then
        c_s({j}) subseteq c_r({i}) for every owner s.

    (R) There are no i!=j and r!=s with
        i ->_r j and j ->_s i.

They quantify only over the given colored relations. There is no auxiliary
occurrence graph, term witness, or supplied elimination order in the tests.

**Characterization theorem.** The reconstruction (1) is a core operation
if and only if (D) and (R) hold.

In particular these conditions imply nonempty outputs, admissible profiles
on every neutral restriction, and all the required atomic and omission
laws; these are consequences of the construction, not extra hypotheses.

There is a direct guard version which does not assume closure operators
as input. Give forbidden-source sets N_(j,r) subseteq V\{j}, and prescribe
the common-owner monomial coefficients

    C_(j,k)(p)=AND_(r!=k) AND_(i in N_(j,r)) [p_i!=r].

Define i ->_r j exactly when i=j or i belongs to N_(j,r). These guard
families are jointly core-realizable if and only if (D),(R) hold for the
resulting relations. Indeed (D) already makes each reflexive relation
transitive, so c_r(E)=UNION_(i in E) c_r({i}) with
c_r({i})={j:i ->_r j} gives precisely the loopless additive closures
above. The coefficients then reconstruct (1). Conversely, the pure-owner
sections of any realizing word recover these same relations and closures,
so the necessity argument applies.

More generally, the initial forbidden sets may depend on the observer:
N_(j,k,r) for r!=k. Then a third closed test is needed:

    (O) N_(j,k,r)=N_(j,l,r) whenever k!=r and l!=r.

Every realizing word satisfies (O): its pure-r source port is independent
of the observing owner k!=r. A probe with only passive variable i equal
to {r}, every other passive variable neutral, detects exactly whether
i belongs to N_(j,k,r). Thus the forbidden sets themselves must agree.
Conversely (O) gives common N_(j,r), and (D),(R) supply the realization.

Consequently (O),(D),(R) are a closed criterion directly on normalized
guard families having one fixed conjunction per source and observer.
They do not cover arbitrary prime-guard disjunctions or nonadditive
owner factors.

## Why the conditions are necessary

In this additive setting, (D) is equivalent to idempotence of every colored
map

    d_alpha(T)=UNION_r c_r(T intersect alpha^(-1)(r)),
        alpha:V->I.                                     (2)

For necessity, if i!=j and i ->_r j, choose alpha(i)=r and alpha(j)=s.
Then d_alpha({i})=c_r({i}), and idempotence gives
c_s({j}) subseteq d_alpha(c_r({i}))=c_r({i}).

Conversely suppose (D) holds and j belongs to d_alpha(T). If j was already
in T, its assigned-color closure is one of the original seed closures.
Otherwise some i in T, i!=j, has j in c_(alpha(i))({i}). Condition (D)
puts c_(alpha(j))({j}) inside that same seed closure. Additivity therefore
gives d_alpha(d_alpha(T)) subseteq d_alpha(T); extensivity gives equality.

Canonical closures of genuine source-separable core operations satisfy
(2), by [full colored outcast](mixed-closure-outcast.md). Thus (D) is
necessary.

Condition (R) is exactly admissibility of the restricted spanning profiles
on every two-point set. Opposite arcs of different colors would make
{i} winning for r and {j} winning for s on {i,j}; taking top coalitions
for the other owners gives an empty rainbow intersection. Conversely,
an empty rainbow intersection of nonempty coalitions on two points must
use both opposite singleton coalitions at different owners.

For a genuine core operation, each nonempty neutral restriction is core
on its remaining full support. Its pure-owner ports are the restrictions
of the original ports, so its spanning profiles are exactly those of the
restricted closures. They are admissible. This proves necessity of (R).

## Monochromatic components and their ancestor order

Assume (D),(R). The union relation i -> j, meaning i ->_r j for some r,
is a preorder. Indeed a path i ->_r j ->_s l with i!=j closes under its
first color by (D); paths with repeated endpoints cause no difficulty.

Take its strongly connected components. Their quotient is a partial order,
again oriented from ancestors to dependents. Every component H of size at
least two has one internal owner r_H, and every nontrivial internal arc
has exactly that color.

To prove this, opposite arcs inside a component exist for every pair by
transitivity of the union relation. Condition (R) forces both directions
to have the same unique color. Fix a pair u,v with color r. For another
point z in the component, let u,z have color s. Composing v ->_r u with
u ->_s z gives v ->_r z; composing z ->_s u with u ->_r v gives
z ->_s v. Condition (R) forces r=s. This proves uniformity throughout H.
Singleton components have no internal owner assigned.

Two further consequences will control the construction.

* Incoming colors are uniform across a target component C. If h outside
  C satisfies h ->_s j for one j in C, then h ->_s j' for every j' in C,
  by (D). Write this as h ->_s C.
* If a nontrivial component H is a proper ancestor of C, then every
  h in H satisfies h ->_(r_H) C. Start with any h ->_s C and another
  h' in H. The internal r_H arc h' -> h propagates that color to C;
  returning through an internal arc gives the same conclusion for h.

## Constructing a component spine

For each target component C construct a word S_C. Start with the
choice_(r_C) fold of the variables in C when C is nontrivial; for a
singleton C={j}, start with x_j.

List the proper ancestor components of C in reverse topological order:
if H is an ancestor of L, process L before H. In other words, process
the components nearest the target first. For each such H:

* If H is a singleton {h}, attach x_h by choice_s for every color s
  satisfying h ->_s C.
* If H is nontrivial, first attach x_h by choice_s for every incoming
  flag h ->_s C with s!=r_H. Then attach the choice_(r_H) fold of all
  variables in H by one further choice_(r_H) gate.

Attaching a sibling means replacing the current word u by u choice_s G.
All folds are nonempty. Orders within one component's first group of
attachments may be arbitrary. The component order is needed only for
the protection of newly introduced auxiliary sources.

Each target j in C occurs exactly once in S_C. Its exact full factors are

    B_(j,r)(E_r)=[j notin c_r(E_r)]
       =AND_(i!=j, i ->_r j) [i notin E_r].               (3)

The starting fold gives precisely the internal r_C filters. Every
singleton ancestor attachment gives its indicated predecessor literal.
For a nontrivial ancestor H, its final r_H fold adds all literals from
H at r_H, which are exactly required incoming flags by the preceding
component facts; its other incoming colors were attached separately.
Thus there are neither missing nor extra target filters.

## Every auxiliary occurrence is protected

For any variable h introduced in an ancestor component H, every occurrence
in S_C has full factors bounded above by h's canonical factors (3).
Extra filters are allowed here; only target-component occurrences must
attain equality.

Consider a required predecessor i ->_r h, i!=h. If i lies in H, the
component is nontrivial and r=r_H. An h occurrence inside the final H-fold
has the internal filters from every other point of H. An h occurrence
introduced by an earlier foreign-color attachment acquires those same
filters when the H-fold is attached above it. On a source-h observation
the h flag itself is false, so the fold's r_H profile tests precisely
the other H variables.

If i lies in a different component L, then L is a proper ancestor of H
and hence of C. It is processed later. Moreover i ->_r h and h -> C
imply i ->_r C by (D). If L is a singleton, its later attachment of
x_i at r provides the required filter. If L is nontrivial and r!=r_L,
the corresponding foreign-color attachment does so. If r=r_L, the
L-fold provides it. Thus every required external filter lies above the
h occurrence.

All marked occurrence contributions of S_C are consequently contained
in (1), source by source and observer by observer. Hence

    S_C(w) subseteq F(w) for every w.                     (4)

This proves, in particular, a chosen-source-linear minorant for every
j, with its whole canonical vector attained at its unique occurrence.
It does not claim that this minorant already equals F.

## Exact reconstruction and size of the normal form

Take the derived union of these words:

    T=UNION_(components C) S_C.                          (5)

Equation (4) gives T<=F. Conversely, any winner in (1) has a supplying
source j in some C. Its marked occurrence in S_C has exactly (3), so
that occurrence supplies the same winner. Thus F<=T. Therefore T=F,
proving sufficiency without any prior nonemptiness assumption.

There are at most n component spines. The base of S_C has |C| leaves.
A singleton ancestor contributes at most K leaves. An ancestor H of
size at least two contributes at most (K-1)|H| foreign-color leaves and
|H| leaves in its final fold. Consequently every spine has at most Kn
leaves, and (5) has at most Kn^2 leaves when derived union is treated as
an allowed gate.

There is also a polynomial primitive-word bound. The standard derived
union is

    unionTerm(s,t)=(s choice_0 t) choice_2 (s choice_1 t),

using any three distinct owners. It has exactly twice the sum of its
operands' leaf counts. Arrange the m component spines in a balanced
binary union tree, splitting each list into floor/ceiling halves. Its
height is ceil(log_2 m), so each spine is copied at most
2^ceil(log_2 m)<=2m times. Therefore its primitive expansion T has

    L(T)<=2m SUM_C L(S_C)<=2Kn^3.                        (5a)

The inequalities are loose also when m=n=1. All the resulting terms
are binary, so their gate counts are exactly one less than their leaf
counts.

## Maximal full types and greatest free completion

The plain derived-union expansion of (5) need not preserve all marked
full vectors on independent flags. A marked completion is needed for
the full-type and free-extension conclusions.

For each j choose its component C and a fresh copy of S_C with j marked.
Form the standard core union of T with this copy. It still realizes F
by (4). The marked-union lemma preserves its exact vector (3): that
vector is sound for F by definition of (1). More explicitly, whenever
B_(j,r)(E_r) is true, a source-j pure-r probe makes both T and S_C
contain a non-r winner. Their r-singleton profiles are therefore false
at that atomic set. Every added r-owned sibling in the union implementation
is then non-r, so its new exclusion factor is redundant. Where the old
factor was false it remains false.

These completed words all realize the same F. Combine them by a fold of
one fixed primitive owned choice. Idempotence preserves F, and each
marked vector survives: at an r-owned macro gate the sibling has F's
r-profile, which is false whenever that marked r-factor is true. Thus
one realizer contains every source's canonical vector (3).

Pure-owner source probes recover the given ports of F. Every actual
occurrence's r-factor is bounded by their OR, which is
[j notin c_r(E_r)]. Hence (3) is the unique greatest actual full type at
j. The preceding completed realizer attains these greatest types for
all sources simultaneously.

For independent, possibly overlapping rival flag sets E_r, it follows
that the greatest term-induced free extension is

    C^greatest_(j,k)(E)=AND_(r!=k) [j notin c_r(E_r)]      (6)

at every old observer k. Each occurrence contribution is bounded by this
product, and the completed word attains it. It is also the greatest
arbitrary antitone extension: a zero has a single-owner, one-hot zero
subpattern witnessing one failed factor, which forces every antitone
extension to stay zero above it.

For a fresh unowned observer include every old-owner factor in (6).
Thus the same word also realizes the canonical common-carrier operation
G_Q from [canonical-separable-extension.md](canonical-separable-extension.md).
The fresh-observer conclusion is greatest among term-induced extensions;
no greatest arbitrary monotone completion of the old faces is asserted.
The marked completion also has a polynomial primitive-word bound.
If C_j contains j, its completed word unionTerm(T,S_(C_j)) has
2(L(T)+L(S_(C_j))) leaves. Coextend the n completed words by a fold
of one fixed primitive owner, which introduces no duplication. The
final word realizing all greatest free coefficients has at most

    2n L(T)+2 SUM_j L(S_(C_j))
        <=4Kn^4+2Kn^2<=6Kn^4                            (7)

primitive leaves. No uniqueness or least-free-extension conclusion
is asserted.

The classification is intrinsic for additive source-separable guard data:
recover the owner preorders from their canonical pure sections, check
(D),(R), and the construction gives a realizing word. Nonadditive closure
dependencies, and beyond them nonseparable mixed guards, remain outside
this theorem.
