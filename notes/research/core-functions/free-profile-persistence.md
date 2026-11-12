# Rainbow profiles force genuinely free source coefficients

Mathematical research, without Lean claims. The positive-profile persistence
argument does not require rival singleton flags to be mutually exclusive.
It therefore gives a lower bound on the independent-status extension of
every representing word, not merely on its ordinary winner operation.

Fix a finite owner set I of size K>=3 and a finite variable set V. Words
use variables and primitive I-owned choices, without constants or role
switches. Fix a source j in V. The observer k may be an old owner in I
or one fresh unowned symbol.

## Independent-status recurrence

For each old owner r choose E_r subseteq V\{j}. These sets are independent:
one passive variable may belong to several E_r simultaneously. Write
Phi_r^S(A) for the ordinary r-singleton profile of a word S, and let
C_(j,k)^S(E) be its free source coefficient, as in
[free-polarization-extrema.md](free-polarization/free-polarization-extrema.md).

At a leaf with label l the coefficient is true exactly when l=j. At a
gate S=u choice_h v its recurrence is

    C^S = C^u OR C^v,                                    if h=k;
    C^S = (C^u AND NOT Phi_h^v(E_h))
             OR (C^v AND NOT Phi_h^u(E_h)),               if h!=k.

For a fresh observer every gate uses the second line. The ordinary profiles
take OR at their own owner's gate and AND at every other gate. All of these
recurrences are evaluated with the same globally specified sets E_r; no
one-hot restriction is imposed.

## Free rainbow persistence

**Theorem.** Suppose there are coalitions A_r, one per old owner, with

    Phi_r^S(A_r)=true for every r in I;
    intersection_r A_r={j};
    E_r intersect intersection_(s!=r) A_s=empty
        for every old r!=k.                              (1)

Then C_(j,k)^S(E)=true, even when the E_r overlap.

Induct on the word. At a leaf l, the positive profiles require l in every
A_r, so l=j and its coefficient is true.

Suppose the root owner is h. Its h-profile is OR, so choose a child L
with Phi_h^L(A_h)=true and call the other child R. For every s!=h the
root's s-profile is AND; hence both children have their positive A_s bit.
Thus L satisfies every positive demand in (1). The intersection and
avoidance conditions concern only the prescribed sets and remain unchanged,
so induction gives C_(j,k)^L(E)=true.

If h=k this contribution reaches the root by the first recurrence line.
If h!=k, the sibling cannot have Phi_h^R(E_h)=true. Otherwise the winning
coalitions E_h for h and A_s for s!=h in that same sibling would have a
common source, by rainbow common-source persistence. This would give an
element of E_h intersect intersection_(s!=h) A_s, contrary to (1).
The sibling h-filter is therefore true, and the second recurrence line
propagates L's coefficient to the root. This completes the induction.

The proof uses only profile recurrences, rainbow common-source persistence,
and the free coefficient recurrence. It never combines the E_r into an
actual winner valuation. In particular, overlap of different owner flags
at one passive variable causes no difficulty.

For a fresh observer one may add the top coalition A_k=V: its profile is
true because it contains the word's support. This does not change any
intersection in (1). The old-owner formulation above already suffices.

## Sharpness for a single rainbow premise

The theorem is exact as a statement about one full rainbow family of
positive profile demands. Let C=intersection_r A_r. If C is empty, no
core word satisfies all those demands. If C is nonempty, a word S with
all those positive bits and C_(j,k)^S(E)=false exists exactly when

    C\{j} is nonempty; or
    some h!=k has E_h intersect intersection_(s!=h) A_s
        nonempty.                                      (2)

For the first alternative choose a label l in C\{j} and use projection
x_l. It has every requested positive bit and no occurrence of source j.

If the first alternative fails, then C={j}. For the second alternative
choose l in E_h intersect intersection_(s!=h) A_s and use

    x_j choice_h x_l.

Its h-profile is true because j belongs to A_h. Every other owner's
profile is true because both j and l belong to its coalition. The chosen
l is different from j, since E_h excludes j. As h!=k and l belongs to
E_h, the sibling blocks the unique source-j occurrence, making its free
coefficient false.

Conversely, if both alternatives in (2) fail, nonemptiness gives C={j}
and every required avoidance intersection is empty. The theorem then
forces the free coefficient true in every word satisfying the demands.

Thus an actual zero witness, whenever one exists for a single rainbow
premise, is already a projection or a two-leaf word. This sharp one-premise
statement also determines forcing by arbitrary positive profile families.

## Exact forcing by arbitrary positive profile families

For each owner r let Acal_r be a family of coalitions containing the top
coalition V. A word retains these requirements when

    Phi_r^S(A)=true for every r and every A in Acal_r.

**Theorem.** Every word retaining the requirements has
C_(j,k)^S(E)=true exactly when some one-per-owner selection A_r in Acal_r
has one of the following forms:

1. Its common intersection is empty.
2. Its common intersection is {j}, and every avoidance intersection
   E_r intersect intersection_(s!=r) A_s is empty for old r!=k.

The first case is infeasibility of the positive requirements themselves,
so the conclusion is then vacuous. If the requirements have any core
realizer, only the second case can occur. Under that natural feasibility
assumption, a free coefficient is forced exactly by one certificate (1).

The forward proof uses a minimal positive premise. Words whose queried
free coefficient is false remain false under every owned choice: both
children have coefficient zero in either recurrence line. Their profile
image is therefore closed under the usual owner-colored Boolean gates.

Suppose none of these zero-coefficient words retains all the requirements.
There are only finitely many profile bits. Choose an inclusion-minimal
subfamily P of the positive requirements which no zero word satisfies.
The subfamily may be empty. It cannot contain two bits alpha,beta of the
same owner h. Minimality would give zero words u and v satisfying
P\{alpha} and P\{beta}, respectively. Their h-owned combination repairs
both h-bits by OR, retains every other-owner bit by AND, and still has
zero free coefficient. This contradicts the choice of P.

Thus P has at most one bit per owner. For each missing owner add its top
coalition V, which belongs to Acal_r and is winning for every core word.
The resulting full rainbow premise still has no zero witness. By the
one-premise sharpness result, its common intersection is empty or it has
precisely the certificate form (1). This proves the forward implication.

Conversely, an empty rainbow intersection excludes every core word by
common-source persistence, and a certificate (1) forces the free bit by
the induction above. This proves both directions. No one-hot assumption,
auxiliary invariant presentation, or simultaneous choice of word realizers
is used in this argument.

The top requirements matter. They permit completion of the minimal rainbow
premise without introducing new positive demands. For an arbitrary family
one can first adjoin these universally true top bits.

## The pointwise least free coefficients of profile families

Let Phi be an actual admissible profile tuple and take

    Acal_r={A:Phi_r(A)=true}.

For each source j, observer k, and independent flag tuple E, the existence
of a certificate (1) is now exactly the minimum of C_(j,k)^S(E) over all
words retaining every positive bit of Phi. If the certificate exists,
every such word has coefficient one. If it does not, the theorem supplies
a retaining word with coefficient zero.

If Phi is maximal admissible, retaining its positive bits already forces
the entire profile tuple: the profile tuple of a retaining word is an
admissible extension of Phi, hence equals Phi. In this case the same
closed certificate formula gives the pointwise least free coefficients
over all words in the exact Phi-profile fibre.

These are pointwise minima. The zero witness may depend on the source,
observer, and flag tuple. The theorem does not supply one word attaining
all minima simultaneously, nor does it restrict the retaining words to
realizers of a specified full operation F unless the profiles themselves
already determine that operation.

Joint attainment fails even for a maximal profile tuple determining one
exact full operation. The
[ternary quota counterexample](free-profile-nonattainment.md) has two
term-induced extensions with no common term-induced lower bound. Each
bitwise minimum is correct, while a common-source disjunction prevents
their simultaneous attainment.

## Read-once words have exact free certificates

**Theorem.** If T is primitive read-once and j occurs in T, then
C_(j,k)^T(E)=true exactly when its positive profiles admit a certificate
(1). This holds for arbitrary overlapping E_r and for an old or fresh
observer k.

Only necessity remains to prove. We use the fact that every read-once
profile tuple is maximal admissible. Indeed an admissible positive
extension Psi can be synthesized by a core word S. The read-once
positive-profile lower bound gives T<=S. At any new singleton-profile
bit of S, its probe output is {r}, forcing the nonempty output of T to
be {r} too. Thus no bit was new. The same argument applies to every
read-once subtree on its own variable support.

Consequently, if R is a read-once subtree with support V_R and
Phi_h^R(E)=false for E subseteq V_R, there are winning coalitions A_s^R
for all s!=h with

    E intersect intersection_(s!=h) A_s^R=empty.           (3)

Otherwise adding E and all its supersets to the h-winning family would
preserve monotonicity and every rainbow common-source intersection. It
would be an admissible strict extension, contradicting maximality.

Now induct on T, taking all constructed coalitions inside the subtree's
variable support. A true source coefficient at a leaf means its label is
j; take every coalition to be {j}.

At a root owned by h, let L be the child containing the unique j occurrence
and R the other child. Their variable supports V_L,V_R are disjoint.
The recurrence and C_(j,k)^T(E)=true imply C_(j,k)^L(E)=true. Induction
gives a certificate A_s^L inside V_L, using the restrictions E_s intersect
V_L of the independent flag sets.

If h!=k, the same recurrence gives

    Phi_h^R(E_h intersect V_R)=false.

Choose the other-owner winning coalitions A_s^R from (3), with
E=E_h intersect V_R. If h=k, no h-avoidance is required, and take
A_s^R=V_R for every s!=h. Set

    A_h=A_h^L,
    A_s=A_s^L union A_s^R for s!=h.

The h-profile wins by its left OR branch; every other profile wins in
both children. Because A_h lies inside V_L, the common intersection is
the left certificate's singleton {j}. For r!=h,k, the A_h factor restricts
the r-avoidance intersection to V_L, where induction applies. For
r=h!=k, disjoint supports split the other-owner intersection into its
left and right parts; the left avoids E_h by induction and the right
avoids it by (3). Thus (1) holds, completing the proof.

For read-once Phi=Phi^T, therefore, the pointwise least free vector in the
profile fibre is attained simultaneously by T itself. Every positive-profile
majorant word S has

    C_(j,k)^T(E) <= C_(j,k)^S(E)

by free persistence. This joint attainment conclusion is specific to the
read-once profile regime, not arbitrary maximal admissible profiles.

There is also full free-extension rigidity for the exact operation F=T.
If S realizes the same old winner operation, the
[pure-owner upper-bound theorem](read-once-rigidity.md) gives the reverse
inequality C^S<=C^T on every independent flag tuple. Hence every realizer
has exactly T's free coefficients. A primitive read-once operation has a
unique term-induced independent-status extension, not merely a greatest
one or a unique ordinary unowned-observer extension.
