# Upper intervals above profile maxima

Mathematical research, without Lean claims. A closure-based capture-trigger
condition gives source-linear core minorants attaining all canonical
full source types. Shared-anchor closures are an independently
parametrized special case. The hypothesis is sufficient, not necessary
for core membership.
Throughout, the target is the source-separable reconstruction from the
closure tuple; pure closures alone do not determine a nonseparable target.

Fix finite owners I with K>=3 and a finite nonempty variable set V.
Menus are nonempty subsets of I, and

    U star_r Z = {r} if U={r} or Z={r},
                 U union Z otherwise.

Derived union is available in the core. For a valuation w put
E_r(w)={v:w_v={r}}. For loopless closures c_r on V define

    k in F_c(w) iff some j with k in w_j is outside
                            UNION_(r!=k) c_r(E_r(w)).     (1)

The intended pure-owner factor of source j is

    D_(j,r)(E)=[j notin c_r(E)], E subseteq V\{j}.         (2)

At a marked j occurrence, its r factor is the conjunction of the
complements of its sibling r-singleton profiles at r-owned ancestors,
with j not an r atom. An observer k uses the product over r!=k;
a fresh unowned observer uses every factor. These factors can also
be evaluated on independent, overlapping owner-status sets.

## The upper-interval theorem

Let p=(p_r)_r be an admissible singleton-profile tuple: each p_r is
monotone, false at empty, true at V, and every choice of positive
coalitions A_r, one per owner, has nonempty intersection. Its greatest
profile completion H_p returns {r} when p_r(E_r) holds and otherwise
the full input union. Admissibility makes it a core operation.

Define the closure tuple

    c_r^p(E)=V if p_r(E), and E otherwise.                (3)

Monotonicity of p_r makes this a loopless closure. It is the pure
closure tuple of H_p.

**Theorem.** For every tuple of closures satisfying

    id <= c_r <= c_r^p for every r,                      (4)

the reconstruction F_c is nonempty and core. Every source j has a
minorant S_j using j exactly once and attaining its canonical full
vector (2). All these types are actual in an F_c realizer. Hence its
canonical
common-carrier completion and greatest independent-status product
completion are term-induced.

These are exactly the source-separable reconstructions above H_p in
pointwise winner inclusion. The interval is closed under pointwise
union and every owned choice, with the closure operations below.

## One-owner traces and source factors

Fix r and call H open when V\H is c_r-closed. For nonempty H let
m_r(H) be the r-fold of its variables. The canonical one-owner trace is

    F_r=UNION_(H open, H nonempty) m_r(H).                (5)

The open family includes V, so every variable occurs. On a pure-r
source probe j={k}, k!=r, a monomial supplies k exactly when it contains
j and avoids the r-atomic set E. The largest open subset of V\E is
V\c_r(E), giving exactly (2). All foreign factors are true, and
winner r is retained whenever any input contains it. Thus F_r has
the reconstruction (1) with only c_r and all other closures identities.

If D_(j,r) is identically true, {j} is open (test E=V\{j}), so
j<=F_r. Otherwise factor j from its monomials using distribution of
star_r over union. Their residual sets are nonempty, giving a j-free
one-owner word

    G_(j,r)=UNION_(H open, j in H) m_r(H\{j}),
    j star_r G_(j,r) <= F_r,
    Phi_r(G_(j,r))(A)=q_(j,r)(A):=[j in c_r(A)],
                                  A subseteq W=V\{j}.   (6)

The last equality complements the open-set survival test. A residual
monomial is r exactly when A meets H\{j}, and their union is r
exactly when every residual monomial is r.

## A normal form protected by source-free trigger words

Condition (4) says that every nontrivial capture implies its trigger:

    q_(j,r)(A) implies p_r(A), A subseteq W.              (7)

For every nonzero q_(j,r), choose a j-free derivative trigger H_(j,r)
on W with profiles

    beta_r(A)=p_r(A);
    beta_s(A)=p_s(A union {j}) for s!=r.                 (8)

These profiles are monotone and true at W. Nonzero q_(j,r) implies p_r(W)=true,
which rules out p_s({j}) for every s!=r by the original rainbow
condition. Thus the beta profiles are normalized. For beta-positive
coalitions A_s subseteq W, use the original positive coalitions A_r
and A_s union {j}, s!=r. Their common intersection is nonempty, and
excluding j from A_r makes it exactly the intersection of all A_s.
Profile synthesis therefore gives H_(j,r). In particular W is nonempty
whenever such a trigger is needed.

If no p_r(E_r) holds at a valuation, (4) makes every current closure
an identity, and F_c is the full input union. Otherwise there is a
unique trigger s. Every foreign closure is an identity there, and

    F_c=F_s,    s in F_s.                               (9)

The membership assertion follows because p_s(empty) is false, so
there is an s-atomic input, whose winner is retained by the r-only
trace at r=s. These cases prove nonemptiness and H_p<=F_c.

For each nonzero q_(j,r), first union G_(j,r) with H_(j,r). Its
r-profile is q_(j,r) AND beta_r=q_(j,r), by (7). Next attach H_(j,r)
once at each foreign owner s!=r, in any order. Call the resulting sibling
Gtilde_(j,r). It has the properties

    Phi_r(Gtilde_(j,r))=q_(j,r);
    Gtilde_(j,r)=G_(j,r) union {r} if H_(j,r)={r};
    Gtilde_(j,r)={s} if H_(j,r)={s}, s!=r.              (10)

All these sibling profiles are evaluated on the passive set W.
Each foreign attachment only conjoins the r-profile with beta_r,
already implied by q_(j,r). If H_(j,r)={r}, the starting union contains
r, so no foreign stage can absorb it and adjoining r changes nothing.
If H_(j,r)={s} with s!=r, the s stage absorbs to {s}; all later stages
keep it.

Start S_j at a marked j and attach Gtilde_(j,r) at owner r for each
nonzero q_(j,r), in any order. All siblings are j-free, so S_j uses
j exactly once; its marked full vector is precisely (2).

To prove S_j<=F_c, the no-trigger case follows by conservativity.
Suppose p_s(E_s) is true. First let w_j!={s}. Then E_s subseteq W,
so every derivative trigger H_(j,r) is {s}: its s-profile is either
p_s(E_s) or p_s(E_s union {j}). Before the s stage, every sibling
is {s}, so the prefix is contained in w_j union {s}. If that stage is
present, (10) and inclusion monotonicity bound its output by

    (w_j union {s}) star_s (G_(j,s) union {s})
       = (w_j star_s G_(j,s)) union {s}
       subseteq F_s.                                  (11)

The identity follows by distribution over union and absorption of
{s}; the inclusion uses (6) and (9). Subsequent siblings are {s}
and stay inside F_s. If the s stage is absent, j<=F_s, so the whole
spine stays inside w_j union {s} subseteq F_s.

If instead w_j={s}, every foreign derivative H_(j,r), r!=s, is {s},
because its s-profile is p_s((E_s\{j}) union {j}). The prefix stays
exactly {s}; its own s stage absorbs any sibling, and subsequent
foreign stages again leave {s}. This proves the bound in all cases.

Union all S_j. Their marked factors supply every contribution in (1),
so this union realizes F_c. Restore each S_j by union with this F_c
realizer. The marked-union preservation lemma in
[source-type-pruning.md](source-type-pruning.md) keeps its sound full
vector unchanged; coextension combines the finitely many witnesses.
Pure probes bound every actual factor by (2), proving attainment of
the canonical full vectors and both product completions claimed above.

Finally, H_p<=F_c also follows from the cases (9). Conversely suppose
H_p<=F_c and a proper E violates (4), with j in c_r(E)\E but p_r(E)
false. Choose k!=r, put j={k}, E at r, and every other input at
I\{k}. The reconstruction F_c omits k. The greatest completion H_p
contains k: its only possible atomic output is r or k, and p_r(E)
is false; its remaining case is the full input union. This contradicts
the bound. Thus the interval description is exact.

## An intrinsic capture-trigger test

For an arbitrary loopless closure tuple define its minimal normalized
trigger profiles by

    p_r^cap(E) iff E=V or some P subseteq E has c_r(P)!=P. (12)

These predicates are monotone, false at empty and true at V. The
existence of an admissible p satisfying (4) is equivalent to
admissibility of p^cap. Indeed (4) forces every nontrivial-capture
premise to be p-positive; monotonicity and normalization give
p_r^cap<=p_r. Admissibility passes to these smaller predicates.
Conversely p^cap itself covers every capture, so (4) holds for it.

This is a finite condition purely on the closures, without an
occurrence graph or an unknown realizing word. It is not necessary:
the three-head family with contexts L_0=L_1={a}, L_2={b} is core by
[the complete-head classification](complete-head-circuits.md), but
its three rule premises are positive for p^cap and have empty common
intersection. The theorem gives a broad positive class, not the full
intrinsic criterion.

## The closure-tuple subalgebra

For arbitrary core F,G on common full support V, put T=F star_s G.
Their pure closures obey

    c_r^T(E)=c_r^F(E) intersect c_r^G(E)        if r!=s;
    c_s^T(E)=V                                if c_s^F(E)=V
                                                or c_s^G(E)=V;
             c_s^F(E) intersect c_s^G(E)       otherwise. (13)

For pointwise union use intersection everywhere. For r!=s choose
a pure-r observing owner different from r,s. No input is an s atom,
so neither operand is an s singleton; the root unions their source
bits. Complementing them gives intersection. For r=s, a spanning
operand has value {r}, so the root absorbs and blocks every source.
If neither spans, neither is {r}, and the root again unions source
bits. Extensivity covers positions already in E, including E=V.

These formulas preserve (4): where p_r(E) is false, both input
closures equal E and neither spans. They also preserve closure
operators. For the own-coordinate operation, if neither value is
top, its intersection C has c_r^F(C) subseteq c_r^F(E)!=V and
similarly for G; applying the operation again returns C. The other
closure laws follow from monotonicity and extensivity. Ordinary
pointwise intersections of closures are closures as well.

The resulting operation is still the reconstruction of its tuple.
At a no-trigger valuation both operands are the full input union.
At a unique trigger r, both are their r-only traces and contain r.
A foreign s gate is union, while an r gate is the one-owner trace
product. Its closure is (13), and a one-owner trace is determined
by that closure. This identifies the full output in each case.

Thus reconstruction is a homomorphic section of the pure-closure map
on the Cartesian product of closure intervals [id,c_r^p]. This is the
algebra of source-separable operations above H_p, with pointwise
union and owned choices.

## Shared-anchor closures

Suppose V has an anchor Y and

    Y notin E implies c_r(E)=E for every r.              (14)

The admissible profile tuple p_r(E)=[Y in E] bounds these closures
as in (4). For j!=Y every derivative trigger can be Y. For j=Y
every factor is identically true, so S_Y=Y. Source-linearity refers
to these minorants, not to the complete F_c realizer in every label.

Writing W=V\{Y}, (14) is equivalent to arbitrary closures d_r on W,
allowing loops:

    c_r(E)=E                         if Y notin E;
           {Y} union d_r(E\{Y})     if Y in E.           (15)

Conversely d_r(A)=c_r(A union {Y})\{Y}. The closure laws in both
directions follow directly. When Y is ambiguous F_c is the full
input union; when Y={s}, it has the particularly simple value

    {s} union UNION_(j in W\d_s(E_s\{Y})) w_j.

This gives an independent closure choice for every owner. Formula
(13) in d_r coordinates uses top W in place of V. It includes W empty,
when the operation is simply Y.

## Smaller canonical traces

The one-owner trace (5) needs only nonempty join-irreducible open sets,
equivalently complements of proper meet-irreducible closed sets. Every
open set is a union of these in the finite open lattice. If H=H_1 union
H_2, associativity and idempotence give

    m_r(H)=m_r(H_1) star_r m_r(H_2)
                      subseteq m_r(H_1) union m_r(H_2).

Thus decomposable monomials are redundant. In the shared-anchor case
{Y} and {Y,j} are open, because their complements omit Y. If {j} is
not open, {Y,j} is join-irreducible: no proper open subset can contain
j. Hence factoring j from the reduced trace still leaves the Y
monomial in G_(j,r), as in the direct shared-anchor construction.
