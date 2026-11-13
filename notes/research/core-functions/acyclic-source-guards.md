# Acyclic source dependence: working normalization lemmas

This is an unfinished route toward the full joint-guard characterization.
There is no sufficiency theorem here. The lemmas below are mathematical
proofs; no Lean development has been started.

Let F be a nonempty source-reconstructing operation. Its complete source
predicates pi_i are antitone predicates on proper partial colorings of the
other inputs, agreeing across observer overlaps. Assume an ordering of the
inputs such that pi_i depends only on predecessors of i. Also assume the
full colored-cofactor law: pi_i(E)=0 makes the whole cofactor fixing E
independent of i. Positive coefficients witness dependence at their probes.

## Singleton factorization follows from these assumptions

Suppose F(v)={r}. Process the inputs with v_i!={r} in order. At such i,
choose k!=r in v_i. By induction every earlier non-r input is captured
under its original r-colored predecessor set. These sets lie in the
current r-prefix, so full FD permits replacing all those earlier non-r
menus by N_k simultaneously without changing F(v)={r}. Earlier r-inputs
stay fixed at r. The coefficient of source i for winner k is now exactly
pi_i(E_r(v) intersect pred(i)); later inputs do not affect it. It must be
zero, or i would supply k. Thus i too is captured under that r-prefix.

At the end, fixing every original r-input captures every remaining input.
The entire cofactor is constant; evaluating all its free inputs at r shows
the constant is r by nonempty conservativity. Therefore every singleton
row has an r-forcing monochromatic cofactor. In particular the singleton
predicate depends only on the r-atomic positions, without assuming that
factorization separately.

## Each owner profile is principal

Fix r, put q_i=pi_i(all predecessors colored r), and let
M_r={i:q_i=1}. Inductively

    pi_i(M_r intersect pred(i), colored r)=q_i.

Indeed every earlier h outside M_r is already captured under its M_r
prefix. Fix the current M_r prefix to r and give i the sole queried
winner k!=r, with other inputs initially N_k. Full FD permits recoloring
the earlier captured inputs to r without changing that winner. The two
source-i coefficients are the displayed left side and q_i.

It follows that fixing M_r to r captures every other source, so makes
the whole cofactor constantly r. Conversely an r-forcing coalition A
cannot omit i in M_r: antitonicity gives
pi_i(A intersect pred(i))>=q_i=1, and the sole-source k-probe contradicts
the supposedly constant r output. Together with singleton factorization,

    Phi_r(A)=1 iff M_r subseteq A.

M_r is nonempty, since an everywhere constant r operation contradicts
conservativity at a different diagonal. These are necessary structural
constraints for every genuine core operation with acyclic source dependence.
They do not assert that principal profiles suffice for acyclicity or for
core realization.

## Color-block elimination

For a source j, suppose pi_j(E)=0. Let T color inputs other than j and
extend E, possibly using every owner. If each source i in T_s satisfies
pi_i(T with its s-block erased)=0,
then pi_j(T with its s-block erased)=0 as well.

Give the uncolored inputs N_s. With j=N_s all possible s-sources are
in T_s and are blocked, so F omits s. If the asserted conclusion failed,
changing j to s would supply s. Full FD under E forbids that change.
This proof uses the full source formula; it is not merely a closure law
for the individual owner profiles.

## A shared retained source under proper fixed contexts

Let E fix a proper coloring of predecessors, and suppose every earlier
free source than j is captured under E, while pi_j(E)=1. Then j is
retained both in the conditional function F_E and in H_E, the neutral
residual deleting the fixed-context variables.

For F_E, earlier free sources are inessential under E. To query any
k in the input at j, replace them by N_k. Antitonicity gives
pi_j(E with its k-block erased)=1, so j supplies k. Restore the earlier
menus using FD.

For H_E, suppose a proper predecessor coloring A has pi_j(A)=0.
It colors only the free predecessors, so is compatible with E.
If E union A is proper, antitonicity and earlier-source FD give
0=pi_j(E union A)=pi_j(E), a contradiction. Otherwise choose an owner s
unused by E. Every source in A_s is an earlier free source captured under
E. Color-block elimination gives pi_j((E union A) with its s-block
erased)=0. That context is proper and still contains E; earlier-source
FD again removes the free colors, contradicting pi_j(E)=1.
Thus all predecessor coefficients in H_E are one and j is retained.

If no free source is active at E, the whole conditional function is
constant. This gives a canonical retained source at every nonconstant
proper-context node, shared with its total neutral residual.

## The unresolved assembly

The shared-root lemma alone does not assemble those conditional functions.
For a globally retained root A=q, let C=partial_A F. One needs a lower-arity
core erasure g_q<=C that agrees with F(q,.) outside q. Its atomic cofactors
must in turn be assembled below ONE common neutral baseline. Independent
lower-arity realizers do not establish this compatibility.

A concrete maximal antitone fill for the missing q-facet is

    pi_i^q(E) = pi_i(E with A neutral)
                AND AND_(s!=q) pi_i(E with its s-block erased, A=q).

Every factor is an original proper coloring. On every facet missing a
foreign owner s!=q it agrees exactly with the prescribed A=q cofactor;
it is bounded by the neutral baseline and preserves the source order.
The shared-root lemma makes its first active source retained. This maximal
fill nevertheless FAILS full colored FD, even for an actual acyclic core
operation. The failure and the missing repair are explicit below.

## Maximal fill can preserve dependence on a deleted source

Fix q and a foreign owner r. Use retained roots A and R_t for every t!=q,
and two additional inputs D,Z. In this paragraph + denotes derived union.
Put

    U=SUM_(t!=q) R_t,
    H=U+SUM_(t!=q)(Z choice_t R_t),
    G=D+H+(Z choice_r D),
    J=A+U+(D choice_q A),
    F=J+H+(G choice_q A).

This is an explicit core word, so all its semantic FD laws hold. Its
complete source predicates are

    pi_A=pi_(R_t)=1,
    pi_D=NOT A_q,
    pi_Z=NOT(D_r AND AND_(t!=q)(R_t)_t).

For pi_Z the syntactic word initially gives
NOT A_q AND NOT D_r, disjoined with NOT(R_t)_t over the roots. The
difference from the displayed predicate would require A=q together with
every foreign root R_t=t, using ALL owners; no proper source coloring
has this pattern. Thus the displayed family is exact and its graph is
acyclic, in order A, roots, D, Z.

At A=q, the cofactor is q+U+Z, independent of D. Indeed H contains Z
unless every root has its indicated foreign color; at that exceptional
root pattern q+U=I already. The total neutral-A residual is G.
Maximal fill makes pi_D^q=0 everywhere. But every foreign-deletion
factor of pi_Z^q is one (deleting color t removes its own root literal),
so it leaves pi_Z^q=pi_Z, from the neutral-baseline factor alone.
At R_t=t, Z=q, its output is N_q for D=r and I for D=q.
Thus a globally captured D still affects the output, which is impossible
for a core operation.

The correct erasure H<=G has pi_Z=NOT AND_(t!=q)(R_t)_t and ignores D.
It agrees with the A=q cofactor outside q: at the rainbow roots, U
already contains every non-q winner. The maximal fill must therefore be
shrunk by propagating captured-source equivalences into later guards.
The example has K+2 variables for every K>=3 (five variables at K=3).

One candidate repair is to process sources topologically and take the
greatest antitone predicate below the initial maximal fill which respects
the captures of the already processed sources. In this example it gives
exactly H. Preservation of all prescribed foreign facets, particularly
when an equivalence path crosses the missing-q facet, remains unproved.

## Relative erasure and dependency compatibility

Bare relative erasure is false. Given a fixed s, put

    h={s} union x,
    D=UNION_(r!=s) (x choice_r y_r).

Every foreign winner r of x survives in its own summand, so h<=D+{s}.
At x=s, y_r=r, however, h=s and D=I\{s}. An erasure g<=D matching h
outside s would have to be empty there; a globally zero g fails at foreign
diagonals. Thus the missing baseline compatibility cannot follow from
inclusion alone. This example also violates dependency compatibility:
D captures x at the displayed foreign-anchor context, while h still
depends on x.

Dependency compatibility does remove that elementary empty-value obstruction.
Normalize h={s}+G with G a nonempty constant-free core. Suppose G(v)={s}
but s is absent from D(v). The proper coloring of v's foreign atomic
positions gives a zero D-source coefficient for every input containing s.
Compatibility therefore makes h independent of all those inputs there.
Replace them by N_s. The value h stays {s}, but now every input omits s,
so provenance and nonemptiness of G make that impossible. Consequently

    (h(v) without s) union (D(v) intersect {s})

is always a nonempty pointwise erasure with the required bound and foreign
memberships. Nonemptiness does not ensure core realization, as follows.

### Compatibility, a DAG baseline, and a common retained root still fail

Let C be the s-owned fold of anchors y_r for r!=s, U their ordinary union,
and introduce another input B. Put

    G=x+B+C,
    D=B+U+SUM_(r!=s)(x choice_r y_r),
    h={s}+G.

The baseline D has a source DAG: B and every anchor are retained; x is
captured precisely at the foreign-rainbow context y_r=r for every r!=s.
At that context C=N_s and h=I regardless of x, so h respects EVERY
colored capture of D. Both retain B. Also G without s is contained in D:
the r-owned summand retains every r-bit of x, while B+C is covered by B+U.

Suppose a core erasure g<=D matched G outside s. Enlarge it by B+C;
this preserves both requirements. G retains every s-bit in every input,
so provenance gives g_s<=G_s. Hence, with C0=B+C,

    C0 <= g <= C0+x.

At foreign observers its x-coefficient is identically one. In the interval
I(C0) this forces lambda_s=1. But Phi_s(C0)(A) says that A contains B
and at least one anchor. On the coloring y_r=r, with B uncolored, every
foreign-deletion complement contains B and another anchor, so theta_s=1.
The universal derangement law forces g to retain s from x=s. At B=N_s
the bound D is N_s, a contradiction. This works uniformly for K>=3.

The obstruction's foreign predicates in h depend cyclically among the
anchors through C. Thus it does not refute the acyclic-cofactor assembly
problem: there the foreign source data of h must share D's source order.

### Positive case: a greatest-profile-completion baseline

If D is a profile maximum, dependency compatibility alone makes G<=D,
so G itself is an eraser. On a monochromatic r-winning coalition A of D,
all other inputs are D-inessential. Compatibility makes h constant there,
equal to {s,r} by substituting all remaining inputs r. For r=s this forces
G=s. For r!=s choose a third owner t and set every unfixed input to t.
Provenance excludes s from G, so G=r with exactly A as its r-atomic set.
The r-profile of G therefore forces r throughout this cofactor. Thus
G agrees with D wherever D is singleton; elsewhere D is the full input
union and contains G. General baseline assembly needs more than these
singleton-profile constraints.
