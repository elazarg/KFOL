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
The shared-root lemma makes its first active source retained. Preservation
of full colored FD by this completion remains unproved.

Bare relative erasure is false. Given a fixed s, put

    h={s} union x,
    D=UNION_(r!=s) (x choice_r y_r).

Every foreign winner r of x survives in its own summand, so h<=D+{s}.
At x=s, y_r=r, however, h=s and D=I\{s}. An erasure g<=D matching h
outside s would have to be empty there; a globally zero g fails at foreign
diagonals. Thus the missing baseline compatibility cannot follow from
inclusion alone. This example also violates dependency compatibility:
D captures x at the displayed foreign-anchor context, while h still
depends on x. Whether the full dependency conditions suffice for the
needed acyclic erasure compiler remains open.

Dependency compatibility does remove that elementary empty-value obstruction.
Normalize h={s}+G with G a nonempty constant-free core. Suppose G(v)={s}
but s is absent from D(v). The proper coloring of v's foreign atomic
positions gives a zero D-source coefficient for every input containing s.
Compatibility therefore makes h independent of all those inputs there.
Replace them by N_s. The value h stays {s}, but now every input omits s,
so provenance and nonemptiness of G make that impossible. Consequently

    (h(v) without s) union (D(v) intersect {s})

is always a nonempty pointwise erasure with the required bound and foreign
memberships. Whether this allowable function, or a smaller function in
the same foreign trace, has a core realization is the remaining issue.
