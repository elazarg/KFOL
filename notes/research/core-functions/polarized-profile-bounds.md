# Polynomial polarizations do not complete positive-profile bounds

Mathematical research, without new Lean claims. All role sets, variable sets,
and terms in this note are finite. Fix an owner set I of size K>=3, and let
A_I be its nonempty winner subsets. Core terms use only I-owned choices,
without constants or role switches. A core polynomial is such a term with
arbitrary fixed elements of A_I also allowed as constants.

Every positive-profile lower-envelope requirement remains a (K+1)-row
condition, even after arbitrary finite circuits nesting the candidate operation
and using core choices and constants. This includes polynomial substitutions,
identifications, and cofactor sections. Consequently the existing Gray crowns
pass all of these requirements and are nevertheless noncore. This rules out
completeness of this entire family of tests; it does not supply the missing
intrinsic source-guard criterion.

## Canonical probes and the lower envelope

For r in I put N_r=I\{r}. For a finite variable set W and A subseteq W,
the canonical r-probe v_r(A) assigns {r} at A and N_r elsewhere. For any
nonempty-valued operation H on these variables define its probe bits by

    Phi_r^H(A)=true iff H(v_r(A))={r}.

For a core polynomial these bits depend only on the r-singleton statuses
of the variable inputs, by the usual singleton recursion with the constant
statuses fixed. For an arbitrary candidate H, the definition above merely
specifies probe values; no factorization or monotonicity is assumed.

Write E_r(w)={j:w_j={r}} and W_k(w)={j:k in w_j}. Define R_Phi(w) to
contain k when there are coalitions A_r, one for every owner, satisfying

    Phi_r(A_r)=true for every r;
    empty != C=intersection_r A_r subseteq W_k(w);
    E_r(w) intersect intersection_(s!=r) A_s=empty
        for every r!=k.                                  (1)

This is the closed positive-profile lower bound from
[the read-once profile note](read-once-profile-minimum.md). Its soundness
extends from core terms to core polynomials.

## Constants do not invalidate the rainbow obstruction

**Lemma.** For every core polynomial S,

    R_(Phi^S)(w) subseteq S(w).                           (2)

Replace each constant occurrence C_l in S by a new variable z_l, obtaining
a constant-free core term Q. It is enough to use one new variable per
occurrence; no independence of equal constants is required. At the query
valuation extend w by z_l=C_l. Given a certificate (1), extend its winning
coalitions by

    B_r=A_r union {z_l:C_l={r}}.

The singleton-status recursion shows Phi_r^Q(B_r)=true, since the original
probe for S has exactly these r-singleton inputs. A constant index belongs
to at most one B_r. Thus the common intersection of the B_r is precisely
C. In particular every input in that common intersection contains k.

For r!=k, a constant index whose query value is {r} belongs to none of
the B_s with s!=r. It therefore contributes nothing to
E_r(w,C) intersect intersection_(s!=r) B_s. The variable part is empty by
(1), so this entire atomic-deviation intersection is empty.

Apply the rainbow one-bound theorem from
[profile-bounds.md](profile-bounds.md) to Q with all owners demanded and
allowed output I\{k}. Its projection alternative fails because every
input in the common intersection contains k. Every allowed-owner absorption
alternative fails by the preceding atomic-deviation calculation. Hence
Q(w,C), and therefore S(w), cannot omit k. This proves (2).

## Local polynomial interpolation is closed under circuits

Call H m-point polynomial-interpolable when every m valuations, allowing
repetitions, have one common core-polynomial interpolant. Here the polynomial
may depend on the selected valuations.

**Circuit lemma.** If F is m-point core-interpolable, every finite acyclic
circuit built from F, I-owned choices, variables, and constants from A_I
is m-point polynomial-interpolable.

Fix m valuations w_1,...,w_m of the circuit's input variables. Induct over
its gates. A variable or constant leaf is already a polynomial. At an owned
choice gate, combine polynomial interpolants for its two children by that
choice. At an F-gate with child operations H_i, first choose a core term t
interpolating F at the m tuples

    (H_i(w_l))_(i in V), for l=1,...,m.

By induction choose polynomial interpolants s_i for the children at the
original m valuations. Then t(s_i:i in V) is a polynomial interpolant for
this gate, since its child values at every w_l are exactly H_i(w_l).
The circuit is finite and acyclic, so this constructs an interpolant for
its output. Shared gates can be unfolded into finite terms.

Different occurrences of F may use different interpolants t. The proof
does not require one term matching F at the combined input tuples of all
its occurrences. More generally, m-point polynomial-interpolability itself
is closed under composition by the same argument.

## The uniform locality barrier

**Theorem.** Suppose F:A_I^V -> A_I is (K+1)-point core-interpolable.
Let H:A_I^W -> A_I be the operation of any finite acyclic circuit using
F, I-owned choices, variables, and fixed winner-menu constants. Then H
satisfies the full positive-profile lower bound

    R_(Phi^H)(w) subseteq H(w) for every w.                (3)

To prove this, take k and a certificate (1) for H at w. By the circuit
lemma, choose one core polynomial S agreeing with H at the following
K+1 valuations, allowing repetitions:

    v_r(A_r) for each r in I,
    w.

Thus Phi_r^S(A_r)=true for every r. The coalitions in (1) are also a
certificate for S, so (2) forces k in S(w). Since S(w)=H(w), this proves
(3).

In particular, let T be any constant-free primitive read-once core term
on W. If H retains every positive profile bit of T, then

    T(w) subseteq H(w) for every w.                       (4)

Indeed the read-once certificate theorem expresses every k in T(w) by a
certificate (1) using positive bits of T. Those bits are also positive for
H, so (3) applies. The comparison term T may have any finite arity; only
one profile probe per owner and the query valuation are needed.

In particular the theorem applies to H(z)=F(p_i(z):i in V) for arbitrary
core polynomials p_i. These include projections, repeated projections, fixed
menus, and derived unions of independent variable blocks. Thus it includes
arbitrary variable identifications, arbitrary cofactor sections, ordinary
union polarizations, and every composition of these operations. It also
allows arbitrary nesting of F itself and branching circuits with multiple
occurrences of F; the candidate need not occur only once.

## Explicit noncore operations passing every such test

Choose d>=2 with 2^d>=K+1, and use the operation F_d on 2d inputs from
[the Gray-crown construction](exponential-crowns.md). It is 2^d-point
core-interpolable and is not a core operation. Interpolation is antitone
in the number of rows, so F_d is also (K+1)-point interpolable.

The theorem therefore applies to every finite circuit built from F_d,
core choices, and arbitrary fixed winner-menu constants, with any finite
input variable set W. Every such operation satisfies its full positive-profile
lower envelope (3), and hence every read-once comparison inequality (4).
Yet F_d itself is noncore.

These are genuine source-guard counterexamples: three-point interpolation
already supplies canonical monotone prime guards reconstructing F_d.
Therefore imposing all of these polarized profile bounds on a canonical
guard family cannot characterize joint realizability. The failure persists
even when all core-polynomial circuits nesting the candidate are tested,
rather than only substitutions, proper neutral sections, or atomic
restrictions.

The role set I stays fixed throughout. Each positive-profile certificate
uses only K+1 evaluations of the transformed operation, and local polynomial
interpolation is closed under arbitrary finite circuit composition.
Increasing the comparison arity or circuit size therefore does not escape
this locality barrier. The result does not rule out structural conditions
that couple unboundedly many guard observations in one requirement.
