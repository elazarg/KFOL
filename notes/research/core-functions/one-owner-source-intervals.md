# Exact separable source extensions of one-owner traces

Written mathematical results, not Lean claims. The full unrestricted
joint-guard characterization remains open.

The proof is in
[appendix-core-one-owner-intervals.tex](../../../sections/appendix-core-one-owner-intervals.tex),
`core:thm:one-owner-source-interval`.

Let C be the r-only trace of any loopless closure c on a finite nonempty
passive support V. Add a source X with separable normalized factors B_s,
and put psi_s = not B_s. The synthetic interval operation is core exactly
when these two subset laws hold:

1. psi_r(c(E)) = psi_r(E).
2. For s != r, E disjoint A and psi_r(E)=0 imply
   psi_s(A \ c(E)) = psi_s(A).

These are also equivalent to full colored-cofactor independence for this
candidate. The construction attains the entire canonical full type at one
X occurrence in a primitive spine S, with F=C union S.

For each nonzero foreign psi_s, generate a Horn closure d_s by
E -> c(E) when psi_r(E)=0, and E -> V when psi_s(V\E)=0.
The second subset law proves that its spanning predicate is exactly
not psi_s(V\E). The r-inner/s-outer CNF of d_s therefore has s-profile
psi_s and is bounded by C wherever psi_r(E_r)=0. Use complements of
all proper closed sets, not merely maximal ones. When psi_r is nonzero,
the own-owner helper is the r-trace of c_f, where c_f(E)=V on psi_r(E)=1
and c_f(E)=c(E) otherwise. It is bounded by C and has profile psi_r.
Attach foreign helpers first and the own-owner helper last. Its absorption
protects exactly the stratum on which the foreign helpers need no bound.

This does not give a single-spine theorem over arbitrary multi-owner
baselines. The four-variable counterexample in
[appendix-core-box-repetition.tex](../../../sections/appendix-core-box-repetition.tex),
`core:prop:one-box-two-copies`, is a separable interval above a profile
maximum with box rank one and minimum named-union X count two. Its
canonical maximal full type is not actual, so there is no greatest
actual full type. The obstruction is the empty rainbow intersection of
the forced helper coalitions {x,z}, {y,z}, and {x,y}.

## General terminal functional interface

For an arbitrary genuine source-separable core baseline C with closures
c_t, the same proof gives a precise FD equivalence (not yet a core
realizability criterion):

    psi_t(c_t(E)) = psi_t(E);
    psi_s(A \ c_t(E)) = psi_s(A)
        if s!=t, E disjoint A, and psi_t(E)=0.

The full proof is `core:lem:terminal-closure-laws` in the same report
file. If exactly one mask t is positive at a valuation but C omits t,
every t-atomic source is captured by some foreign owner with zero mask.
The second law removes all these sources while preserving psi_t=1,
contradicting normalization. Thus the synthetic operation has the simpler
whole-menu formula: F=C union X when every mask is zero, and F=C
otherwise. For an old captured input j, choose a capturing owner t.
If its mask is positive, F=C for every menu of j. Otherwise the two
laws make all masks invariant under j, proving full functional
independence. The new-source case follows immediately from the formula.

The current synthesis question is whether these two laws suffice to
adjoin a terminal separable source above any genuine separable core
baseline. This adds no dependency cycle, but the one-owner construction
does not extend directly: the four-variable example already disproves
attainment by a single spine with the canonical maximal full type.

## No owner-only bound on exact spine order

`core:prop:ordered-reset-witnesses` in the box-repetition report file
gives a second limitation. Let T_m be a serial spine starting at X,
with helpers v_i and alternating owners a,b, and put
F_m=T_m union partial_X T_m. This is a separable interval, with
one-box X predicate and a one-X named-union realizer. Every primitive
one-X minorant attaining that full type needs at least m gates.

For each i, let L_i be the last r_i gate whose helper has positive
r_i-profile on {v_i}. A two-reset valuation vi=r_i, vj=r_j,
all other variables and X the third atom c, forces L_i<L_j whenever
i<j and r_i!=r_j. Otherwise the proposed minorant retains r_i when
F_m omits it. In the alternating case L_1<...<L_m. Arbitrary passive
core helpers do not evade the argument. Thus a finite list of owner
orders depending only on K cannot serve as a complete normal form.

The neutral residual in this example is generally NOT the passive
serial spine. For m=2 it is (v1 union v2) choice_b v2. Separability
follows instead by restricting the original read-once source predicates.
