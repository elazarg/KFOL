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
