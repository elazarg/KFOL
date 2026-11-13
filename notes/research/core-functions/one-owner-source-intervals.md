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
baselines. The strengthened four-variable counterexample in
[appendix-core-box-repetition.tex](../../../sections/appendix-core-box-repetition.tex),
`core:prop:one-box-two-copies`, is a separable interval above a globally
minimal profile maximum with box rank one and minimum X count two,
even in the primitive signature. Its baseline has majority-2 profiles
at a,b and unanimity at every other owner. Passive helpers have profiles
(a:majority-2,b:xy,c:xy) and its a/b swap, with unanimity elsewhere.
The two spines (X choice_c H_a) choice_b C and
(X choice_c H_b) choice_a C both contain C, so their c-choice equals
their union and uses exactly two X leaves. Its
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

## Primitive read-once baselines are now solved

The two terminal laws suffice over every primitive read-once baseline,
and over disjoint unions of such baselines. The complete written proof is
[appendix-core-read-once-extensions.tex](../../../sections/appendix-core-read-once-extensions.tex),
`core:thm:read-once-terminal-extension`.

There are three ingredients.

1. Single-mask rigidity: if only psi_s can be nonzero on a primitive
   read-once baseline, then it is zero or Phi_s(C). Every coalition
   failing Phi_s can be stripped to empty with foreign-owner capture
   contexts disjoint from the current coalition. Lift child captures
   using disjoint support. At an s-root strip both children; at a foreign
   q-root strip one failing child, then fix that whole child to q to
   capture the rest. Cross invariance preserves psi_s during stripping.
2. Terminal realization is preserved by disjoint baseline union. Extend
   the factor product to all pairs of proper component colorings,
   including globally full-palette pairs. Every nonzero section satisfies
   the component terminal laws. Its rows and columns are therefore actual
   interval predicates. Finite intersections of columns give a rectangle
   decomposition, and source composition realizes the rectangle products.
3. At a read-once root r, descend the laws from C=C1 choice_r C2 to
   D=C1 union C2. If psi_r is nonzero, synthesize H above D and take
   H choice_r C; on C=r the target must equal C, and elsewhere C=D.
   If psi_r=0, root capture forces every mask to vanish on coalitions
   contained in just one child. Pure-owner sections then have only one
   nonzero mask. Rigidity forces every nonzero psi_t to be
   Phi_t(C1) AND Phi_t(C2)=Phi_t(C), which has a direct spine realization.

Do not extend the rigidity lemma to named-union trees: input union has
arbitrary single-mask extensions. The union lemma is valid more generally,
but the read-once induction uses primitive choice children in its zero
root-mask branch. Repeated-variable multi-owner baselines remain the
unresolved terminal case; this theorem does not settle arbitrary cyclic
joint-guard compatibility.

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
