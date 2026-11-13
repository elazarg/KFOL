# Exact full types and source counts above profile maxima

Written mathematical results, not Lean claims. The proofs are in
[appendix-core-interval-types.tex](../../../sections/appendix-core-interval-types.tex):
`core:thm:profile-interval-types`, `core:cor:profile-interval-copy-number`,
and `core:cor:profile-interval-greatest-type`.

Let C be a greatest singleton-profile completion on nonempty passive
support W, with profiles f_a. Let F be any core interval operation
C <= F(X,w) <= C union X, with complete source predicate P_F.

For normalized antitone factors B_r, put psi_r=not B_r and
R={r:psi_r is nonzero}. A primitive one-X spine has exactly the owners
R on its path. This assertion does NOT apply before linearization:
X choice_a X has trivial full type despite its a-owned path gate.

## Complete criterion

B is an actual full occurrence type of F exactly when:

1. Its box P_B(E)=AND_r B_r(E_r) is contained in P_F.
2. For every r in R, f_r <= psi_r.
3. For every r in R, every psi_r-positive coalition A and every selection
   of f_a-positive coalitions A_a at the inactive owners a outside R have
   nonempty common intersection A intersect INTERSECTION_a A_a.

There are no unknown realizing terms in these conditions. The last two
conditions depend only on the baseline and the proposed factors.

For fixed R the mask parameters are independent. Define h_J(A) by requiring
A to meet EVERY intersection of one positive f_a coalition per a in J
(empty J gives intersection W). Then the baseline-compatible masks are
exactly f_r <= psi_r <= h_(I\R) at active owners, with psi_a=0 at the
others. These monotone-profile intervals are all nonempty by baseline
admissibility. Soundness is the remaining constraint depending on F.

Necessity uses marked linearization and the general
`core:lem:linear-profile-inheritance` from
[neutral completions](../../../sections/appendix-core-neutral-completions.tex).
Inactive owners have no path gates;
putting X=a on a C=a row forces every helper to equal a, so helpers inherit
every inactive profile f_a. At an r-gate, its helper profiles OR to psi_r.
Selecting a helper positive on A and using profile admissibility gives
the common-intersection condition. An active r's deleted profile is
nonzero, preserved in the neutral residue, and bounded by psi_r. Since
the residue lies below C, this gives f_r <= psi_r.

For sufficiency synthesize H_r with own profile psi_r, all inactive
profiles f_a, and unanimity at the other active owners. Attach H_r to X
at r for each active owner, then attach C once at each active owner.
The second phase's extra factors are redundant because f_r <= psi_r.
It restores every active singleton stratum; inactive singleton strata are
safe by profile inheritance. On ambiguous C the passive union contains
every helper. The result is a safe one-X spine with exactly B and at
most 2|R| marked-path attachments, irrespective of helper size.

## Exact multiplicity and greatest types

Let b_C(P) be the minimum number of boxes contained in P, covering P,
and satisfying conditions 2--3. Then b_C(P_F) is EXACTLY the minimum
number of X leaves in a realizer with union named. Any expression's
occurrence types give the lower cover. Conversely union the synthesized
one-X spines with C. Named-union linearization simply skips union nodes.
The empty predicate has the empty cover and is realized by C alone.

Recover the canonical pure factors D_r(E)=P_F(only E colored r).
For a nonzero source family, a greatest actual full type exists exactly
when D is sound and satisfies conditions 2--3. Soundness of D is exactly
separability of the new-source family. Necessity follows because pure
probes bound all actual factors by D, while the coordinatewise union
of a realizer's actual factors equals D.

The four-variable majority example has box rank one but relative rank
two: c:{x,y}, a:{x,z}, b:{y,z} fail the common-intersection condition.
This now follows directly from the criterion, replacing its separate
nonattainment argument in the report.

## What remains for a general baseline

The profile conditions above remain necessary for any core baseline.
The use of a profile maximum in sufficiency is precise: every ambiguous
baseline value is the whole passive union, so helper values cannot leak.
For a smaller baseline there are simultaneous value bounds as well.

For example, a safe one-X spine with type B forces EVERY helper below C
on the no-mask region where all psi_r(E_r)=0. With ambiguous X no helper
absorbs there, so every gate unions; testing X=I\{k} forces every helper
to omit each k outside C. For a type omitting owner a, the same bound
also holds throughout theta_a^C, because inherited a-profiles prohibit
all foreign helper absorptions there. These are simultaneous bounds;
pointwise one-bound feasibility does NOT synthesize a common helper.
The three-passive-variable counterexample in
[profile-bounds.md](profile-bounds.md#remaining-target) has a genuine core
baseline C and one active mask. Its exact inherited profiles extend C's
profiles and have a bounded helper at every individual input (two explicit
helpers cover all inputs), but two atomic rows exclude any common helper.
The corresponding sound full type is not actual in the known core interval
C union T (`core:cor:pointwise-helper-obstruction`). This is separate from
the five-variable terminal counter, whose pointwise helper obstruction was
already enough to exclude a realization.

This solves the profile-maximum interval type problem, not arbitrary
joint guard realizability or the general interval type spectrum.
