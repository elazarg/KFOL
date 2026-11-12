# The pointwise lower envelope of an exact profile fibre

Mathematical research, without Lean claims. Prescribing negative as well
as positive singleton-profile bits changes the lower envelope. The
complete one-bound theorem gives a closed formula with two certificate
families: positive rainbows and same-owner separators. It computes the
pointwise intersection of the exact profile realizer values, without
asserting that this intersection is itself realized by one word.

Fix finite owners I with K>=3, a finite nonempty variable set V, and an
admissible complete profile tuple Phi. Thus there is at least one core
word with exactly these profiles. At a winner valuation w put

    W_k={i:k in w_i},       E_r={i:w_i={r}}.

Define J_Phi(w) to contain k when either of the following certificates
exists.

## The two certificate families

A **rainbow certificate** is a choice of one coalition A_r per owner with

    Phi_r(A_r)=true for every r;
    empty != C=intersection_r A_r subseteq W_k;
    E_r intersects intersection_(s!=r) A_s = empty
        for every r!=k.                                  (1)

This is the positive-profile lower envelope R_Phi from
[read-once-profile-minimum.md](read-once-profile-minimum.md).

A **separator certificate** consists of an owner r and coalitions A,B with

    Phi_r(A)=true,       Phi_r(B)=false;
    A\B subseteq W_k;
    r=k or E_r subseteq B;
    E_s intersects A = empty for every s outside {r,k}.   (2)

The difference A\B is automatically nonempty by profile monotonicity.
All data in (1),(2) belong to the prescribed profiles and the query
valuation. Neither certificate contains a term or an auxiliary invariant
presentation.

## Exact pointwise intersection theorem

**Theorem.** For every valuation w,

    J_Phi(w)=INTERSECTION {S(w):S is core and profiles(S)=Phi}. (3)

In particular R_Phi(w) subseteq J_Phi(w), and a winner outside J_Phi(w)
has an exact-profile realizer omitting it. That realizer may depend on
the query valuation and winner.

Fix k and put U=I\{k}. A word omits k at w exactly when its output is
contained in U. Apply the complete exact-profile one-bound criterion in
[profile-bounds.md](profile-bounds.md). Its top-bit condition holds by
admissibility. It requires all same-owner true/false pairs to be safe,
and every positive full rainbow to satisfy the bounded rainbow test.

For a same-owner pair A,B at owner r, PairSafe_U is the disjunction

    (A\B) intersects {i:w_i subseteq U}; or
    r in U, A\B nonempty, and E_r\B nonempty; or
    A\B nonempty and E_s intersects A nonempty
        for some s in U\{r}.

The first set is V\W_k; the difference is nonempty. Thus failure of
all three alternatives is precisely (2).

For a positive full rainbow, admissibility gives C!=empty. Its bounded
test requires either an input menu w_i subseteq U at some i in C, or
an allowed owner r!=k with a singleton position in the intersection of
the other coalitions. Failure of this test is exactly (1).

Consequently an exact-profile word omitting k exists if and only if
there is no certificate of either kind. Taking the Boolean complement
proves (3), including existence of an omitting realizer whenever k is
not in the displayed closed envelope.

The argument uses the complete one-bound theorem, not a necessary-only
estimate of that theorem. In particular it gives both directions of
pointwise forcing.

## Positive and exact profiles can give different answers

For a primitive read-once word T, its positive-profile envelope already
equals T. Since T itself is an exact-profile realizer, (3) gives
J_(Phi^T)=T as well.

There is a different situation for the mixed three-owner minimum

    F=(X choice_1 Y) choice_0 (Y choice_2 Z).

Its complete profiles are

    Phi_0=Y AND (X OR Z),       Phi_1=Y AND Z,
    Phi_2=X AND Y.

The [mixed-CNF theorem](mixed-cnf-minimum.md) proves that F is the least
operation in this exact profile fibre. Hence J_Phi=F. At W=(1,0,2),

    J_Phi(W)={1,2},       R_Phi(W)=empty.

For the second equality, both F and projection Y retain every positive
bit of Phi, while their outputs at W are disjoint. In the exact-profile
fibre, the false bits supply the missing certificates. For example to
force winner 1 at W, use r=0,A=XY,B=Y in (2). Its difference is {X},
which supplies 1; E_0={Y} lies in B, and E_2={Z} misses A. To force
winner 2, use r=0,A=YZ,B=Y instead.

Thus discarding negative profile data can lose every winner even when
the exact profile fibre has a genuine least core operation.

## What remains joint

The set J_Phi(w) may be empty. The witnesses omitting its missing winners
need not be the same word, either across winners or across valuations.
Nothing in (3) alone asserts that J_Phi is core, has exactly Phi as its
own singleton profiles, or is an exact-profile least element.

Even the necessary interval condition

    J_Phi(w) subseteq F(w) subseteq E_Phi(w)

does not characterize membership in the core profile fibre. The existing
five-point profile-fibre nonconvexity theorem supplies a noncore function
between two actual core operations with those same profiles. Its lower
core bound is one exact-profile realizer, so the noncore function is
above J_Phi. It is also below the greatest profile completion E_Phi. See the
[profile nonconvexity result](README.md#greatest-completions-and-gaps-in-core-realizability).

The formula isolates exactly what one valuation and complete profile
data force. The full target still requires compatibility of the complete
source guards over all valuations.
