# Free independent-status polarization: extrema and a six-bit obstruction

Research note, 12 November 2026; these results are not yet Lean statements.

## Definition of the free extension

For a term t and owner r let f^t_r(E) be its r-singleton profile, where E is the set of variables assigned the r singleton. This is an ordinary monotone Boolean function. At an r-owned gate, profile r takes OR and every other profile takes AND.

For a source variable j and observer k, put independent Boolean flags a_(i,r) on all other variables i and rival owners r != k. A marked j occurrence contributes its usual product of owner factors; the free coefficient C^t_(j,k) is the OR of these contributions, now evaluated with the flags independent. It is antitone in the flags. On the one-hot domain it is the ordinary source coefficient of the WinnerSet operation.

These extensions really depend on the representing term. They are not determined by its WinnerSet operation.

At a gate t = u star_h v the free coefficient is

    C^t_(j,k) = C^u_(j,k) OR C^v_(j,k)                         if h=k,
    C^t_(j,k) = (C^u_(j,k) AND NOT f^v_h(E_h))
                OR (C^v_(j,k) AND NOT f^u_h(E_h))             if h!=k,

where E_h omits source j. This is the occurrence-path formula with independent flags.

## Positive result: a greatest term-induced extension exists

Fix a genuine WinnerSet operation F. All terms representing F have the same profiles f_r.

For every such term and r != k,

    C_(j,k) => NOT f_r(E_r).

Proof: delete every flag outside owner r. Antitonicity preserves a true coefficient. This leaves a valid one-hot source probe. If f_r(E_r) were true, F would be the r singleton there and could not contain k.

Consequently if u and v both represent F, the extra sibling filter at ANY gate u star_h v is redundant. The new term still represents F by idempotence, and its free coefficient vector is exactly the pointwise OR of the two original vectors.

There are finitely many free coefficient bits. Choosing finitely many F realizers covering all bits attained by any realizer and joining them gives a canonical greatest *term-induced* free extension of F. More strongly, the full actual occurrence types of the two realizers are unchanged at the macro gate; a finite universal F realizer contains every actual type.

This is an existence theorem. Defining the greatest extension by reference to all F realizers does not yet give an intrinsic guard characterization.

## The greatest arbitrary antitone completion need not be induced by any term

Given a one-hot coefficient C, its greatest antitone extension is

    C^max(A) = AND { C(B) : B <= A and B is one-hot }.

Equivalently, evaluate the canonical prime-guard DNF with independent flags. Its least antitone extension agrees with C on one-hot points and is false at every non-one-hot point.

The four-gate operation in `canonical-prime-occurrence-counterexample.md`,

    F=(a star_0 b) star_2 (a star_1 (b star_1 c)),

has canonical source-a, observer-2 coefficient

    [b != {0}] OR [c != {1}].

Its greatest arbitrary completion is therefore

    NOT b_0 OR NOT c_1.

But its exact maximal actual a types are LEFT and RIGHT from that note. Thus every representing term has free source-a, observer-2 coefficient at most

    NOT b_0 OR (NOT b_1 AND NOT c_1),

and the displayed term attains this bound. At b_0=b_1=true, c_1=false the arbitrary greatest completion is true while every term-induced extension is false.

## Negative result: even union has no least term-induced free extension

This needs only two variables and three owners. For a binary term define

    alpha = f_0({a}),       gamma = f_2({a}),
    beta  = f_1({b}),       delta = f_2({b}),
    X = C_(a,0) at b_1=b_2=true,
    Y = C_(b,1) at a_0=a_2=true.

Every term satisfies these five clauses:

    alpha => X,
    NOT (gamma AND beta),
    beta => NOT X,
    delta => NOT X,
    gamma OR X OR Y.                                      (P)

They define a closed 16-state relation on six bits. The leaves a and b satisfy it. At an h-owned gate the four profile bits use OR at their owner and AND at the other owners. The source bits update as follows, using unprimed/primed child values:

    h=0:  Xnew = X OR X'
          Ynew = (Y AND NOT alpha') OR (Y' AND NOT alpha)
    h=1:  Xnew = (X AND NOT beta') OR (X' AND NOT beta)
          Ynew = Y OR Y'
    h=2:  Xnew = (X AND NOT delta') OR (X' AND NOT delta)
          Ynew = (Y AND NOT gamma') OR (Y' AND NOT gamma).

The first four clauses are the usual singleton-profile/source and cross-owner disjoint-source implications, and are immediately preserved by these recurrences. For the last clause:

* At owner 0, Xnew=false forces X=X'=false, hence alpha=alpha'=false. Then Ynew=Y OR Y'; if it too is false, each child has gamma=true by (P), so gammanew=true.
* At owner 1, suppose gammanew=Xnew=Ynew=false. Then Y=Y'=false and one child has gamma=false, say the first. Its (P) gives X=true and hence beta=false. Xnew=false then forces beta'=true. The cross-owner clause gives gamma'=false, and the second child's (P) forces X'=true, contradicting beta'=>NOT X'.
* At owner 2, gammanew=false forces gamma=gamma'=false, so Ynew=Y OR Y'. If Ynew=false, both children have X=true by (P), and hence delta=delta'=false. Thus Xnew=true.

This proves (P) by ordinary term induction, without a clone enumeration.

Now every term representing binary set union has f_2({a})=false. Hence every such term satisfies

    X OR Y.

Consider the two standard union realizers

    U_0 = (a star_1 b) star_0 (a star_2 b),
    U_1 = (a star_0 b) star_1 (a star_2 b).

The free extension of U_0 has X=false; that of U_1 has Y=false. No term-induced union extension is below both, since it would have X=Y=false. Therefore the poset of term-induced union extensions is not downward directed and has no least element. In particular its least arbitrary antitone completion is not term induced.

## Optional complete binary check

Binary free semantics closes at exactly 43 records. A record consists of the three singleton profiles and the six source coefficient truth tables, each on two rival flags. There are exactly 18 records for the genuine union operation. For these records each coefficient is either mask 15 (unconditionally true) or mask 7 (false only at the impossible double-rival corner).

The suppressed coordinates form a subset of one row or one column in the 2-by-3 (source,observer) grid. Conversely every such subset occurs. This explains both the unique greatest extension and the absence of lower bounds for U_0,U_1.

Files:

* `free-polarization-six-bit-check.py`: self-contained 64-case relation/closure check; no table, enumeration discovery or external data needed.
* `free-polarization-check.py` and `free-polarization-binary.json`: independent check of a fixed closed 43-record certificate, with explicit term witnesses for every record. Closure plus witnesses proves the optional exact binary description.

## Scope

The natural least completion fails; the natural unrestricted greatest completion fails; a greatest term-induced completion exists. A short intrinsic description of that greatest coherent completion, or a general free-cube occurrence-saturation theorem, is not established here.
