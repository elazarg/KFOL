# Colored feedback elimination and a three-owner obstruction

Mathematical research, without Lean claims. Pair-cut, reciprocal
shared-witness compatibility, hereditary common-source admissibility and
functional cofactor dependence do not suffice, even together. A four-variable
counterexample works for every finite owner set with at least three elements.
Its proper neutral faces and identification minors are core operations.
Unlike the earlier [two-rule obstruction](separable-closure-counterexample.md),
its pure-owner closures cannot come from **any** core operation, including a
nonseparable one.

The proof gives an additional structural law on arbitrary core closures.
Three differently colored captures cannot form a conditional triangle unless
the remaining context already captures the whole triangle. This follows from
two elementary profile bridges and an induction; no enumeration is needed.

## A uniform four-row invariant

Write r,s,t for three distinct owners, I for the whole owner set, and
N=I\{r}. Use variables x,y,z,W and the following four valuations:

| row | x | y | z | W |
|---|---|---|---|---|
| a | {r} | I | {r} | {r} |
| b | I | {s} | {s} | N |
| c | {t} | {t} | I | N |
| d | {s} | {r} | {r} | {r} |

Every subword H has values in the following small domains:

    H(a) in {{r},I};
    H(b) in {{s},N,I};
    H(c) in {{t},N,I};
    H(d) in {{r},{s},{r,s}}.                         (1)

There is no atomic input of any fourth owner at these rows. Such an owner's
singleton profile is therefore false throughout every subword, so its gates
act as union. The same observation determines which gates act as union at
each of the four rows for r,s,t.

The following two implications hold for every core word:

    H(a)={r}, H(b)={s} imply H(c)=I;                 (B1)
    H(a)={r}, H(c)={t} imply H(b)=I.                 (B2)

For (B1), induct on H. An r-root has a child with a-value {r}, and both
children have b-value {s}; choose that child. Its c-value I persists because
the r-gate acts as union at c. At an s-root choose a child with b-value {s};
both children have a-value {r}, and again the child's I persists at c.
At a t-root both children satisfy the two premises and therefore both have
c-value I; the t-gate cannot absorb either of them. Other owners act as
union. The projection cases are immediate: only z satisfies both premises,
and its c-value is I. Interchanging b,c and s,t proves (B2).

Now induct again to prove

    H(a)={r}, s in H(d) imply H(b)=I or H(c)=I.      (B3)

At an r-root, neither child may have d-value {r}, since that would absorb s.
Both children therefore contain s at d. Choose a child with a-value {r};
its witness from (B3) persists at b or c, where an r-gate is union.

At an s-root, both children have a-value {r}. Choose a child carrying s at d.
If its witness is I at c, it persists. If its witness is I at b, the only
way to erase it is a sibling with b-value {s}. That sibling satisfies (B1)
and has c-value I, which persists. At a t-root the argument is symmetric:
an I-witness at b persists, and erasing one at c forces a sibling with
c-value {t}, hence b-value I by (B2). Other owners act as union.
Among projections only x satisfies the premises of (B3), and its b-value
is I.

In particular every core word satisfies

    H(a)={r}, r notin H(b), r notin H(c)
        imply s notin H(d).                         (2)

The auxiliary implications explain exactly why a foreign-owned gate cannot
hide both negative rows while preserving the positive row.

## The stronger context consequence

Replace W by a finite context block L: every member of L has the displayed
W-column. Let Phi_r^H be H's owner-r singleton profile, and put

    A=L union {x,z}.

There is a stronger three-row statement:

    Phi_r^H(A), r notin H(b), r notin H(c)
        imply Phi_r^H(L).                           (3)

The same two bridges give a direct induction. At an r-root the two negative
budgets pass to both children because r acts as union on b,c. Choose an
A-positive child and apply induction. At an s-root both children are
A-positive. The c-budget passes to both because c has no atomic s input.
Bridge (B1) then excludes b-value {s} for either child, so the s-root acts
as union at b and both b-budgets pass too. Both children satisfy the
induction hypothesis, giving their r-profiles at L and therefore the
parent's. At a t-root use (B2) in the same way. Other foreign roots pass
both budgets and require both child profiles. A projection satisfying the
three premises lies in L: x violates the b-budget, z violates the c-budget,
and y is not in A.

Consequently, let c_u be the canonical pure-owner closures of any core
operation, on its essential support. For distinct x,y,z and a disjoint
context L, the following implication holds for distinct owners r,s,t:

    y in c_r(L union {x,z}),
    x in c_s({y,z}), z in c_t({x,y})
        imply {x,y,z} subseteq c_r(L).               (C3)

To prove this, take the neutral residual on U=L union {x,y,z}. Neutral
elimination leaves a genuine full-support core word, whose closures are
c_u(E) intersect U. The first premise makes its r-profile true at A.
The second makes x inessential when y=z={s}; since x is the only possible
r-source at b, this gives the b-budget. The third gives the c-budget.
Statement (3) says c_r(L) contains U. Closure monotonicity translates this
back to the original operation. If L is empty, looplessness makes the
antecedent impossible.

Thus (C3) is a law on the given closures, without a realizing-word witness
or a source-separation assumption. It implies both weaker exchanges that
replace x or z in the initial coalition by y, but asserts more: all three
heads were already consequences of the context alone.

## A general feedback elimination law

The same argument works with blocks and any finite family of queries,
including several queries with the same owner. Fix an observing owner r
and a finite index set J. Give each index i an owner s_i!=r and sets
X_i,P_i of variables. Require

    X_i intersect P_i = empty;
    X_i subseteq c_(s_i)(P_i);
    A intersect P_i = empty, or some j has
        s_j!=s_i and A intersect P_i subseteq X_j.   (7)

Assume also

    UNION_i (P_i union X_i) subseteq c_r(A).          (8)

Then the canonical closures of every core operation satisfy

    c_r(A)=c_r(A\UNION_i X_i).                       (FE)

Everything in this implication is given closure data. Condition (7) is
a direct cover test among the displayed coalitions; it supplies no
elimination order, occurrence graph, or unknown realizing object. An
empty intersection needs no second query.

Here is the profile bridge needed for the proof. If a word has both
Phi_r(A) and Phi_s(P), and a valuation v has no atomic r or s input
and gives every member of A intersect P a menu containing r, then
r belongs to its output. Induct on the word. At an r-root choose an
A-positive child; both children are P-positive, and the r-gate acts
as union on v. At an s-root do the reverse. At any other root both
children retain both positive profiles, hence contain r by induction;
neither can be the absorbing singleton of that other owner. A leaf
lies in A intersect P, so contains r. When the intersection is empty,
ordinary rainbow common-source persistence already excludes the two
positive profiles.

Take the neutral residual on

    U=A union UNION_i (P_i union X_i).

Assumption (8) makes its r-profile positive at A. At row q_i, put I
on X_i, the s_i atom on P_i, and N_r elsewhere. The capture condition
in (7) and simultaneous cofactor independence imply that q_i omits r.
Replacing X_i by N_r leaves the same output, and then all inputs omit r.

Induct on a word satisfying that positive profile and all the row budgets.
At an r-root every budget passes to both children, and one child is
A-positive. At a foreign root u both children are A-positive. Every
budget q_j with s_j!=u passes directly, because that query has no atomic
u input. For an index i with s_i=u, neither child can have its u-profile
positive at P_i. If A intersect P_i is empty, the two positive profiles
would contradict rainbow common-source persistence. Otherwise (7) gives
an index j of a different color whose budget has already passed to both
children. The bridge would put r in that child's q_j output, again
contradicting its budget. Thus no u-profile blocker exists at any
u-colored query, and all those budgets pass too. This also covers owners
absent from the index family. Induction makes the r-profile positive at
A\UNION_i X_i: at an r-root one positive child suffices, and at every
foreign root both are positive. A leaf satisfying all budgets must lie
in that set.

Consequently U subseteq c_r(A\UNION_i X_i). In particular A is
contained there, so closure idempotence and monotonicity give (FE).
If U or J is empty the identity is immediate.

The one-query-per-owner version can instead use S subseteq I\{r} and
a map f:S->S with f(s)!=s and A intersect P_s subseteq X_(f(s)). This
implies (7). The two-owner block case swaps s,t. Choosing

    A=L union {x,z};
    X_s={x}, P_s={y,z}; X_t={z}, P_t={x,y}

recovers (C3). If A\UNION_i X_i is empty while A is nonempty,
looplessness makes (7)-(8) impossible for a genuine core system.

This is a closed necessary elimination law, with arbitrary block sizes
and arbitrarily many queries at a fixed owner count. Its sufficiency,
with the earlier laws, has not been established.

## A counterexample to the previous closure laws

Specialize to owners r=0,s=1,t=2 and variables V={x,y,z,W}. Define

    c_0(E)=E union ({y} if {x,z,W} subseteq E else empty);
    c_1(E)=E union ({x} if {y,z} subseteq E else empty);
    c_2(E)=E union ({z} if {x,y} subseteq E else empty);
    c_u(E)=E for every other owner u.                (4)

These are loopless closures. Their source-separable reconstruction is

    F(w)=W
         union (x unless y=z={1})
         union (y unless x=z=W={0})
         union (z unless x=y={2}).                   (5)

Here a variable on the right denotes its whole input menu. An omitted
term contributes the empty set. The unconditional W makes F nonempty.
The three trigger patterns are mutually incompatible, so at most one
head is suppressed at a valuation.

The earlier tests all hold:

* **Pair-cut (P).** If one rule fires, using its added head to fire a
  differently colored rule would require another premise shared by both
  rules to have two different owners. The disjoint premise sets in (P)
  cannot do this. Hence no new second head escapes the existing closure
  union.
* **Reciprocal intersection (CI), equivalently (C2) given (P).** The
  0/1 reciprocal pair shares z, the 0/2 pair shares x, and the 1/2 pair
  shares y, after removing the two heads.
* **Hereditary common-source (H).** In any retained set containing W,
  every spanning coalition contains W, since no closure captures it.
  Without W, only the 1/2 pair remains. On {x,y,z} its spanning
  coalitions both contain y; on smaller nonempty sets all restricted
  closures are identities.
* **Exact functional dependence.** Fixing x=z=W={0} makes F constantly
  {0}, independently of y. Fixing y=z={1} makes F={1} union W,
  independently of x. Fixing x=y={2} makes F={2} union W,
  independently of z. All remaining one-color essentials have their
  pure-source probes as witnesses. Thus (4) are the actual cofactor
  dependence closures of F. This also supplies omission independence,
  full old-value outcast and their neutral restrictions by the arguments
  in [cofactor dependence](cofactor-dependence-closures.md).

Its exact singleton profiles are xzW at owner 0, yzW at owner 1, xyW at
owner 2, and unanimity at every other owner. In particular they are
admissible, with common source W. On all-ambiguous inputs F is the input
union, so every variable is essential.

Nevertheless the four rows above give

    F(a)={0}, F(b)=N_0, F(c)=N_0, F(d)={0,1},

contradicting (2). Equivalently, (4) violates (C3): its premises hold
with L={W}, while c_0({W})={W}. This second argument rules out even
joint pure-port realization by a nonseparable core term.

## All proper input reductions are core

Deleting x,y or z neutrally leaves input union. Deleting W leaves
the shared-context two-rule operation

    y union (x star_1 (y star_2 z))
      union (z star_2 (y star_1 x)).                  (6)

All smaller nonempty neutral faces are therefore core as well. The empty
face is zero.

There are six pair-identification minors. Writing U for the identified
input, the following primitive-choice/derived-union words realize them:

| identification | word |
|---|---|
| x=y=U | W union U union (z star_2 U) |
| y=z=U | W union U union (x star_1 U) |
| x=z=U | W union U union (y star_0 (U star_1 W)) |
| W=x=U | U union (y star_0 (U star_2 z)) union (z star_2 (U star_0 y)) |
| W=z=U | U union (x star_1 (U star_0 y)) union (y star_0 (U star_1 x)) |
| W=y=U | U union (x star_1 (U star_2 z)) union (z star_2 (U star_1 x)) |

The last three use the two-rule common-context construction. Every
proper identification minor factors through one of these six and is
therefore core. Idempotence, essential support and the canonical factor
recovery argument from [block decomposition](block-decomposition.md)
then show that F has no proper disjoint idempotent decomposition: its
outer diagonal minor and its inner neutral factors would all be core,
making F core as well.

The obstruction therefore survives all proper neutral and identification
reductions. It does not say that such reductions or the new law (C3)
form a complete criterion. It refutes sufficiency of the preceding
pairwise laws even after all those reductions have been checked.
