# Conditional foreign traces are exactly tuples with a full-support minorant

Written mathematical proof, not yet formalized in Lean. The
conditional foreign closures of an actual core operation need not have a
common core realizer, even at an independent base. Their exact description
is weaker: their joint trace function has a full-support constant-free
minorant. An explicit four-owner core operation has a nonrealizable
three-owner tuple as such a conditional trace.

## Trace notation and the statement

Let I be a finite set of at least two foreign owners, and let B be a
finite nonempty variable set. Use the foreign choices together with union;
union is named explicitly when only two foreign owners remain. In the
full core with one additional owner rho it is a derived operation.

Write Q={0<a<b}, with +=max and

    u*v=0 if u=0 or v=0, and max(u,v) otherwise.

At coordinate s in I, choice_s is * and every other choice and union
are +. Put P_I=PRODUCT_(s in I) Q_s, and let P_I,0 also name its
all-zero tuple. These zero states are trace values, not the empty
winner-menu constant.

For loopless closures d_s on B let f_d be their coordinatewise trace
function. Its coordinate s is encoded by the interior

    J_s(C)=B\d_s(B\C).

On inputs 0 outside C, b on M subseteq C, and a on C\M, the value
is 0 when J_s(C) is empty, b when J_s(C) meets M, and a otherwise.
Each coordinate is a Q term, and the coordinate isolators in
[the pure-trace quotient](pure-trace-quotient.md) give f_d a P_I,0
realizer. It need not have a common constant-free realizer.

**Theorem.** The following are equivalent.

1. There is a core operation T over I union {rho}, with rho outside I,
   an independent base B for c_rho, and D=c_rho(B)\B, such that its
   conditional foreign closures are

       d_s(E)=c_s(E union D) intersect B, E subseteq B.   (1)

2. There is a constant-free foreign-choice/union word g using every
   variable of B, with

       g<=f_d pointwise on P_I                           (2)

   in the product chain order.

In the reverse direction only one additional variable is needed: D
can be a singleton. Thus (2) describes exactly the scope of conditional
foreign traces, rather than asserting that they themselves are term
operations.

## From an independent base to a minorant

Take the winnerwise ghost-neutral residual on U=c_rho(B)=B union D,
and choose a core word for it. This uses the established neutral-residual
theorem: its pure closures are c_s(E) intersect U. It is not literal
substitution of the empty winner menu into a word.

The residual's rho-profile is positive at B. It is negative at every
B\{j}, j in B, because independence excludes j from
c_rho(B\{j}); a spanning coalition would capture it. Thus B is an
inclusion-minimal winning rho-coalition.

Prune each rho-owned node to a child whose rho-profile is positive at B.
At every foreign node both children have positive rho-profile, so keep
both. The same holds for union nodes. Every surviving leaf belongs to B,
and the resulting constant-free word g has only foreign choices and union.
It uses all of B. Otherwise its rho-profile would be positive at some
B\{j}; pruning OR nodes to a child only decreases rho-profiles, which
would make the original residual positive there too.

Here is a direct membership proof of the bound. In the rho-player view,
menus containing rho have value P; foreign singleton menus retain their
atom, and other menus have value N. The order has foreign atoms below
N below P. A rho-owned gate is join in this order, and every foreign
gate is monotone. Pruning therefore decreases the rho-view at every
input.

Suppose j in d_s(E)\E. On the residual's pure-s source probe, put
j={rho}, all of E union D at {s}, and the remaining inputs at
I\{rho}. Only j contains rho, and its capture makes the original
output omit rho. The pruned output omits rho too. Since g has no D
variables, this is its pure-s probe on B, proving

    c_s^g(E) contains d_s(E) for every s,E.           (PM)

Equivalently its trace interior is contained in J_s(C), which proves
the pointwise bound (2). It also shows that g is an ordinary core
minorant of the separable reconstruction of d: every source coefficient
of g is bounded by the product of its pure factors, and (PM) bounds
that product by the prescribed reconstruction. Such a minorant may be
strictly smaller than the reconstruction.

## Every full-support minorant has a one-variable realization

Conversely suppose (2) holds. Choose a P_I,0 word F for f_d. It uses
all of B; one can ensure that the zero symbol occurs by replacing F
with F+0. Introduce a fresh variable A and replace every zero constant
of F by A, obtaining a constant-free word T_0. Add an observing owner
rho and form

    T=T_0 choice_rho g.                               (3)

Every foreign choice and union acts as join at the rho coordinate.
Thus T_0 has rho-trace SUM_(j in B) j + A, while the full-support g
has rho-trace SUM_(j in B) j. The rho-trace of (3) is

    (SUM_B j + A) * SUM_B j.

Its interior on C subseteq B union {A} is C when C meets B and empty
otherwise. Therefore

    c_rho(E)=E union {A} if B subseteq E, and E otherwise. (4)

In particular B is rho-independent and c_rho(B)\B={A}.

At an old coordinate s the root in (3) is join. Setting A to trace zero
gives f_d,s+g_s=f_d,s by (2). Hence its conditional closures are exactly
(1). Interpreting the named unions by derived core union makes (3) an
ordinary constant-free core word. Their rho trace is still join, including
when a union implementation uses the added owner internally.

## An actual operation with a nonrealizable conditional tuple

Use foreign owners 0,1,2 and variables B={x,y,z,w}. Take

    d_0: {x,z,w}=>y;
    d_1: {y,z}=>x;
    d_2: {x,y}=>z.                                  (5)

These closures are loopless but have no common core realizer, by the
[three-owner feedback law](three-owner-exchange.md). Their trace function
has coordinate formulas

    f_0=m+y*m,   m=x+z+w;
    f_1=w+n+x*n, n=y+z;
    f_2=w+p+z*p, p=x+y.                             (6)

Define

    H=y union (x choice_1 (y choice_2 z))
        union (z choice_2 (y choice_1 x));
    g=w union (w choice_0 H).                       (7)

This is a full-support constant-free word. At coordinates 1,2 it agrees
identically with f. At coordinate 0 it is zero when w_0=0, and the
full input join otherwise. Formula (6) is zero only when
x_0=z_0=w_0=0, and the full join otherwise. Thus g<=f pointwise.

For an explicit choice of F in the construction, lift each formula in
(6) to a word F_s using choice_s for multiplication and union for +.
Let kappa_s(U) attach trace zero at each other foreign owner once.
Then

    F=kappa_0(F_0) union kappa_1(F_1) union kappa_2(F_2)

realizes f in P_I,0. Replace all its zero constants by the new variable
A and apply (3) with (7). This gives an actual four-owner core word
on five variables. Its base B is rho-independent, D={A}, and its
conditional foreign tuple is exactly the nonrealizable tuple (5).

Thus conditional joint realizability is not a necessary test for core
operations and cannot be imposed iteratively on their independent bases.
The necessary conditional profile and no-feedback laws remain valid;
they assert less than common realization of the whole conditional tuple.

## Raw feedback is necessary but not sufficient

For a loopless closure tuple d, a necessary condition for (2) is absence
of raw rainbow feedback: there must be no finite family

    X_i subseteq d_(s_i)(Q_i), X_i intersect Q_i=empty,

with nonempty head union, where every Q_i is covered by head blocks
of pairwise distinct owners different from s_i. Necessity now follows
from the reverse construction: such a tuple would occur at a genuine
rho-independent base, where core feedback elimination forbids it.
Equivalently this is the feedback test at a newly added identity observing
coordinate; it does not impose (FE) at the old owners.

The converse fails already for two foreign colors on three variables.
Let B={a,b,c} and define the loopless closures

    d_0: a=>b, b=>a;
    d_1: a=>c, c=>a.                                (8)

Thus d_0 has parallel pair {a,b} and free variable c; d_1 has parallel
pair {a,c} and free variable b.

**Theorem.** The tuple (8) has no raw rainbow feedback, but f_d has no
full-support constant-free foreign-choice/union minorant.

Its hereditary common-source profiles are immediate. On all of B the
minimal spanning coalitions are {a,c},{b,c} for d_0 and {a,b},{b,c}
for d_1; every pair intersects. On retained {a,b}, d_1 is identity;
on {a,c}, d_0 is identity; on {b,c}, both are identity. Singleton
retained sets also have identity closures. Looplessness makes every
spanning coalition of a nonempty retained set nonempty. Therefore all
the hereditary profile tests pass, and the two-color compression theorem
excludes raw feedback of every finite size.

Suppose a full-support minorant g existed, with pure closures c_0,c_1.
The bound (PM) gives b=>_0 a and a=>_1 c. Elementary cross-value
composition then puts c in c_0({b}), so c_0({b})=B. Similarly c=>_1 a
and a=>_0 b force c_1({c})=B. The singleton profiles of g would thus
have disjoint positive coalitions {b} at owner 0 and {c} at owner 1,
contrary to common-source admissibility. Equivalently, the same input
with b={0} and c={1} would have to yield both distinct singletons.

Named union causes no exception: introduce a third owner and implement
union by the derived core term. This preserves both old trace coordinates,
and the core cross-value composition and profile laws apply. The new
coordinate has the full-support union trace, so its positive unanimity
coalition does not repair the empty intersection.

Thus raw feedback cannot alone characterize minorant feasibility. The
capture budgets must also admit the extra old-owner captures forced by
cross-value composition; here those forced captures already contradict
profile admissibility. No sufficiency assertion follows for feedback
augmented by a fresh identity observer or by further closure laws.
