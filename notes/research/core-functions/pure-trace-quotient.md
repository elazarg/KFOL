# The joint pure-trace quotient and a ternary basis for one coordinate

Mathematical research, without Lean claims. Joint
pure-owner data form a proper equational quotient of the core. One trace
coordinate has a finite relational basis of arity at most three. Neither
finite basability nor finite relatedness of the constant-free colored
product P is proved.

## Canonical traces and their three-state encoding

Fix finite owners I, |I|=K>=3, and a finite nonempty variable set V.
For a core term T and owner r, replace every foreign-owned gate by union.
Distribution gives a nonempty union of nonempty r-folds. Let H_r(T)
be their supports, and define the canonical interior

    I_r^T(C)=UNION {S in H_r(T): S subseteq C}, C subseteq V.

The support presentation need not be unique; this interior is unique.
At a leaf j its value is {j} if j belongs to C, and empty otherwise.
For T=L choice_q R the exact recursion is

    I_r^T(C)=I_r^L(C) union I_r^R(C),             if q!=r;
             that same union if both are nonempty,
             and empty otherwise,              if q=r.       (1)

At an r-root, contained monomials are unions of one contained monomial
from each child; at a foreign root they are simply merged. In particular
I_r^T(V) is the variable support of T, independently of r. Unused variables
are allowed. Pure ports and singleton profiles are recovered by

    D^T_(j,r)(E) iff j belongs to I_r^T(V\E), j notin E;
    Phi_r^T(E) iff I_r^T(V\E) is empty.                    (2)

Let Q={0,a,b}, ordered 0<a<b. Write + for maximum and define

    x*y=0 if x=0 or y=0; otherwise x*y=max(x,y).

This is the existing `Dissemilattice.Three`, with states b,n,p renamed
0,a,b. Its exact seven-equation basis is proved in
`KFOL/Core/ChoiceUnion/ThreeCompleteness.lean`.
Let Q_r interpret choice_r as * and every foreign choice as +, and put

    P=PRODUCT_(r in I) Q_r.

The usual derived union is + in every coordinate. At coordinate r,
assign 0 outside C, b on B subseteq C, and a on C\B. Recursion (1) gives

    T=0 iff I_r^T(C) is empty;
    T=b iff I_r^T(C) intersects B;
    T=a otherwise.                                      (3)

Taking B={j} detects every interior member; arbitrary B is then determined.
Consequently two core terms have identical joint pure ports if and only
if they have the same term function on P. This concerns all sources,
including unused ones; singleton profiles are already determined by (2).

## A pure source can require repetition

There is no general normal form as a union of words linear in a chosen
source, even for the pure-trace quotient. Here linear means at most one
occurrence in a constant-free choice/union word; naming union does not
help. This is a written mathematical proof, not a new Lean claim.

Choose distinct owners A,B,C and four variables a,x,p,e. Put

    T=(e choice_C x) choice_B ((x choice_C a) choice_A p).

**Proposition.** If S<=T pointwise on P and S is x-linear, then its
B-coordinate is zero at x=b,a=p=e=0. T's B-coordinate there is b.
Thus every word with T's pure tuple repeats x. Even a finite union
of x-linear words cannot have T's pure tuple.

Use the four scalar coordinate probes below. In this table alpha=a and
beta=b denote the chain values, while the column a is a variable.

| Coordinate | variable a | x | p | e | T |
|---|---|---|---|---|---|
| A | beta | 0 | 0 | alpha | alpha |
| B0 | 0 | 0 | beta | 0 | 0 |
| B1 | 0 | 0 | 0 | beta | 0 |
| C | 0 | beta | alpha | 0 | alpha |

For every x-free word G satisfying G_B0=G_B1=0:

1. G_A is nonzero. Otherwise G has positive A-profile at {p} and
   positive B-profile at {a,e}, contrary to common-source intersection.
2. If G_C=0, then G_A=beta. Indeed G_A<=alpha implies a positive
   A-profile at {p,e}: lower e to zero in its A-row; the output is then
   0 or beta and cannot be beta. Its B1 and C zero evaluations give
   positive B-profile at {a,p} and C-profile at {a,e}. These three
   coalitions have empty common intersection. All other owners use
   the full coalition {a,p,e}.

Suppose an x-linear S has positive B-coordinate at the query. Every
x-free sibling has value zero there, so the x-path contains no B-owned
gate: such a gate would erase the positive value permanently. Along
the two B-budget rows all path gates are maxima. Since S<=T, every
sibling has B0=B1=0 and satisfies the two facts above.

The invariant along the x-path is G_A=beta or G_C=beta. Initially the
C-row is beta. An A-gate cannot erase an A beta, since its sibling's
A value is nonzero. A C-gate can erase a C beta only with a sibling
whose C value is zero, which introduces an A beta. Every other gate
and union is maximum in both coordinates. The final invariant
contradicts S_A,S_C<=alpha.

In a finite union equal to T on P each summand is <=T, and some
summand must have positive query value. This proves the union claim.
The proof works for every ambient K>=3, including extra-owner gates.

Equivalently, no x-linear core minorant of the separable pure-port
upper hull of T retains this positive pure port. This refutes extraction
under an arbitrary separable upper bound. T itself is not separable,
so the statement does not refute a theorem restricted to genuinely
separable core targets. The report statement is
`core:prop:pure-source-repetition`.

## The conservative equational hull is strictly smaller

The variety V(P) is exactly the variety generated by all conservative
algebras belonging to the core variety. Indeed the report's conservative
presentation (`core:thm:conservative-basis`) makes every such algebra have
all but at most one choice equal to derived union. Its remaining two
operations satisfy the seven laws, so the existing Three-completeness
theorem places it in V(Q_r). Conversely every Q_r is conservative and
belongs to the core variety by `core:prop:dissemilattice-lift`. Hence

    V(P)=JOIN_(r in I) V(Q_r).                            (4)

The relative conservative basis does not axiomatize V(P) over arbitrary
algebras: its equations hold in the whole core variety as well.

For distinct owners alpha,beta,gamma, P satisfies the five-leaf identity

    x choice_gamma (y choice_beta (z choice_gamma (x choice_alpha y)))
      =x choice_gamma ((x choice_alpha y) choice_gamma (y choice_beta z)).
                                                               (5)

At the alpha coordinate both sides reduce to x+y+z; at beta they reduce
to x+y+yz; at gamma they reduce to xy+xz+xyz; all other coordinates give
x+y+z. Here juxtaposition is that coordinate's multiplication. These
reductions use distribution, idempotence, and xy<=x+y in the join order,
all consequences of the seven laws. In the core itself, take
x={alpha}, y={gamma}, z={beta}. The left side is {alpha,beta,gamma}
and the right side {alpha,beta}. Thus this equational quotient is proper;
it is not an equivalent encoding of the full source guards.
The identity even fails in the scalar observer-gamma bichain with union:
take x=atom alpha, y=P, z=atom beta. The two sides are P and N.
Thus ordinary same-signature subalgebra, product and quotient constructions
cannot recover that scalar algebra from P; its existing obstruction
families do not transfer through such a recovery.

## A finite relational basis for the single Q clone

Let sigma identify a,b and distinguish 0. The following five relations
on Q form a relational basis for its constant-free term clone:

* the chain order <= and the singleton relations {0},{a};
* S={(x,y,z): sigma(x)=sigma(y)=sigma(z), z=max(x,y)};
* R={(x,y,z): sigma(x)=sigma(y), x!=b implies z=y}.

Thus every relation in the basis has arity at most three.

**Invariance.** Both operations are monotone, preserve {0,a}, are idempotent,
and induce respectively OR and AND on the nonzero indicator sigma.
For S, the zero/nonzero pattern is identical in its three rows. A zero
multiplication output is zero in all three rows; otherwise the relevant
nonzero inputs combine by maximum, which commutes with maximum.
For R, a non-b first output under + means neither first input is b, so
both third inputs equal their second inputs. Under *, a zero first output
has a zero input, whose second and third inputs are also zero. A first
output a requires both first inputs a, again fixing both third inputs.
These are all cases where R imposes its last-coordinate equality.

**Completeness.** Let f:Q^V->Q preserve these relations, with |V|>=1.
The three omitted preservation properties follow from the five relations.
Columns (b,a,0) lie in R, so its output (f(b^V),a,0) forces f(b^V)=b.
Columns (x,y,y) lie in R whenever sigma(x)=sigma(y), so f preserves
ker(sigma). Finally inputs from {0,a} are at most a^V; order and
f(a^V)=a make their outputs at most a, giving preservation of {0,a}.

For B subseteq C subseteq V write v(C,B) for 0 outside C, b on B,
and a on C\B. Preservation of ker(sigma) makes the zero/nonzero status
of f(v(C,B)) depend only on C. Preservation of S gives

    f(v(C,B union D))=max(f(v(C,B)),f(v(C,D))).          (6)

Since {0,a} is preserved, f(v(C,empty)) is not b. Therefore the set

    I(C)={j in C: f(v(C,{j}))=b}

satisfies f(v(C,B))=b iff B intersects I(C). It is contractive by
definition and monotone in C by preservation of <=.

If I(C) is empty, use the three valuation rows v(C,C), v(C,empty),
v(empty,empty). Every column lies in R, and the first output is not b.
The last two outputs must agree; the singleton relation {0} makes the
last one 0. Thus the whole C-fiber has output 0. Conversely a nonempty
I(C) makes the fiber nonzero, and its unmarked output is a. We obtain
exactly formula (3) with I in place of I_r^T.

For I(C) subseteq C' subseteq C and any B subseteq C, use rows

    u=v(C,C\C'), v=v(C,B), w=v(C',B intersect C').

Every column lies in R. The first output is not b because its marked
set misses I(C), so f(v)=f(w). Taking C'=I(C) and B={j} for each
j in I(C) gives I(C) subseteq I(I(C)); contraction gives equality.
Thus I is an interior, including at sets with empty image.

The already derived f(b^V)=b gives I(V) nonempty;
it need not equal V because variables may be unused. Let F be the
nonempty family of nonempty fixed sets of I. Every interior satisfies

    I(C)=UNION {S in F: S subseteq C}.

The + of the *-monomials with supports S in F consequently agrees with f
on every v(C,B), by (3), and these exhaust Q^V. Hence f is a Q term.
This proves finite relatedness for the single coordinate, independently
of the existing finite equational basis.

## Adjoining zero makes the colored product ternary-related

Write Q_0 and P_0 for the expansions by the constant 0, respectively
the all-zero vector.
All clone statements concern positive-arity operations, including induced
constant operations. A Q_0 term reduces to 0 or a constant-free Q term,
using x+0=x and x*0=0. Conversely both alternatives are available.

**Theorem.** The five relations <=,S,R,{0},{0,a} form a relational basis
for Q_0. Hence P_0 has a relational basis of arity at most three.

For the first claim, let f preserve those five relations. The argument
using (x,y,y) in R still gives preservation of ker(sigma). The relation
{0,a} makes f(a^V) either 0 or a. If it is 0, sigma-preservation makes
f(b^V)=0; monotonicity then forces f identically 0. Otherwise f fixes a
and 0, so it preserves the previous constant-free five-relation basis
and is a Q term. Every Q_0 term preserves the displayed relations,
since they are Q-invariant and each contains its all-zero tuple.

For the product, include the binary factor congruences

    theta_r={(u,v) in P^2: u_r=v_r},

and, for each r and each of the five Q_0 basis relations rho of arity d,
include its coordinate pullback

    rho^r={(u_1,...,u_d): (u_(1,r),...,u_(d,r)) in rho}.

Preservation of every theta_r makes f:P^V->P coordinatewise:
f(u)_r=g_r((u_(v,r))_v). The pullbacks put each g_r in Clo(Q_0).
Conversely these independent coordinate functions are all term-induced
in P_0. Starting at x, attach 0 once at every owner s!=r:

    kappa_r(x)=FOLD_(s!=r) (current choice_s 0).

At coordinate r each attachment is join with 0 and leaves x_r unchanged.
At coordinate s its own attachment kills that coordinate, and later joins
with 0 preserve the zero. Thus kappa_r isolates coordinate r. Lift a
Q_0 realizer of g_r using choice_r and derived union, apply kappa_r,
and take the derived union over r. The result realizes the entire tuple.
This proves the asserted ternary relational basis, uniformly in K.

Naming this existing all-zero P element is not adjoining an empty winner
menu to the original core. An empty menu is neutral for every owned
choice. The zero of P instead annihilates the owner's trace coordinate;
it represents simultaneous positive singleton-profile signals for all
owners, which no genuine winner menu can have.

## Maximal zero-avoiding subalgebras

In this section P^m denotes an ordinary power, m>=1, without a named zero
constant. Index its coordinates by (r,l), r in I and 1<=l<=m.
For a selection l_r of one coordinate per owner define the rainbow clause

    C_l={u in P^m: u_(r,l_r)!=0 for some r}.             (7)

**Theorem.** The maximal invariant relations avoiding the all-zero tuple
are exactly the clauses C_l. Every zero-avoiding invariant relation,
including the empty relation, is contained in one of them.

Each clause is nonempty and proper. It is invariant: if a choice_q output
were zero in all selected coordinates, both inputs would be zero at every
selected foreign coordinate, and one input would also be zero at q.
That input would violate the clause.

For containment let R be a nonempty zero-avoiding invariant relation.
It is finite. Regard its members as variable columns and put

    E_(r,l)={u in R: u_(r,l)=0}.

A term generates the zero tuple exactly when its singleton profiles have
all the positive demands Phi_r(E_(r,l)). Indeed its r-coordinate trace
is zero exactly at a positive owner-r singleton-profile probe, independent
of the positive a/b values at the other positions. The existing
[profile theorem](../../../sections/appendix-core-basis.tex)
(`core:thm:profiles`) applies also to these multiple demands per owner:
the least monotone profiles containing them are admissible exactly when
every selection of one demanded coalition per owner has nonempty
intersection. If a demanded coalition is empty, this condition fails
immediately. Otherwise the least profiles are normalized and unanimous,
so the theorem constructs a word meeting all demands.

No such word generates zero from R. Therefore some selection has
intersection_r E_(r,l_r)=empty, which is precisely R subseteq C_l.
For empty R containment is immediate.

To prove maximality, adjoin any y outside C_l. For its own selection l,
y is zero at every selected coordinate. For any different selection l',
choose r with l'_r!=l_r; the vector having a only at (r,l_r) lies in C_l
and is zero at every l'-selected coordinate. Consequently every rainbow
selection of the zero coalitions of C_l union {y} has a common variable
column. Profile feasibility generates zero, so no larger zero-avoiding
invariant relation contains C_l.

## All maximal proper subalgebras

**Corollary.** For K>=3 and m>=1, the maximal proper subalgebras of P^m
are exactly the following:

* a coordinate pullback pi_r^(-1)(S), where S is a maximal proper
  Q_0-subalgebra of Q^m;
* a rainbow nonzero clause C_l from (7).

If a subalgebra R contains the zero tuple, the isolators kappa_r can use
that tuple as a parameter. They show

    R=PRODUCT_r pi_r(R).

Each projection is a Q_0-subalgebra: it contains zero and is closed under
both multiplication and join. Maximal properness therefore forces exactly
one projection to be proper, and that projection must be maximal proper.
Conversely every stated pullback is maximal: any larger subalgebra still
contains zero and has this product form, so enlarging its sole proper
factor generates the whole power.

If R avoids zero, it lies in a proper clause C_l, so maximal properness
forces equality. To verify that every clause really is maximal proper,
adjoin y outside it. The preceding proof generates zero. Moreover
pi_r(C_l)=Q^m for every r: any chosen r-coordinate vector can be supplemented
by a at the selected coordinate of another owner. Once zero is generated,
the isolators and derived union therefore generate all of P^m.

## Maximal proper invariants do not recover the constant-free clone

Even adding all clauses (7) to the basis of P_0 is insufficient. For
explicit evidence use the loopless closures on {x,y,z,W}

    c_0: {x,z,W}=>y; c_1: {y,z}=>x; c_2: {x,y}=>z,
    all other c_r identity.

At each coordinate take the Q term with interior
I_r(C)=V\c_r(V\C). These give an operation f in Clo(P_0), by coordinate
isolation. Each coordinate term is idempotent, so f is idempotent too.
Their singleton profiles are admissible: every spanning coalition
contains W, which no closure captures. Hence f preserves every clause
(7). More generally, for selected coordinate r let C_r be its nonzero
input positions. Column membership in the clause says UNION_r C_r=V.
If all selected outputs were zero, Phi_r(V\C_r) would hold for every r,
contradicting the common-source condition. This also covers all powers m.

Nevertheless f is not a constant-free P term. Such a term would give a
core word with exactly these pure closures, contradicting the proved
[three-owner feedback law](three-owner-exchange.md):
the displayed three captures force {x,y,z} subseteq c_0({W}), which is
false. Thus f preserves the product's ternary zero-expansion basis and
every maximal zero-avoider, yet has no common constant-free realizer.
By the corollary this f preserves every maximal proper invariant relation
in every finite power: those containing zero are preserved because f is
a P_0 term, and the remaining ones are the clauses already checked.
Thus even all maximal proper invariants together do not determine Clo(P).
In particular Clo(P) is not the idempotent fragment of Clo(P_0).

## Every unary subalgebra still does not suffice

The same four-variable operation f preserves **every** unary subalgebra
of P, as well as all the individual-coordinate basis relations. It is
exactly one-point term-interpolable but is not two-point
term-interpolable. This gives an analytic counterexample to replacing
colored compatibility by the individual Q conditions and all unary
subalgebras.

For clarity its coordinate formulas are

    f_0=(x_0+z_0+w_0) + y_0*(x_0+z_0+w_0);
    f_1=w_1+y_1+z_1 + x_1*(y_1+z_1);
    f_2=w_2+x_2+y_2 + z_2*(x_2+y_2);
    f_r=x_r+y_r+z_r+w_r for every other r.          (8)

Each is a constant-free Q term. Define the core words

    H=Y union (X choice_1 (Y choice_2 Z))
        union (Z choice_2 (Y choice_1 X));
    T_upper=W union H;
    T_lower=W union (W choice_0 H).                 (9)

At every coordinate other than 0, both T_upper and T_lower agree
identically with f. At coordinate 0, H is x_0+y_0+z_0, so T_upper
is the full join J=x_0+y_0+z_0+w_0. The lower word is

    w_0 + w_0*(x_0+y_0+z_0),

which is 0 when w_0=0 and J otherwise. Formula (8) is 0 when
x_0=z_0=w_0=0 and J otherwise. Consequently, at each single input
tuple u in P^4,

    f(u)=T_lower(u) if x_0=z_0=w_0=0;
    f(u)=T_upper(u) otherwise.                      (10)

The choice in (10) proves local interpolation; it is not claimed to
be a term-defined conditional. If all four inputs lie in a unary
subalgebra, both words in (9) take their values in that subalgebra.
Thus f preserves every unary subalgebra of P.

Here are two inputs that cannot share an interpolant. Display only
coordinates 0,1,2; every omitted coordinate is 0.

| variable | input u | input v |
|---|---|---|
| X | (0,b,0) | (a,0,0) |
| Y | (a,0,0) | (a,0,0) |
| Z | (0,0,b) | (a,0,0) |
| W | (0,a,a) | (0,0,0) |

The prescribed values are

    f(u)=(0,a,a),    f(v)=(a,0,0).                  (11)

Suppose a constant-free word T matched both. Its coordinate-0 value
at u forces Phi_0^T({X,Z,W})=true. Its coordinate-1 and coordinate-2
values at u are not b, so they give the two omission budgets in the
word-level [feedback profile passage](three-owner-exchange.md), with

    A={X,Z,W};
    X_1={X}, P_1={Y,Z};
    X_2={Z}, P_2={X,Y}.

The two colored covers hold. That passage forces Phi_0^T({W})=true;
it needs no closure-spanning hypothesis once the initial profile and
budgets are given. At v the coordinate-0 inputs are a on X,Y,Z and
0 on W. This positive profile forces T(v)_0=0, contradicting (11).

Equivalently, the binary subalgebra of P^2 generated by the four
column pairs (u_X,v_X),...,(u_W,v_W) does not contain (f(u),f(v)).
Thus f preserves all unary invariant relations but fails a binary one.
All coordinates of f remain genuine Q terms and f is idempotent;
the failure is solely their realization by one common constant-free
word.

## What the reduction leaves

Pulling these relations back along each projection P->Q_r enforces the
correct individual coordinate interiors. It does not enforce their
realization by one common colored term. A join of finitely based
varieties is not automatically given a finite basis by their separate
bases. The finite relational basis after adjoining zero does not supply
a finite relational basis for constant-free P.
Those colored compatibility questions, and the stronger intrinsic
criterion for arbitrary joint source guards, remain separate.
