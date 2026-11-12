# Cofactor dependence and the canonical owner closures

Mathematical research, without Lean claims. The canonical owner closures
of every core operation have an intrinsic definition using ordinary
restrictions of the full winner-valued function. Source separation is
not needed. This identifies a general closure construction and explains
exactly what fixing a monochromatic coalition makes irrelevant; it does
not supply a criterion for joint guard realizability or prove maximal
free-extension attainment.

## A closure associated with any distinguished input value

Let V be finite, let X be a nonempty input set with a distinguished
element a, and let F:X^V->Y be any function. A variable is essential if
changing only that variable can change the output. For E subseteq V,
write F_(E,a) for the cofactor obtained by fixing every input in E to a,
and define

    dep_a(E)=E union {j outside E:j is inessential in F_(E,a)}. (1)

**Proposition.** The map dep_a is a closure operator. It is loopless,
meaning dep_a(empty)=empty, exactly when every input of F is essential.

Extensivity is immediate. If E subseteq E', an input already made
inessential by fixing E remains inessential after the further
restrictions, unless it belongs to E', when it is included by definition.
This proves monotonicity.

For idempotence put C=dep_a(E). The cofactor F_(E,a) is independent of
each coordinate in C\E. Since V is finite, changing these coordinates
one at a time shows joint independence of all of them. Fixing them to a
therefore leaves exactly the same function of the remaining coordinates.
In particular it creates no new inessential coordinate outside C. Thus
dep_a(C)=C. Finally dep_a(empty) is precisely the set of inessential
inputs of the original function, proving the last assertion.

The construction concerns functional dependence, rather than the value
of a particular cofactor evaluation. In particular, declaring j
inessential in (1) quantifies over every assignment of all the other
unfixed inputs.

There is also a cross-value composition law. If a,b are distinguished
input values and i belongs to dep_a(E)\E, then

    dep_b({i}) subseteq dep_a(E).                        (C)

The E=a cofactor is independent of i, so fixing i=b does not change
that function. Every variable made inessential by fixing i=b remains
inessential after also fixing E=a, and hence in the unchanged E-cofactor.
Variables in E or equal to i are already included on the right. This
proves (C) for arbitrary F, without game operations or source separation.

## Equality with the core's canonical owner closure

Fix finite owners I with K>=3 and the carrier A=P_+(I). The primitive
operation owned by r is

    U star_r W = {r} if U={r} or W={r},
                 U union W otherwise.

Let F:A^V->A be any core operation on a finite nonempty variable set V;
unused inputs are permitted here. Fix r in I. For j outside E and
k!=r, its pure-owner source probe assigns

    x_j={k},  x_i={r} for i in E,
    x_i=N_k=I\{k} at all other inputs.

Write D_(j,r)(E) for membership of k in the resulting output. For core
operations this is independent of the chosen k!=r. The canonical owner
closure is

    c_r(E)=E union {j outside E:D_(j,r)(E)=false}.          (2)

**Theorem.** For every core operation, whether source-separable or not,

    c_r(E)=dep_{ {r} }(E).                                (3)

Here is a direct proof of the nontrivial implication. Choose any core
word for F. The singleton-r profile of a subword is a monotone Boolean
function of its r-atomic input positions: its gate is OR at an r-owned
node and AND at every other-owned node.

On the pure-owner probe, an occurrence of j can lose its observed k
only at an r-owned ancestor whose sibling has value {r}. No other
foreign-owner singleton is available: the remaining inputs are the
ambiguous menu N_k, and an owner-k absorption retains k. Consequently
D_(j,r)(E)=false means that every occurrence of j has such an r-owned
blocking ancestor, with the sibling's r-profile already true when
exactly E are r atoms and j is not an r atom.

Keep E fixed to {r}, and now allow every other input, including j, to
take an arbitrary menu. The identified sibling profiles stay true:
the r-atomic set can only grow from E, and these profiles are monotone.
Each identified ancestor therefore has the fixed value {r} on the
entire cofactor. Choose the maximal identified subtrees under inclusion.
They are disjoint and cover every occurrence of j. Replacing them by
their fixed values removes all occurrences of j without changing the
cofactor's function. Thus j is inessential in F_(E,{r}). An unused j
is covered by the same conclusion without any subtree replacements.

Conversely, if D_(j,r)(E) is true, the probe above has k in its output.
Replace just x_j by N_k. All inputs now omit k, so conservativity makes
the output omit k. Both evaluations fix E to {r}, and differ only at
j. Therefore j is essential in that cofactor. This proves (3).

In particular the owner closures can be defined directly from the full
operation, without occurrence graphs or prime guards. Their closure
laws then follow from the general proposition. The owner-shadow law
is another presentation of this same closure property, as established
in [separable-closures.md](separable-closures.md); no new independent
compatibility assumption is being added here.

## Exact consequences for monochromatic restrictions

Put C=c_r(E). If two valuations x,y fix E to {r} and agree outside C,
then

    F(x)=F(y).                                            (4)

Indeed every coordinate in C\E is inessential in the cofactor, and
finite coordinate-by-coordinate replacement proves simultaneous
independence. The coordinates in E remain fixed in (4); their inclusion
in C does not authorize changing those prescribed values.

Thus if an actual valuation has r-atomic set E, every coordinate in
c_r(E)\E may be replaced by an arbitrary menu, simultaneously, without
changing its output. In particular replacing all of them by {r}
preserves the value and changes the r-atomic set exactly from E to
c_r(E). This is a statement about the complete old winner set, including
its constant atomic part, rather than just the presence of a fresh
observer.

The spanning-profile identity also has a direct semantic proof:

    c_r(E)=V iff fixing E to {r} forces output {r}.         (5)

The left side says that the cofactor is constant. Evaluating its
remaining coordinates at {r} identifies that constant as {r} by
idempotence. Conversely a constant cofactor has no essential variables.
Since a core's singleton profile depends only on its atomic-r positions,
this is the familiar profile Phi_r(E)=[c_r(E)=V].

## Source separation and dependence imply hereditary omission

There is a useful consequence even for synthetic candidates. Suppose F
has the loopless source-separable reconstruction

    k in F(w) iff some j with k in w_j lies outside
                           UNION_(r!=k) c_r(E_r(w)),

and c_r agrees with its monochromatic dependence closure. Outputs may
initially be allowed to be empty in this paragraph.

**Proposition.** F satisfies omission independence: if its output omits
k, every input originally containing k may be changed arbitrarily,
simultaneously, without changing the full output.

Every such original source j is captured by some foreign owner r!=k,
by the displayed product formula. Its capturing r-atomic inputs omit k
and are therefore kept fixed. Dependence makes j inessential uniformly
while those fixed inputs retain their values. Apply this to the changed
coordinates one at a time; all the original capturing atomic inputs
remain fixed throughout. The whole output is preserved.

The property is hereditary under winnerwise neutral restrictions. For
nonempty U subseteq V, the restricted formula has closures
c_r^U(E)=c_r(E) intersect U. If j belongs to this closure, the original
function is independent of j while E is fixed to {r}. Evaluate that
identity with each outside-U input at I\{k}, separately for each queried
winner k. It shows that the entire neutral residual F_U is independent
of j in the same cofactor. The reverse implication again follows from
its conservative pure-source probe. Thus the restricted closures are
its dependence closures, and the proposition applies on every U.

These formulas are also nonempty. They are idempotent on diagonal
inputs. If one output were empty, every winner would be omitted. Change
each input in turn to a fixed atom {r}, using any winner in its current
nonempty menu to apply omission independence. The output would stay
empty, contradicting idempotence at the final diagonal. This argument
applies also to every nonempty neutral restriction.

This implication uses the source-separable product formula. For a
nonseparable operation a source can lose k through different mixed
filters even when every individual pure-owner port is true; the above
choice of a capturing owner is then unavailable.

## The maximal semantic forcing predicate is closure-invariant

Define

    Force_r(E) iff r belongs to F(x) for every x whose
                              r-atomic set is exactly E.  (6)

**Corollary.** Force_r(E)=Force_r(c_r(E)). In fact the sets of attainable
output values on these two exact-atomic-set fibers are identical.

For the forward comparison of their output ranges, take x with exact
r-atomic set E and replace c_r(E)\E by {r}. Equation (4) preserves
the output, and the new exact set is c_r(E). Conversely take a valuation
with exact set c_r(E), and replace those same coordinates by any fixed
non-r-atomic menu, for example I\{r}. Equation (4) again preserves the
output, and the new exact set is E. These give both inclusions of the
output ranges and hence the corollary.

An arbitrary monotone sufficient predicate g(E) implying Force_r(E)
need not itself be c_r-invariant. For F(Y,Z)=Y star_r Z, the predicate
g(E)=[Y in E] is sufficient, but c_r({Z})={Y,Z}; hence
g({Z}) is false and g(c_r({Z})) is true. The corollary concerns the
maximal semantic predicate (6), not every selected sufficient condition.
No profile-interval or minorant-realization assertion follows from it.

## Mixed source guards are cofactor-support data

The cut proof extends to every partial atomic coloring p whose colors
omit at least one owner k. Let dom(p) be its fixed inputs, and j an
unfixed source. Probe with j={k}, the prescribed atoms at dom(p),
and N_k elsewhere. Then, for every core operation F,

    C_(j,k)(p)=false iff j is inessential in F restricted by p. (7)

For the forward implication every occurrence of j is blocked by an
ancestor of some owner r!=k whose sibling has an r-singleton profile
already true on p's r-atomic positions. That profile stays true under
arbitrary menus at all unfixed positions. Maximal such absorbing
subtrees cover all j occurrences, so replacing them by their fixed
atoms removes j from the cofactor. For the reverse implication,
C_(j,k)(p)=true distinguishes j={k} from j=N_k: in the latter probe
all inputs omit k, and conservativity makes the output omit k too.

Consequently the bit is independent of which missing owner k is used.
The entire dependence set of the cofactor is

    dep(p)=dom(p) union {j:C_(j,k)(p)=false}.             (8)

It grows under extension of p. Further assignments to any finite set
of its unfixed inessential positions, with arbitrary menus, leave
the same cofactor function and the same dependence set on its
remaining inputs. These are statements about the full winner-valued
function, not merely its observed bit.

The whole operation can be recovered from this signature. At w, fix
every rival atomic position E_r(w), r!=k, and call the resulting
proper-color context p_k(w). Source reconstruction and (7) give

    k in F(w) iff some j with k in w_j is essential
                         in F restricted by p_k(w).    (9)

Thus general canonical guards have an intrinsic semantic meaning:
they are precisely the essential-variable data of proper-color
atomic cofactors. Source separation means, equivalently,

    dep(p)=UNION_r c_r(E_r(p))                         (10)

for every proper-color atomic context. Differently colored
restrictions then create no additional inessential variables beyond
those created by their individual monochromatic restrictions.

These descriptions apply to an already given core operation; they
are not a criterion for which arbitrary cofactor-support signatures
come from core syntax. The separable counterexamples below pass
the same proper-color dependence test: a zero mixed bit has a
zero monochromatic factor, whose functional independence persists
under the other fixed colors. A true bit still supplies its probe
witness of essentiality.

## Full-color cofactors can have additional inessential inputs

For a partial atomic coloring with disjoint sets E_r, let dep(E_*) be
the fixed coordinates together with the inessential variables of the
mixed cofactor x_i={r} for i in E_r. Further restriction preserves
inessentiality, so

    UNION_r c_r(E_r) subseteq dep(E_*).                    (11)

The inclusion can be strict even for input union. Take the union on
variables j and z_r for all r in I, and fix each z_r to
{r}. The resulting old winner set is I for every value of j, so the
mixed cofactor makes j inessential. On the other hand a one-color
restriction of input union leaves each unfixed input essential. Thus
c_r({z_r})={z_r}, and their union does not contain j.

This extra mixed dependence is ordinary saturation of the old output:
the fixed atomic inputs already supply every old winner. It must not be
identified with loss of the fresh observer in the common-carrier
extension. For the same union word on B_I, those old atoms together
with a fresh P at j give output P. The canonical set Q={j} correctly
retains that potential fresh source even though the old mixed cofactor
is constant. The distinction is also relevant to
[canonical-separable-extension.md](canonical-separable-extension.md).

## Functional dependence does not settle realizability

The [two-owner prime obstruction](separable-closure-counterexample.md)
has exactly these monochromatic dependence closures for every K>=3.
It also has admissible profiles and omission independence on every
neutral restriction, and core proper neutral faces and identification
minors. Its three canonical source rows still violate a law of every
core term. Thus the semantic definition above improves the closure
theory and its proofs; it does not turn that necessary theory into a
sufficient criterion for joint guard realizability.
The [three-owner obstruction](three-owner-exchange.md) also has exact
functional-dependence closures and passes the reciprocal shared-witness
law, but its closures violate the stronger feedback elimination law
obeyed by all genuine cores.
