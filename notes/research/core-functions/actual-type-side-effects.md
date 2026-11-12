# Actual source types have an all-owner side-effect law

Mathematical research, without new Lean claims. This strengthens the necessary
tests in [source-type-pruning.md](source-type-pruning.md) and gives an analytic
counterexample to their sufficiency even when the target operation is known
to be core. No term enumeration is used.

Fix a finite owner set I with K>=3. All terms are constant-free primitive
core terms, with owned choices from I. Derived union is available because
there are three distinct owners. A full occurrence type at source j is the
vector B=(B_r)_(r in I) of its antitone owner factors, each satisfying
B_r(empty)=true.

## A closed all-owner side-effect condition

At a valuation w whose source menu w_j is ambiguous, put

    E_r(w)={i!=j:w_i={r}},
    D_B(w)={r in I:B_r(E_r(w))=false}.

**Theorem.** If B occurs at a marked j-leaf in a term realizing F, then

    D_B(w)!=empty implies F(w) intersect D_B(w)!=empty.    (1)

The source menu being ambiguous means that its singleton status is false
at every owner. Thus the factor B_r(E_r(w)) is exactly the conjunction,
over the marked path's r-owned ancestors, of the assertions that the
corresponding sibling does not evaluate to {r}. This remains true when a
sibling contains other occurrences of j: those occurrences also have false
r-singleton status at w.

If D_B(w) is nonempty, choose the ancestor nearest the root whose sibling
is a singleton of that ancestor's owner. Write r for that owner. At this
node the result is {r}, and r belongs to D_B(w). Above it there is no
owner-singleton sibling. A different owner cannot absorb away r: its
current child contains r, hence cannot itself be that different owner's
singleton, and its sibling is not that singleton either. An r-owned node
also retains r. Therefore r reaches the root, proving (1).

For completeness, if D_B(w) is empty, the marked ambiguous menu reaches
the root intact. No sibling can absorb it, and its ambiguity prevents the
current branch from becoming an absorbing singleton. Thus in this case
w_j is contained in F(w), which also follows from type soundness.

In particular, a unique failed factor has the unconditional side effect

    D_B(w)={s} implies s in F(w).                        (2)

No observer-owner atom is excluded in (1) or (2). The old causal-drift
test is a special case: if observer k has no singleton input, B_k is true
because E_k is empty. If B_s is false and all other factors except possibly
B_k are true, then D_B={s}, and (2) gives the old conclusion. The new law
also applies when every owner has singleton inputs, and when several owner
factors fail simultaneously.

The condition is directly checkable on a proposed full type and target
operation. For a target specified by canonical prime guards, their source
reconstruction supplies the output occurring in (1); no witness graph or
term for the proposed type appears in the condition.

## Soundness, causal drift, and owner-shadow are not sufficient

Choose c in I and variables X,Y,Z_r for every r in I\{c}. Define the
actual core operation

    F = X union UNION_(r!=c) (Y choice_r Z_r).             (3)

It has K+1 variables. At source X consider the full type

    B_c=[Y!={c}],
    B_r=true for every r!=c.                              (4)

This type passes all three necessary tests from source-type-pruning.md.

**Soundness.** The operation F always contains the entire menu X. Every
contribution of any source-X type is therefore contained in the target
source coefficients. In particular (4) is globally sound.

**Causal drift.** Only the c-factor can fail, and it fails precisely when
Y={c}. Let k!=c be an observer with no k-singleton input. Then Z_k!={k},
so Y choice_k Z_k retains c. The outer union in (3) retains it as well.
Thus every c-drift test passes; tests involving any other failed factor
are vacuous.

**Owner-shadow incidence.** For r!=c, the only prime avoidance guard of
the true factor is empty, giving hyperedge {X}. Its incidence obligation
holds because F always contains X. At c, the single prime avoidance guard
is {Y}, giving hyperedge {X,Y}. In the corresponding pure-c tests every
Z_r equals {c}. Since r!=c, every branch Y choice_r {c} contains Y:
an absorption at r can only return the already-singleton menu Y={r},
and otherwise the branch takes union. Hence F contains both X and Y on
these tests, proving both required incidences.

Nevertheless the type is not actual. Set

    X=I\{c},   Y={c},   Z_r={r} for every r!=c.            (5)

The source X is ambiguous because K>=3. Every owned branch in (3)
absorbs to {r}, so F at (5) is exactly I\{c}. But (4) has D_B={c}
there. Equation (2) would force c into the output of any realizing term
containing that type, a contradiction.

The same argument excludes any subordinate core term S<=F carrying the
type: (2) would give c in S at (5), whereas F omits c there. Thus a
marked-union construction cannot insert this sound, drift-safe,
owner-shadow-safe type into F.

For K=3 take c=2. The example is simply

    F=X union (Y choice_0 Z_0) union (Y choice_1 Z_1),

with witness valuation (X,Y,Z_0,Z_1)=({0,1},{2},{0},{1}).
Its output is {0,1}, while the proposed type would force 2.

## A sound coordinatewise join of actual types need not be actual

The same target (3) refutes a possible amalgamation rule. Write
H_r=Y choice_r Z_r and, for r!=c, put

    T_r=(X choice_c Y) choice_r H_r.

This operation is contained in X union H_r. If H_r={r}, its outer
r-gate absorbs to {r}. Otherwise H_r contains Y, while the inner
word is contained in X union Y; conservativity at the outer gate
gives the claimed inclusion. Hence T_r<=F.

Its single X occurrence has full type

    B^(r)_c=NOT Y_c;
    B^(r)_r=NOT Y_r AND NOT (Z_r)_r;
    B^(r)_s=true for every s notin {c,r}.                  (6)

Union T_r with F. The result is F, and the marked-union lemma from
[source-type-pruning.md](source-type-pruning.md) preserves (6), since
it is globally sound by T_r<=F. Thus each B^(r) is an actual F type.

Choose distinct r,s different from c, possible because K>=3. Their
coordinatewise OR is exactly

    (B^(r) OR B^(s))_c=NOT Y_c;
    (B^(r) OR B^(s))_q=true for every q!=c.               (7)

This is the globally sound but nonactual type (4). It also passes
causal drift and owner-shadow, by the preceding proof. Therefore the
actual full types are not closed under coordinatewise joins even when
the joined vector is globally sound. No assertion about existence of
different least upper bounds within the actual-type poset is needed.

This does not refute a version restricted to globally source-separable
targets. Although the source-X coefficients of F are unconditional,
the source-Y, observer-c coefficient is

    OR_(q!=c) [Z_q!={q}].

Every pure-owner Y coefficient is true: a branch with a different owner
still supplies the source. But the displayed mixed coefficient is
false when all Z_q={q}. Thus the target is not source-separable at Y.
The example shows that separation at the marked source alone cannot
justify actual-type amalgamation. The
[complete-head circuit family](complete-head-circuits.md) also refutes
it for a fully source-separable target: two explicit actual head types
join to its nonactual canonical full vector. That target has no
greatest actual type at any head, although its greatest coefficients
at the old observers are jointly attainable.

Moreover the unconditional source-X type is actual, from the explicit
X branch of (3). The missing joined type is a weaker type, not the
canonical greatest type. Hence this join counterexample does not
answer those questions. The complete-head family settles maximal full
types negatively while preserving old-observer free-product attainment;
that latter general problem remains separate.

## Scope

This refutes the conditional classification of actual full occurrence types
by soundness, causal drift, and owner-shadow incidence, even for an explicit
genuine core target. The stronger all-owner law is necessary; no sufficiency
claim is made for it.

The example concerns exact occurrence types. Its proposed type is dominated
by the unconditional source-X type, so it does not by itself show that taking
the disjunction of all old-test-safe types overestimates the greatest
term-induced free coefficient extension. That separate coefficient-level
question remains untouched by this counterexample.
