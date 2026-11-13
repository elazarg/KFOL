# Acyclic source compatibility and its canonical normal form

The acyclic subclass is solved mathematically. The complete proofs are in
[appendix-core-acyclic.tex](../../../sections/appendix-core-acyclic.tex), under
`core:lem:captured-rectangle`, `core:lem:source-pattern-reduction`, and
`core:thm:acyclic-source-guards`. These are written proofs, not Lean claims.
The unrestricted cyclic characterization remains the full target.

## Intrinsic criterion

Fix finite K>=3 and a nonempty source-reconstructing operation F.
Its complete source families must agree across observer overlaps and be
antitone. A source order puts every predicate pi_i after all the inputs
whose passive statuses it depends on; equivalently the source-dependence
graph is acyclic. Under that hypothesis, F is core exactly when it satisfies
the full colored-cofactor law:

    pi_i(E)=0 iff fixing the proper coloring E makes the entire
                  cofactor independent of input i.

The positive direction is witnessed at the canonical probe, so only the
zero-implies-independence direction needs checking. No term, unknown helper,
recursive recognition test, or auxiliary invariant clutter occurs in this
criterion. Full independence permits arbitrary changes of an unfixed menu,
including its atomic color.

## Captured-input rectangles

Let C be an actual core prefix and F_P a synthetic interval operation
C<=F_P(X,v)<=C+X satisfying full colored FD. Let proper R capture each
input in B under C, with no B-input fixed by R, and suppose P(R)=1.
Then

    Q_(R,B)(E) = AND_r [E_r\B subseteq R_r]

is contained in P. It ignores B and allows only R's color or neutrality
at every other input.

For E in this rectangle put T=R union E|_B. If T is proper, full passive
FD lets one add its captured colors without changing the sole X-query;
thus P(T)=P(R)=1 and antitonicity gives P(E)=1.
If T uses every owner, choose l unused by R. The entire l-block is captured,
and the same proper argument gives P(T^hat l)=1. If P(T^hat k)=0 for any k,
full FD of the NEW source X would make it inessential under T^hat k.
Extend to T, assign every still-uncolored passive N_l, and vary X between
N_l and l. The prefix omits l because all its l-sources are captured;
the new source supplies l exactly at the latter input, a contradiction.
Choose k missing from E and use E subseteq T^hat k.

This is the step that handles the missing-observer hole. T need not color
every input; 'uses every owner' concerns its palette only.

## Active reduction of a positive pattern

For a proper predecessor coloring q in a source-ordered core C define

    J(q)={i:pi_i(q restricted to predecessors of i)=1},
    R(q)=q restricted to J(q).

Every input outside J(q) is captured under R(q). Induct in source order:
earlier excluded inputs were captured under the retained prefix, so full
FD permits recoloring them to their q-values in a sole-source probe.
Thus pi_i(R(q)|_<i)=pi_i(q|_<i). A zero captures i; extending to the
full R(q) preserves its independence.

For any positive P(q), antitonicity gives P(R(q))=1. The rectangle lemma
therefore puts the following one-box predicate inside P:

    Q_q(E)=AND_r [E_r intersect J(q) subseteq q_r].

## Safe reverse-order spines

Start at X. For i in J(q) in DECREASING source order, attach v_i once at
each owner r for which i is not colored r by q. An uncolored i is attached
at every owner. The order within an input's group is arbitrary but fixed.
The marked X-occurrence has exactly source factor Q_q.

Every helper occurrence is safe below C+X. If a helper i supplied a winner
k absent from C, its actual foreign-k predecessor coloring T would have
pi_i(T)=0. Apply the rectangle lemma again, now to the ACTUAL core prefix
C_<=i over C_<i, with distinguished source i and positive pattern q|_<i.
If T matched all its active constraints, the lemma would force pi_i(T)=1.
Hence some earlier active j<i has actual menu {r}, r!=k, forbidden by q_j.
Its r-owned group lies higher on the reverse-order spine and kills that
particular marked helper occurrence's contribution. All helper occurrences
are covered separately; later reintroduction comes from a different
occurrence and receives its own argument. Union with C realizes Q_q.

## Global compilation

Identically unused sources are globally inessential by FD at the empty
coloring and may be omitted. The first remaining source is unconditional,
so its prefix is a projection. Every later prefix is a neutral residual
with unchanged earlier guards and inherited full FD. Adjoining its last
source is an interval extension of its already core predecessor prefix.
The preceding construction therefore realizes each prefix inductively.

For each source i it suffices to use maximal positive proper predecessor
colorings q. Every positive coloring extends to one of them; its Q_q is
antitone and covers that coloring. The union of ALL the raw-variable
spines, over all sources, is exactly F. No unknown intermediate operation
or helper occurs in this final normal form.

With union named, the leaf count is at most

    (1+K(n-1))*n*K^n.

Each distinct predecessor coloring is represented by one canonical probe
with later inputs neutral, so there are at most n*K^n chosen spines.
Each has one marked leaf and at most K attachments per predecessor.

## Principal singleton profiles

For owner r put M_r={i:pi_i(all predecessors colored r)=1}.
Pattern reduction at the all-r coloring shows that fixing M_r to r
captures every other input and forces r. Any r-forcing coalition omitting
i in M_r would allow pi_i>=1 by antitonicity and hence a foreign winner
at its sole-source probe. Thus

    Phi_r(F)(A)=1 iff M_r subseteq A.

## Scope of the remaining problem

Core operations can have cyclic source dependence: x choice_a y already
has a two-cycle. The theorem does not reject those operations. It removes
acyclic dependence from the unresolved part of joint guard compatibility;
the remaining full target must account for feedback components and their
interactions. The prime Gray obstructions show that their size and locality
cannot be bounded in advance.
