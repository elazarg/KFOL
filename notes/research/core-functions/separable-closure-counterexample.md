# Hereditary closure profiles and global omission still do not suffice

Mathematical research, without Lean claims. Four variables and three owners
give a source-separable noncore operation satisfying loopless owner closure
laws, every colored-closure idempotence law, full Q-outcast, span-outcast,
maximal admissible profiles, and the exact atomic-profile law. Every nonempty
neutral residual is nonempty, and every restricted closure family has
admissible profiles. The operation also satisfies global omission
independence and whole-input provenance. Every proper identification minor
is core.

A dictator wrapper supplies the general mechanism. At three owners it can
hide a base operation's failure of omission independence while preserving
its neutral residual. Consequently global omission does not imply omission
for neutral faces of synthetic separable operations. This example does not
settle a criterion requiring every proper neutral face to be core.

## Dictator wrapping of a colored closure family

Let R be a finite nonempty variable set and let h_r be loopless closures
on R, one for each old owner r. Their source-separable reconstruction H is

    k in H(w) iff some j with k in w_j lies outside
                         UNION_(r!=k) h_r(E_r(w)).

The auxiliary H is allowed to have empty values. Add a new variable W,
put V=R union {W}, and define

    c_r(E)=V if W in E;
           h_r(E) otherwise.                              (1)

Every c_r is again a loopless closure. Let F be its source-separable
reconstruction. Then

    F(w,W)=W if W is a singleton;
           W union H(w) otherwise.                        (2)

An atomic W={r} makes c_r(E_r)=V and removes every other winner. Its own
source survives because no foreign closure generates W. If W is ambiguous,
it belongs to no atomic set and no closure captures it; its whole menu
survives, while the base sources contribute exactly H. This proves (2),
including when H is empty.

The c_r are F's canonical pure-owner closures: at a pure-r source probe
only the r-atomic set can contribute a rival filter, so its coefficient is
exactly [j notin c_r(E)]. No term realization is used in this recovery.

The wrapper has the following closed properties.

* F is nonempty and contains W. Its complete singleton profiles are the
  maximal dictator tuple Phi_r(E)=[W in E], and it satisfies the full
  atomic-profile law F={r} iff c_r(E_r)=V iff W={r}.
* Colored-closure idempotence for c is equivalent to that for h. In a full
  coloring alpha, a seed set T containing W closes to V. A seed set not
  containing W closes entirely inside R, exactly by the base colored map.
* Span-outcast always holds. Spanning is equivalent to W being atomic at
  that owner. An ambiguous W is in Q and cannot be restored as a blocked
  position; an atomic W is retained at its original owner.
* Hereditary profile admissibility is inherited exactly. On a nonempty
  U subseteq R the restricted closures are h_r restricted to U. When W
  belongs to U, every restricted spanning predicate is the dictator W.
* Every neutral residual containing W is nonempty. Residuals on nonempty
  U subseteq R are exactly the base residuals H_U.

Full Q-outcast follows whenever the base colored maps are idempotent, by
[the colored-closure equivalence](mixed-closure-outcast.md). The wrapper
therefore satisfies both outcast laws, including saturated fibres.

## Three-owner omission is automatic for the wrapper

Now let the old owner set be exactly {0,1,2}. The wrapper satisfies global
omission independence for every loopless base family, independently of
whether H satisfies that law.

Suppose F omits winner r and replace arbitrarily all inputs originally
containing r, leaving the other inputs fixed. If W is atomic, it omits r
and stays unchanged; equation (2) fixes the same output. If W is ambiguous,
it must be I\{r}, since it is contained in F. Thus W is again unchanged
and F=W.

Every original r-containing source was blocked by some foreign closure
c_s(E_s), s!=r. All original s-singleton positions omit r and stay fixed;
the foreign atomic sets can only increase. Their blockers persist by
monotonicity. Positions originally omitting r are unchanged and cannot
become new r-sources. Hence the changed output still omits r and still
contains W=I\{r}, so it is exactly the original output.

This argument specifically uses three owners. The wrapper may mask a
noncore base residual without satisfying analogous omission laws at larger
owner sets.

## A three-variable base

Take R={A,B,C} and owners {0,1,2}. Define

    h_0(E)=E union ({C} if {A,B} subseteq E else empty);
    h_1(E)=E union ({B} if C in E else empty);
    h_2(E)=E.                                             (3)

These are loopless closures. Every base colored map is idempotent. The
only possible new consequences are C from 0-colored A,B and B from a
1-colored C. If adding C activates the second rule, its consequence B
was already a seed of the first rule. If adding B activates the first,
its consequence C was already a seed of the second. No second application
can add a new position.

The complete base profiles are

    Phi_0(E)=[{A,B} subseteq E];
    Phi_1(E)=[{A,C} subseteq E];
    Phi_2(E)=[E=R].

They are admissible because every winning coalition contains A. The
proper neutral restrictions have these closure/profile descriptions:

* On {A,B} and {A,C}, all restricted closures are identities, so every
  owner has unanimity and the operation is input union.
* On {B,C}, only h_1 remains nontrivial, with C implying B. Its operation
  is C union (B choice_1 C), so its profiles are C at owner 1 and BC at
  the other owners.
* On each singleton the residual is its projection.

Thus every restricted profile tuple is admissible, and every nonempty
base neutral residual is nonempty. At the full base, A is never generated
by any h_r and therefore its entire menu always survives: H contains A.

The base nevertheless violates omission independence. At

    A={0}, B={1,2}, C={1},

its output is {0,1}; replacing B by {0} changes the output to {0}.
Both outputs omit 2, while the changed input originally contained 2.
The first value follows because h_1({C}) blocks B but not A or C. At
the second valuation h_0({A,B}) spans R and the output is {0}. Hence H
is a nonempty noncore operation.

For later calculations, its full values have the elementary description

    H={0}             if A=B={0};
      A union C       otherwise, if C={1};
      A union B union C otherwise.                       (4)

The first case takes priority. Only the 0-rule can block C, and only the
1-rule can block B; their surviving same-owner contributions are already
supplied by A or C respectively. This proves (4) directly from the source
formula.

## The four-variable counterexample

Apply (1) to the base (3). The resulting F on A,B,C,W has all the
properties in the opening statement.

It is idempotent and inclusion-monotone. Idempotence follows from the
source formula on equal inputs. For monotonicity, increasing a menu can
only remove its rival singleton flags and add winner membership; the
closure filters cannot turn a surviving source off. Whole-input provenance
also holds: by (4), H is {0}, A union C, or the whole base union. Each
output winner has a whole input menu contained in F, using W itself in
the atomic-W case.

Every variable is essential. For example, with W={1,2}, B={0}, C={1},
changing A from {0} to {1} changes F from I to {1,2}. With A={0},
C={1}, W={0,2}, changing B from {0} to {1} changes F from {0,2} to I.
With A={0}, B={2}, W={0,1}, changing C from {1} to {2} changes F from
{0,1} to I. Atomic choices of W show its own essentiality.

All hereditary spanning predicates

    Phi_r^U(E)=[U subseteq c_r(E)]

are admissible, by the wrapper theorem and the base restrictions above.
Every nonempty neutral residual is nonempty: those retaining W contain
W, and those deleting W are the already described H_U.

Nevertheless deleting W by winnerwise neutral sections gives exactly H.
For each winner k, put W=I\{k}; equation (2) gives

    k in F(A,B,C,I\{k}) iff k in H(A,B,C).

Core neutral elimination says this residual must be zero or a genuine
lower-arity core operation. H is nonempty and violates omission, so F
cannot be core.

Thus every global law listed above coexists with a noncore neutral facet.
In particular the wrapper's global omission independence does not descend
to that facet. Nonemptiness of all neutral faces is substantially weaker
than core realizability of all those faces.

## Every proper identification minor is core

The base H has these three binary identification minors, directly from
(4):

    H(U,U,C)=U union (U choice_0 C);
    H(U,B,U)=U union (B choice_1 U);
    H(A,U,U)=A union U.                                   (5)

Consequently identifying any two base variables in F gives the core reset
of a core binary operation against W.

Identifications with W also have explicit core words. Write Reset(T,U)
for the standard core reset: U when U is atomic, and U union T otherwise.
Then

    F(U,B,C,U)=Reset(C union (B choice_1 C),U);
    F(A,U,C,U)=Reset(A union C,U);
    F(A,B,U,U)=Reset(A union B,U).                        (6)

For the first identity, ambiguous A=U prevents the 0-rule from firing, and
(4) reduces to U union C union (B choice_1 C). For the second, ambiguous
B prevents the 0-rule; the wrapper restores B even when the 1-rule blocks
it. For the third, ambiguous C prevents the 1-rule; the wrapper restores
C even when the 0-rule blocks it. Atomic U always gives U. This proves
(6). Every further identification is a minor of one of these core words,
so all proper identification minors are core.

## Safe individual full types still do not give a common realization

For each source j take its canonical factor vector

    B^(j)_r(E)=[j notin c_r(E)], for E subseteq V\{j}.

Each vector is antitone and normalized by looplessness. It is globally
sound by the defining source-separation formula. Owner-shadow incidence
holds because each c_r is a closure. The all-source side-effect proof in
[separable-closures.md](separable-closures.md) uses source attribution,
omission independence and loopless separation; all three have been
verified for this F. Hence these vectors also pass the all-owner
side-effect law, and therefore its causal-drift specialization.

Moreover these vectors cover every positive canonical source bit:
at observer k their product over r!=k is exactly F's source coefficient.
Thus one proposed full type per source covers all the guards, and every
type passes soundness, normalization, owner-shadow, drift and all-owner
side effects. Yet the covered operation is not core.

This refutes sufficiency of those individual-type tests as a general
guard-realizability criterion. It does not refute a conditional theorem
about actual types when the target is already independently known to
be core; that hypothesis fails for this synthetic F.

## Common-carrier consequences and scope

The c_r define the canonical candidate G_Q on B_I: return a spanning
owner's atom, otherwise P exactly when the P-marked positions meet Q,
and N otherwise. The closed proofs in
[canonical-separable-extension.md](canonical-separable-extension.md)
show it is flat-order monotone, agrees with the synthetic F observer view
on every omitted-atom face, and preserves the full ternary outcast relation.
Both Q-outcast and span-outcast have been verified here.

This G_Q is not core either: a realizing word would have F's old observer
views and therefore would realize F, contradicting neutral elimination.
Its agreement with synthetic old faces does not assert those faces are
core. The question whether G_Q is attained for an already genuine
source-separable core F remains open.

The counterexample rules out the proposed combination of hereditary
profile admissibility, nonempty neutral residuals, colored closure
idempotence, global span-outcast, and global omission. It leaves open
stronger compatibility tests imposing the full core laws on every neutral
face, and the general direct criterion for jointly realizable guards.
