# Full-support branching cannot be eliminated at three inputs

This research counterexample has a finite closed certificate and a separate
four-row analytic argument below. It is not yet a Lean theorem. The example
refutes the envelope-spine normal form with unbounded owner repetitions.
Since every binary core operation is its greatest profile completion, it also
refutes arbitrary finite unions of ternary terms each having an input used
at most once. The obstruction holds for every ambient role set K>=3.

Let E(phi,S) be the greatest core completion on a nonempty variable support S of an admissible full singleton-profile tuple phi. On a valuation it returns the unique prescribed singleton, if there is one, and otherwise the union of the inputs in S. A proposed envelope spine starts at a variable or at one such completion and repeatedly combines its current result with another greatest completion by an arbitrary owned choice. Owners may repeat. Also allow arbitrary finite unions, including unions between these actions.

## An explicit core counterexample

Use owners 0,1,2 and variables X,Y,Z. Set

    A = X star_2 (Z star_2 Y),
    H = Z star_1 Y,
    B = (X star_0 H) star_1 (H union Y),
    x = Y star_0 A,
    y = X star_0 B,
    F = x star_1 y.

Both A and B are themselves greatest profile completions with full support:

| Completion | owner 0 profile | owner 1 profile | owner 2 profile |
|---|---|---|---|
| A | XYZ | XYZ | X OR Y OR Z |
| B | YZ | Y OR XZ | XYZ |

The standalone checker verifies their complete 343-entry winner tables against these greatest-completion formulas. Thus the counterexample is a literal core word, with derived core union, rather than a function supplied by a search oracle.

The following five singleton-input rows suffice:

| Row | X | Y | Z | F | observation |
|---|---|---|---|---|---|
| A0 | 1 | 0 | 1 | {1} | owner 0 absent |
| A1 | 2 | 1 | 0 | {1,2} | owner 0 absent |
| A2 | 1 | 0 | 0 | {0} | owner 1 absent |
| A3 | 0 | 2 | 1 | {0,2} | owner 1 absent |
| Q | 0 | 1 | 2 | {0,1,2} | owner 2 present |

Every function in the proposed envelope-spine/union language satisfies the persistence clause

    2 in output(Q) implies
      0 in output(A0) or 0 in output(A1)
      or 1 in output(A2) or 1 in output(A3).

F violates it. Consequently no union of envelope spines bounded by F can cover its positive owner-2 observation at Q.

## Every binary core operation is a greatest completion

**Lemma.** On its syntactic variable support, every core operation using at
most two variables is its greatest singleton-profile completion.

One used variable gives projection. Suppose both inputs A,B occur. If both
are ambiguous, all subterm values are ambiguous unions, so the result is
A union B. If exactly one is a singleton {r} and the other is ambiguous B,
induction gives:

* a subtree using only the singleton input has value {r};
* one using only B has value B;
* one using both has value {r} or B union {r}.

At a mixed node the only possible absorbing singleton is {r}; otherwise
both input contributions remain. This proves the induction, including the
case r belongs to B. If both inputs are singleton menus, any ambiguous
output is their union by conservativity. Thus every ambiguous final value
is the full input union. The singleton profiles already determine all
singleton cases, proving the lemma. For example reset(X,Y) is exactly the
greatest completion of projection-Y profiles on support {X,Y}; a variable
can belong to the support without being essential in any profile.

Now follow the unique occurrence of an input appearing once in a ternary
term. Each sibling subtree uses only the other two inputs and is therefore
a greatest completion by the lemma. The term is an envelope spine. A term
omitting an input uses at most two variables and is itself an allowed
completion. Consequently every ternary term with some input occurring at
most once belongs to the envelope-spine language defined above.

The certificate below therefore proves that **every term realizing F uses
each of X,Y,Z at least twice**, and that even finite unions of terms with
an input used at most once cannot realize F. The conclusion does not depend
on having proposed greatest completions as a normal form.

It also forces genuine branching at full support. Any term in which every
node has at least one child that is a greatest completion is an envelope
spine, by induction. Thus any realizer of F has a node whose two children
are both nongreatest operations. The binary lemma makes both child supports
all of {X,Y,Z}. Replacing general tree synthesis by a single chain of
recursively nonmaximal full-support subproblems loses this example.

## A small closed certificate

There are exactly 18 normalized monotone Boolean functions on three inputs. Enumerating the admissible triples by rainbow common-source intersection, and every nonempty support containing their profile dependencies, gives 625 greatest profile completions. Thus profile-inessential support variables are included. Their restrictions to the five rows above give exactly 100 different five-tuples of nonempty winner masks.

The certificate is an explicit relation R of 416 five-tuples. It contains the three projection columns and all 100 envelope tuples. It is closed under:

* coordinatewise union;
* x -> x star_r E for every owner r and every one of the 100 envelope tuples E.

Every tuple in R satisfies the displayed persistence clause. In fact the only tuples satisfying all four negative observations are, in winner masks 1=owner0, 2=owner1, 4=owner2,

    (2,2,1,5,2), (2,6,1,1,1), (2,6,1,5,3).

None has owner 2 at Q. The counterexample tuple is (2,6,1,5,7).

Thus certificate soundness needs only the stated inclusions and finite closure checks, followed by induction on the proposed normal form. It does not require proving that a term enumeration or relation-generation search was exhaustive. The standalone standard-library checker regenerates the relation, then independently verifies every inclusion and closure obligation. It also enumerates all admissible full profiles and supports directly; no SAT solver, auxiliary clone data, or external package is used.

Files:

* `envelope-spine-counter-check.py`: self-contained checker (about 0.2 seconds).
The checker constructs its finite relation directly and verifies every inclusion, closure and separation condition; no external certificate file is needed.

## Four-row analytic obstruction to a linear supplying source

For the focused source-linear claim, no finite-state certificate is needed.
Use just A0,A1,A2,Q from the table. Every term in which Z occurs exactly
once satisfies

    2 in output(Q), 0 notin output(A0), 1 notin output(A2)
        imply 0 in output(A1).                             (L)

Follow the Z occurrence from leaf to root. Each step takes its current
value star_r G(X,Y), for a sibling G that omits Z. At A0 and A2 the sibling
has the same value E because (X,Y)=(1,0) at both rows, while the initial
Z values are {1} and {0}. All values on these rows stay inside {0,1}.
The two final negative demands therefore force the output pair ({1},{0}).

The only way one step can produce this pair is:

* r=0, E={1}, and the preceding pair was ({1},{0}); or
* r=1, E={0}, and the preceding pair was ({1},{0}).

For r=0, the first output can be {1} only if both its operands are {1};
the second output then needs its current operand {0}. The r=1 argument
is dual. Any other owner acts as union on these menus, which cannot produce
both distinct singleton outputs with one common nonempty E. Working
backwards, every step has owner 0 or 1 and the distinguished pair is
preserved throughout the spine.

At Q, all siblings take inputs X={0},Y={1}, so none contains 2. Its presence
at the final output must survive continuously from the Z leaf. At A1, the
initial Z is {0}. Removing 0 would require an owner-1 step with G(A1)={1};
owner 2 is already excluded, and owner 0 cannot remove 0. But Y={1} at
both A1 and Q, while X is not {1} at either. G's owner-1 singleton profile
therefore makes G(Q)={1} as well. That step would absorb away 2 at Q,
which can never be restored. Thus 0 survives at A1, proving (L).

F violates (L), so no term realizing it can use its supplying variable Z
once. More strongly, a finite union of source-linear subordinate witnesses
cannot cover its owner-2 observation at Q: only Z supplies 2 there, so any
such witness would have to use Z once, contradicting (L).

## Uniformity in added owners

All displayed rows use only the three owners 0,1,2. An additional-owner gate
acts as union on these values. In any sibling binary operation, replace
such gates by the derived union on 0,1,2; its restriction is a core binary
operation over that triple and hence one of the greatest completions covered
by the certificate. The 416-state relation is union-closed, so it also admits
additional-owner spine actions. Both the finite-certificate conclusion and
the analytic source-linear obstruction hold uniformly for every ambient
role set containing these three owners.
