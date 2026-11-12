# The canonical column-sound clutter always fails at nontrivial arity

Mathematical research, without Lean claims. Taking every column-sound
clause gives a canonical clutter, but it cannot replace the quantified
admissible diagrams in the closed hypergraph criterion. At every arity
n>=2 it fails NoTrap already on n isolated-source probes. The failure is
literal and does not depend on a search, a chosen elimination order, or
semantic completeness of the diagram theorem.

There is nevertheless a greatest admissible subfamily of the column-sound
supports. Its existence does not give a short intrinsic characterization:
it is exactly the family of clauses valid on the generated core relation.

## Column-sound supports

Let R be a finite row set, I a finite owner set with at least three owners,
and V a finite nonempty variable set. The projection columns are tuples
of nonempty winner menus, one tuple for each variable.

A clause has either no premise or one membership premise p=(q,k), and a
head S subseteq R times I. Write Sound(p,S) when every projection column
satisfies the clause. Sound is upward closed in S. At each premise take
all inclusion-minimal sound heads; their indexed clutters form the
canonical column-sound diagram D_sound. Its supported heads are exactly
the sound heads.

This diagram satisfies the boundary conditions: row-full nonemptiness,
weakening of pure clauses to conditional clauses, and membership
tautologies. The issue is NoTrap.

## A literal n-probe failure

Fix different owners r,k. For each variable j introduce the canonical
isolated-source probe q_j at observer k:

    variable j has value {k};
    every other variable has value {r}.

These are genuine canonical source probes, with no neutral entries.
Consider the pure head

    H={(q_j,k): j in V}.

Every column meets H at exactly its own vertex. Hence H is column-sound
and inclusion-minimal: deleting (q_j,k) makes column j miss the head.
It is therefore an actual pure edge of D_sound.

For owner r the r-coloured part of H is empty, so the empty cut is an
allowed proper initial cut. At a candidate exposed vertex (q_j,k), the
required pure blocker has head

    B_r(empty,q_j)={(q_j,s):s!=r}.

Since n>=2, choose another column ell!=j. Its value at q_j is {r}, so
it misses this blocker. The blocker is not column-sound and cannot be
supported by D_sound. No head vertex can be exposed. Thus NoTrap fails
at this one cut of H.

The same proof applies when the row set contains the entire canonical
probe table: H uses only the displayed n rows, remains a minimal sound
head, and its blockers are still missed by the indicated columns.

There is also a two-leaf counterterm to the pure head. Choose different
variables a,b. At every displayed row,

    x_a choice_r x_b = {r}.

At q_a or q_b one operand is the absorbing singleton {r}; at every other
row both operands are {r}. Hence the term misses H everywhere. The
canonical column-sound diagram contains a clause that is not core-valid,
and NoTrap detects it uniformly at every nontrivial arity.

## What all column-sound clauses actually describe

Identify a row tuple with its set of membership atoms. Write C_j for
the atom set of projection column j, and let

    U={UNION_(j in J) C_j : empty!=J subseteq V}.

**Lemma.** The models of all column-sound clauses are exactly U.

Every such clause is preserved under nonempty unions. For a conditional
clause, a premise atom in a union occurs in some input column, whose
head witness remains in the union. Pure clauses are preserved as well.
Thus every member of U is a model.

Conversely take an atom set X outside U, and put

    J_X={j:C_j subseteq X},
    U_X=UNION_(j in J_X) C_j.

If J_X is empty, every column meets the complementary head (R times I)\X.
That pure sound clause separates X.

If J_X is nonempty, U_X cannot equal X, or X would belong to U. Choose
p in X\U_X. Every column containing p must meet (R times I)\X: otherwise
it would be contained in X and put p in U_X. Therefore the conditional
clause

    p implies OR ((R times I)\X)

is column-sound and is violated by X. This proves the lemma.

Thus D_sound presents the nonempty-union closure of the columns, rather
than their closure under all owned choices. The n-probe construction
exhibits the discrepancy without appealing to this semantic description.

## Admissible sound support families are closed under union

Fix the same finite columns. Let D_lambda be any nonempty collection of
admissible diagrams containing those columns. Define a new support
predicate by

    Supports_union(p,S) iff some D_lambda supports (p,S).

It is upward closed. Since the atom set is finite, taking its minimal
heads gives a diagram D_union with exactly this support predicate.
Equivalently, unite the old heads at each premise and delete all
nonminimal heads.

Boundary holds. A pure support came from some old diagram and therefore
has every conditional weakening there; row-full supports and tautologies
are present in any old diagram. Column soundness is also preserved.

For NoTrap, let H be a minimal union head at premise p. It is supported
in some D_lambda, so that diagram has an edge J subseteq H. The union
also supports J. Minimality of H forces J=H: H was itself an old edge.
For any owner and proper initial cut of H, apply that old edge's NoTrap
condition. Its exposed vertex and every required blocker remain supported
in the union. Thus D_union is admissible.

Consequently there is a unique greatest admissible column-sound support
family: take the union over all such families. The collection is nonempty,
since the universal relation of nonempty row menus is invariant, contains
the columns, and has its boundary/tautology presentation. Finiteness
ensures only finitely many distinct supports can occur.

## Identification of the greatest admissible family

Let G be the relation of all tuples obtained by core words from the
projection columns. Every admissible diagram containing the columns
contains G among its models, by invariance. Hence every support in their
greatest union is a clause valid on G.

Conversely, the canonical all-valid-clause diagram of G is admissible by
the closed hypergraph theorem, and contains the columns. It is one of the
families in that union. Therefore the greatest admissible column-sound
support family consists exactly of all clauses valid on G; its model
relation is G itself.

This fact explains what a successful canonical pruning would have to
recover. It does not provide the desired direct guard criterion. Naming
the greatest admissible subfamily a cycle core, or specifying it by a
greatest fixed point, only restates the missing recognition step.

The [five-probe shortcut counterexample](canonical-blocker-shortcut.md)
shows that testing all cuts of one target against column-sound blockers
can accept a false clause. The uniform construction here gives the
complementary global barrier: taking all sound prime heads and checking
their NoTrap obligations fails at every arity n>=2. Neither procedure
eliminates the need to justify the auxiliary supports.
