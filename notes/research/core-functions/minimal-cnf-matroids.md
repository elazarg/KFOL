# Globally minimal two-owner CNFs are exactly matroid CNFs

Mathematical research, without Lean claims. The matroid construction has a
converse: a finite full-support two-owner CNF is globally minimal precisely
when its prime clause clutter is a loopless matroid's cocircuit family and
all its other clauses are complements of flats of that matroid. Factoring
also gives, for each chosen source, a realizer using that variable once and
attaining both canonical source factors at the same occurrence.

Fix a finite owner set I with K>=3, distinguished owners 0,1, and a finite
nonempty variable set V. All operations act on nonempty winner subsets of I.
Terms use primitive owned choices, without constants or role switches.
An operation is globally minimal if no different core operation lies below
it in pointwise winner-set inclusion.

Let Ccal be a finite nonempty family of nonempty subsets covering V. For
each clause C write q_C for the choice_1 fold of its variables, and put

    F_Ccal=FOLD_choice_0_(C in Ccal) q_C.                  (1)

Both owned choices are associative, commutative, and idempotent, so order,
association, and duplicate clauses do not affect this definition. Write
Dcal for the inclusion-minimal members of Ccal, its prime clause clutter.

## Factoring decreases winners

**Subdistributivity lemma.** For distinct owners r,s and arbitrary nonempty
winner menus A,B,C,

    A choice_s (B choice_r C)
        subseteq (A choice_s B) choice_r (A choice_s C).  (2)

If A={s}, or if B=C={s}, both sides are {s}. Exclude those cases. If B
or C is {r}, the left side is A union {r}. One right-hand child is exactly
this menu. The outer r-choice either takes union and retains it, or absorbs
to {r}; that absorption requires A={r}, in which case the left side is
also {r}. If neither B nor C is {r}, the outer right-hand choice cannot
absorb: one of its children could equal {r} only if A and the corresponding
B or C were both {r}. Its value is therefore the union of the two children.
If neither B nor C is {s}, this is A union B union C. If just one is {s},
the other child still contains A, giving the same union. The excluded case
B=C={s} completes the proof.

By induction and monotonicity of owned choices, (2) gives

    x_j choice_1 (FOLD_choice_0_i H_i)
        subseteq FOLD_choice_0_i (x_j choice_1 H_i)       (3)

for every finite nonempty family of nonempty core terms H_i. All folds
here are actual nonempty folds; no units or constants are introduced.

## The clutter converse

**Theorem.** Suppose Ccal is a clutter covering V. Then F_Ccal is globally
minimal if and only if Ccal is the cocircuit family of a loopless matroid.

The matroid-to-minimality implication is proved in
[matroid-core-operations.md](matroid-core-operations.md). For the converse
we prove the cocircuit elimination axiom.

Suppose elimination fails. There are distinct clauses C_1,C_2 and
j in C_1 intersect C_2 such that no clause lies in

    U=(C_1 union C_2)\{j}.

Choose i in C_2\C_1; this is possible because the clauses form an
antichain. Group the j-containing clauses and factor out j. Specifically,
let A be the choice_0 fold of clauses avoiding j, when that family is
nonempty, and set

    Q=FOLD_choice_0_(C contains j) q_(C\{j}),
    S_j=A choice_0 (x_j choice_1 Q).                      (4)

If there is no clause avoiding j, omit A and its outer gate. Every
j-containing clause has a nonempty residual: a clause {j} would contradict
the antichain property with C_1. Equation (3), followed by the untouched
outer context A when present, proves S_j<=F_Ccal.

This inclusion is strict. Choose a third owner k and use the valuation

    x_i={k};
    x_l={0} for l in C_1\{j};
    x_l={1} for l outside C_1 union C_2;
    x_l={0,1} at every remaining position, including j.   (5)

These cases are disjoint because i lies in C_2\C_1. No original clause
is the 0 singleton: a clause whose inputs were all 0 would lie properly
inside C_1. The clause C_2 has no 1-singleton input and contains x_i={k},
so its value contains k. The outer 0-fold has no absorber and F_Ccal
therefore contains k.

In Q, however, the residual C_1\{j} is the 0 singleton, so Q={0}.
The factored inner term x_j choice_1 Q is {0,1}. Every clause avoiding
j meets V\(C_1 union C_2); otherwise it would be contained in U,
contrary to the elimination failure. Such a clause is absorbed to {1}.
Thus A, when present, is {1}, and S_j at (5) is {0,1}, omitting k.
This contradicts global minimality.

Hence the nonempty antichain Ccal satisfies cocircuit elimination, so
it is a finite matroid's cocircuit family. Its coverage of V excludes
loops. This proves the converse.

## Redundant clauses and the complete CNF classification

The prime-clutter reduction always satisfies

    F_Dcal <= F_Ccal.                                    (6)

Indeed, if any original clause has value {0}, its variables are all
0-singletons. It contains a minimal clause with the same value {0}, so
both outer folds return {0}. Otherwise every clause avoids the outer
absorber and each fold is the union of its clause values; the union over
the subfamily Dcal is contained in the union over Ccal.

If F_Ccal is globally minimal, (6) is equality. The minimal clauses
must still cover V. Every occurring variable of a primitive core word
is essential for K>=3, whereas a variable outside the union of Dcal is
ignored by F_Dcal. Thus equality and the original full-support assumption
force full support of Dcal. The clutter converse now makes Dcal the
cocircuits of a loopless matroid M.

There is also an exact equality criterion for (6), independent of matroids:

    F_Ccal=F_Dcal iff every C in Ccal is the union of
        the minimal clauses D contained in C.             (7)

For a source j, on the usual source probe with rival atomic sets E_0,E_1,
the two factors of any two-owner CNF are

    G_0(E_0)=NOT exists C in Ccal with C subseteq E_0;
    G_(j,1)(E_1)=exists C in Ccal with j in C and
                         C intersect E_1=empty.          (8)

At observer k use each factor whose owner differs from k. The outer
0-factor is independent of the marked clause, since a j-containing clause
cannot be all 0 when the source supplies k!=0. The inner 1-factor is the
disjunction over its j-containing clauses. This proves (8) by the same
occurrence calculation as for the matroid CNF.

The 0-factor is unchanged on passing to minimal clauses, because every
clause contains a minimal one. If the union property in (7) holds, every
j-containing clause disjoint from E_1 contains a minimal j-containing
clause disjoint from E_1. Thus the 1-factors also agree, and source
reconstruction proves equality of the operations.

Conversely suppose some C contains j not covered by a minimal clause
inside C. Choose a third observer k, give j the menu {k}, give exactly
V\C the 1 singleton, and give every other passive variable the ambiguous
menu I\{k}. There are no 0-singleton inputs. The clause C supplies k
in F_Ccal. Every minimal clause containing j meets V\C and is absorbed
to {1}, so F_Dcal omits k. This proves strictness and hence (7).

For the matroid M, a set C is a union of its contained cocircuits exactly
when V\C is a flat. By the cocircuit/closure criterion, an element j in C
belongs to a cocircuit contained in C exactly when j is outside cl(V\C).
Requiring this for every j in C is precisely cl(V\C)=V\C.

We therefore obtain the full classification:

**CNF classification theorem.** The full-support word F_Ccal is globally
minimal if and only if its minimal clause clutter Dcal is the cocircuit
family of a loopless matroid M and every clause in Ccal is the complement
of a flat of M. In that case F_Ccal=F_M.

Necessity follows from (6), the clutter converse, and (7). Conversely
these conditions give F_Ccal=F_Dcal=F_M, which is globally minimal by
the matroid construction.

## Every chosen matroid source has a linear realizer

Let M be loopless and fix j in V. There is a word realizing F_M in which
j occurs exactly once.

Rank one has the sole cocircuit V, so its canonical CNF is already the
single choice_1 clause on V. The one-variable case is projection. If j
is a coloop and there are other variables, {j} is its only containing
cocircuit and

    F_M=x_j choice_0 F_(M\j).                            (9)

The deletion matroid is loopless on a nonempty set, so this is a genuine
constant-free word linear in j.

In the remaining case the rank is at least two and j is not a coloop.
There is a cocircuit containing j by looplessness, no such cocircuit
is {j}, and there is a cocircuit avoiding j: extend j to a basis, remove
a different basis element, and take the complement of the resulting
hyperplane. Thus both A and Q in (4) are nonempty folds. Apply (4) to
the canonical cocircuit CNF. Factoring gives S_j<=F_M, and global
minimality forces S_j=F_M. Its only j occurrence is the displayed x_j.

Moreover this occurrence has exactly the canonical factors

    B_(j,0)(E_0) iff V\E_0 spans M;
    B_(j,1)(E_1) iff j notin cl(E_1);
    B_(j,r)=true for r notin {0,1}.                        (10)

For the 0-factor, the only outer sibling is A. Its 0-profile says that
some j-avoiding cocircuit is contained in E_0. Since j is excluded from
E_0, this is equivalent to some arbitrary cocircuit being contained in
E_0. Negating gives the spanning condition in (10).

For the 1-factor, Q's 1-profile says that E_1 meets C\{j} for every
cocircuit C containing j. Negating says that some such cocircuit misses
E_1, equivalently j is outside cl(E_1). The rank-one and coloop formulas
give these same factors directly. No other owner appears on the marked
path.

Pure-owner source probes bound every actual source-j occurrence factor
by (10), while this linear realizer attains the whole vector at once.
Thus (10) is the unique greatest actual full type at j. This strengthens
the cocircuit-CNF free coefficient calculation: its two canonical factors
can be placed at one single occurrence, rather than merely recovered as
an OR of separate occurrence contributions.

The choice of linear source can vary between these realizers. The theorem
does not claim that one word uses every variable once: the exact read-once
boundary remains the rank-one direct-sum classification in the matroid
note. It classifies two-owner CNFs and their minimal operations, not the
full mixed-owner guard problem or all exact occurrence types below (10).

## Both prime Boolean normal forms are minimal exactly for thresholds

Let f be a nonconstant monotone Boolean function on its finite nonempty
full essential support V. Interpret Boolean AND by choice_0 and Boolean
OR by choice_1. Its prime CNF and prime DNF are then two actual core
words. Both have owner-1 profile f, owner-0 profile its Boolean dual,
and unanimity profiles at every other owner. Full essential support
ensures every variable occurs in each normal form.

**Theorem.** The prime CNF and prime DNF operations are both globally
minimal if and only if f is a uniform threshold

    f(E)=true iff |E|>=rho, for some 1<=rho<=|V|.          (11)

Suppose first that the prime CNF is globally minimal. Its clauses are
a full-support clutter, so the classification above makes them the
cocircuits of a loopless matroid M. The function f is precisely spanning
in M; its minimal true sets, hence its prime DNF monomials, are M's
bases. Write F_M for the canonical CNF and G_M for this basis DNF.

Their profiles are identical. The matroid theorem identifies F_M with
the closed positive-profile lower envelope, so

    F_M <= G_M.                                         (12)

If M is nonuniform of rank rho, choose a dependent rho-element set and
a circuit D inside it. Then |D|<=rho. Choose e in D and an observer k
different from 0 and 1. At the valuation

    x_e={k};
    x_l={1} for l in L=D\{e};
    x_l=I\{k} for every remaining l,                     (13)

there are no 0-singleton inputs. The set L is independent of size at
most rho-1 and is nonspanning. But e belongs to cl(L). The matroid source
formula therefore makes F_M omit k: e is its only k-containing input,
and it lies in the closure of the 1-singleton positions.

Looplessness gives a basis containing e. Its DNF monomial retains k,
since none of its inputs is the absorbing 0 singleton. No DNF monomial
is the 1 singleton, because that would be a basis contained in the
nonspanning set L. The outer choice_1 fold therefore takes union and
retains k. Thus (12) is strict for every nonuniform M. In particular,
G_M cannot be globally minimal.

Consequently minimality of both normal forms forces M uniform, giving
(11). Conversely, for the uniform rank-rho matroid, the prime CNF clauses
are all (|V|-rho+1)-subsets and the prime DNF monomials are all rho-subsets.
The former are its cocircuits. After interchanging owners 0 and 1, the
latter are the cocircuits of the uniform rank-(|V|-rho+1) matroid. The
matroid minimality theorem, symmetric in the two distinguished owners,
therefore makes both operations globally minimal. Equation (12) then
forces their equality.

Both normal forms consequently realize the same tight quota operation
with deficits

    d_0=rho-1,   d_1=|V|-rho,   d_r=0 for r notin {0,1}.

This includes rank one, full rank, and the one-variable case. For every
nonuniform loopless matroid, in contrast, its prime basis DNF is strictly
above its globally minimal cocircuit CNF, with (13) an explicit separating
valuation. The corollary concerns these canonical prime normal forms;
it makes no claim about arbitrary Boolean-equivalent core words.
