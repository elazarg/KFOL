# A closed criterion for one complete source family

Written mathematical proofs, without new Lean claims. The report statements
are `core:thm:source-completion`, `core:cor:colored-cofactor-dependence`, and
`core:cor:source-box-rank` in
[the report source](../../../sections/appendix-core-source-completions.tex).
These classify one complete source family; joint realization across sources
is still the full target.

Fix K>=3, a distinguished input x, and a nonempty finite passive set W.
Let D consist of tuples E=(E_r)_r of pairwise-disjoint subsets of W with
at least one E_k empty. Order them by componentwise inclusion. The facet
D_k has E_k empty. It is exactly the canonical probe domain for observer
k, with x={k}, inputs in E_r equal to {r}, and uncolored inputs N_k.

## Two closed conditions

A complete source family (c_k)_k has a core realizer exactly when

1. Every c_k is antitone on D_k.
2. c_k(E)=c_l(E) whenever E belongs to both facets.

Agreement glues them into one P:D->Bool. For E<=E', choose an owner
missing from E'; both tuples lie in that facet, proving global
antitonicity. Either P is false everywhere or P(empty)=true.

Necessity follows from occurrence factors. At each x-occurrence o the
owner factors B_(o,r) are antitone and normalized at empty. Its observer-k
contribution is the product over owners other than k. On D_k the omitted
factor has empty argument and is true, so every observer sees the same
full product. Disjunction over occurrences gives P.

## Greatest core completion

Put U(w)=union_(i in W) w_i and E_r(w)={i:w_i={r}}. Extend P by false
outside D; those patterns already have U=I. Then

    F_P(X,w) = U(w) union (X if P(E(w)) else empty)

is core. For each positive E start one spine at x and attach at owner r
the r-fold of W\E_r, omitting an empty complement. Its factor is
[E'_r subseteq E_r], with NONSTRICT inclusion. Each passive contribution
lies in U. A winner k outside U has E'_k empty, so its source factor is
the complete product, independent of which missing observer was chosen.
Union U with these spines to realize F_P.

Every core realization of the same source family lies below F_P: any
winner outside U must come from x and its source coefficient is P.
Therefore F_P is the unique greatest CORE completion. Greatestness is
not asserted for arbitrary functions sharing the sampled probes.
The core operations retaining every passive input are exactly these F_P.
For any original core F, its completion at source x is simply F union U.

## Exact minimum source reuse

An owner box is the product of normalized antitone predicates B_r(E_r),
one per owner. Let b(P) be the fewest such boxes whose disjunction equals
P ON D; let b(false)=0. The least number of x-occurrences among ALL core
words with this source family, with union named, is exactly b(P).

Every occurrence gives one box, proving the lower bound. Conversely,
for B_r not identically true, its complement is a normalized nonzero
monotone profile. Synthesize that r-profile with unanimity at the other
owners and attach the resulting x-free helper at an r-gate to one x leaf.
Skip identically-true factors. The spine has exactly that box; adding U
absorbs every passive side effect. A minimum cover therefore gives F_P
with exactly b(P) copies of x.

A primitive realization uses at most K*b(P) copies. For a finite union
of arbitrary arguments, fold the arguments once at each owner r. The
result A_r is r or their ambiguous union S. A read-once combining tree
whose owner avoids its leaf-child labels computes union of the A_r.
If none equals S, all K owners already occur in the arguments, so S=I.
Thus each original argument is used exactly K times. Singleton S follows
by idempotence.

## The semantic meaning of the source predicate

For any core F with source predicate P, fix the inputs of E_r to r and
leave the uncolored inputs and x arbitrary. Then

    P(E)=false iff this whole cofactor is independent of x.

If P(E) is true, the canonical missing-owner k probe distinguishes
x={k} from x=N_k. If it is false, every x-occurrence has a foreign
absorbing ancestor whose singleton sibling is forced using only the
fixed colored inputs. Its profile remains true for all assignments of
the unfixed inputs. Maximal such constant subwords cover every x leaf;
collapsing them removes x throughout the cofactor.

This extends the monochromatic dependence-closure interpretation to all
proper partial owner-colorings. General functional-dependence laws alone
are insufficient: the Gray obstruction itself has these proper colored
cofactor dependencies, yet is noncore.

## Remaining joint problem

Each source now has a canonical greatest completion and a closed marginal
criterion. The issue is compatibility of these completions. Their ordinary
pointwise intersection need not be source-reconstructing; it can retain a
winner merely because that winner appears at several inputs. Even when
the sourcewise reconstructed candidate is nonempty and its proper source
families have common core realizers, the Gray obstructions exclude a
global realization. The new criterion settles the complete one-source
problem, not this final joint step.
