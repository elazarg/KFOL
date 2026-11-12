# Global characterization: structural reductions and obstructions

The active target is in [target.md](target.md). This note separates proved
library results from research arguments that have not been formalized.

## Proved in Lean

- `Core/AtomicObserver`: exact closed reachability criterion for one observer
  on atomic interval inputs, including ambient role sets larger than three
  and the nullary boundary.
- `Core/Bichain` and `Core/BichainFiber`: the four-element observer quotient is
  the union-expanded bichain; its pure Boolean-projection fiber is the whole
  expanded clone at one lower arity plus one zero trace, with uniqueness.
- `Core/AtomicAmalgamation`: three individually core-realizable complete views
  with common unanimity singleton profiles need not have a common core term.
  Three atomic rows suffice to exclude one. The relation certificate is closed
  under the actual owned choices; no clone-enumeration assumption is used.
- `Core/Hypergraphs`: closed boundary/no-trap axioms present every invariant
  relation, even empty relations and empty coordinate sets. Universal
  preservation and positive/negative guard persistence give exact global
  obstruction criteria. Auxiliary clutters are still quantified over.

The bichain is the algebra in Harding, Walker and Walker, *Type-2 Fuzzy Sets
and Bichains* (2013), Definition 5 and Figure 1. Its older normal-form results
for identities do not specify which formal normal forms arise from terms;
they do not supply the missing guard characterization.

## Union polarization does not complete the scalar criterion

The following uniform mathematical counterexample has a written proof below,
but is not yet a Lean theorem or a report claim. Ternary experimental agreement
was misleading and must not be extrapolated.

Let B={b,c,N,P}, with the two bichain operations and observer union. For a
monotone Boolean function f, interpret b,c as fixed bits 0,1 and N,P as free
coordinates, obtaining a Boolean subcube Q(v). Define D_f(v) as follows:
return b or c when f is constantly 0 or 1 on Q(v); otherwise return P when
some P-marked coordinate is essential in f restricted to Q(v), and N otherwise.
An essential coordinate has a pair of vertices differing only there on which
f changes.

Replace each input by the observer union of k fresh atomic inputs from
{b,c,P}. Every positive atomic interval of the resulting P trace has a monotone
Boolean separator that is constant on every zero interval, for every k.
Indeed, choose an essential marked coordinate j and a Boolean edge witnessing
it. In each block choose a nonconstant cardinality threshold theta_i. At a
fixed mixed block its value can be either witness bit; at a marked block its
lower and upper values bracket that bit; at block j they are 0 and 1. Then
psi=f(theta_1,...,theta_n) separates the positive interval. Wherever psi
changes, a coordinatewise Boolean path has an f-changing edge in a strictly
increasing block. That block is P-marked and essential in the corresponding
cofactor. Hence every psi-positive interval is D_f-positive. The atomic
criterion therefore accepts every such polarization.

Nevertheless f(a,b,c,d)=ab OR ac OR bd gives a nonterm D_f. For a pure
meet/join formula with Boolean function g, endpoints are determined by the
lower/upper Boolean corners. Every essential marked coordinate forces P,
by its Boolean edge on {b,P,c} and passive monotonicity. Suppose a smallest
formula for D_f has a join root with children g,h<=f. A child owning any
minimal true assignment must own all three, by these implications:

| Ownership implication | Partial input (a,b,c,d) | Essential marked coordinate if it fails |
| --- | --- | --- |
| ac -> ab | (N,c,P,b) | c |
| bd -> ab | (c,N,b,P) | d |
| ab -> ac | (N,P,c,b) | b |
| ab -> bd | (P,N,b,c) | a |

In each row f depends only on the N-marked coordinate, so D_f=N. An
ownership failure gives P in that child; its sibling cannot give c because
the lower Boolean corner has f=0. Thus the join would give P, a contradiction.
A child owns some minterm, hence all three, so its Boolean function is f.
It must itself equal D_f: essential marked coordinates force every desired P,
and unwanted P would propagate through the root. This contradicts minimality.
For a meet root use Boolean duality: swap b,c and meet,join, fixing N,P;
the dual is ab OR ad OR bc, the same function with c,d exchanged.

A full term expands into a nonempty observer union of pure formulas. Stable
Boolean outputs force each summand's Boolean function to be f. P is absorbing
under union, so each summand has no additional P, while essentiality forces all
required P. Each would realize D_f, contradicting the pure case. Thus even all
union-polarized atomic tests miss a nonterm.

## Other routes that do not suffice

Independent observer criteria fail by the formal amalgamation example.
Completing singleton profiles and taking unions of their greatest envelopes
also loses term functions below those envelopes. Tracking surviving Boolean
DNF monomials and CNF clauses independently loses the requirement that the
same repeated occurrence survive both.

A simple coherence schema records only the set of states occurring in a tuple:
R_Gamma consists of tuples whose nonempty value-set belongs to Gamma. Requiring
invariance under the three operations at every relation arity still misses the
cyclic nonterm operations. Nonuniversal such schemas either allow no P, where
the cyclic operation acts as union, or forbid b and c in one coherent set,
where a single deletion patch agrees on every column. Adding passive guard
monotonicity does not remove that defect. A richer relation schema needs the
colored incidences retained by the proved clutter presentation.

A canonical occurrence graph cannot simply retain maximal source types.
For X star_r (X star_s Y), r!=s, the two X occurrences have distinct filter
roles, including a dominated type. Conversely, taking all safe types introduces
unrealizable unused occurrences even for a projection. Choosing witnesses can
create new maximal cliques and new guards, so this has not eliminated the
compatibility problem.
