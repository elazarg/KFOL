# Characterization target and the nonfinite-relatedness theorem

The original target is a short structural characterization of jointly
realizable canonical source guards, comparable to the monotonicity and
common-source conditions for singleton profiles. Row deletion is exact
recursive recognition; it does not replace recursion by closed conditions.

The concrete finite-relatedness question is now settled negatively.
Fix any finite role set K≥3. For every m≥0, there is an operation

    F : A_K^(m+3) → A_K

such that every m valuations have a common core-term interpolant, yet F is
not a core term operation. K stays fixed as m grows. The proof treats all
ambient role sets with three distinguished owners and proves each patch on
every valuation, including ambiguous values and additional owners.

The complete statements are `Paper.core_not_finitely_related` and
`Paper.core_no_finite_relation_basis`. The latter says explicitly that, for
any finite family of core-invariant relations, some nonterm operation
preserves every member of the family. `Core/RelationalInterpolation`
identifies m-point interpolation with preservation of every m-ary invariant
relation; `Core/PatchInterpolation` proves its antitonicity in m.

## The cyclic construction

Take n=m+3 inputs with cyclic successor i↦i+1, and distinct owners a,b,c.
Normally F returns the union of all inputs. On the region with input i
exactly {c}, input i+1 neither {b} nor {c}, and all other inputs {b}, it
returns {b,c}. The n exceptional regions are disjoint.

Deleting any one exceptional region gives a core operation. The proof cuts
the cycle into a path and separates Boolean intervals by prefix disjunctions,
nonadjacent-pair conjunctions and cardinality thresholds. Greatest singleton
profile completions turn these Boolean separators into actual core terms,
whose finite union is exactly the deletion patch on every input.
Each valuation disagrees with at most one deletion patch. Any m valuations
therefore share a patch, since n>m.

The full cycle violates cyclic persistence. At its forward rows, with c at i,
a at i+1 and b elsewhere, F omits a; at the opposite rows it includes a.
Every core term that includes a at an opposite row must include a at some
forward row. In the observer-a quotient, core terms expand into finite unions
of lattice polynomials on b<a<c. Each polynomial induces a monotone Boolean
function. Vanishing derivatives on all forward edges force vanishing on the
opposite edges by finite cyclic propagation.

Definitions are in `Definitions/CoreCrown`; the proof runs through
`CrownBoolean`, `CrownPatch`, `CrownBasePatch`, `CrownRotation`, `CrownPatches`,
`CyclicPersistence` and `CrownObstruction`. `CrownFullSyntax` also proves the
counterexample idempotent, so idempotent extraction rules out full-language
realizations. Thus the expansions by constants and role switches are not
finitely related either. `FiniteRelationObstruction` takes
the maximum arity of an arbitrary finite relation family, including empty
families and nullary relations. All proof closures use only propext,
Classical.choice and Quot.sound. The sole finite observer-table check uses
kernel `decide`, with a general induction supplying the all-term theorem.

Nonfinite relatedness excludes characterization by a fixed finite family of
invariant relations. It does not exclude every possible short structural law
with unbounded quantification.
