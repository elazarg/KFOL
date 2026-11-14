# Spines over a fixed helper alphabet

Written proofs in
[appendix-core-spine-blocks.tex](../../../sections/appendix-core-spine-blocks.tex),
`core:thm:spine-block-normal-form`, `core:cor:spine-permutation-safety`,
and `core:prop:spine-quadratic-alphabet`. No new Lean claims.

A letter e=(r,H) means append the X-free helper H by owner-r choice.
Fix a finite used alphabet of m such letters, and order it f1,...,fm by
last occurrence in a word u.

## Least and greatest contexts for a last-occurrence order

The permutation P=f1...fm is POINTWISE BELOW u, while the full triangular
word

    T=(fm...f1)(fm...f2)...(fm)

is POINTWISE ABOVE it. All three have the same singleton-output tests
and, for core helpers, the same exact full marked type.

At each valuation an elementary map is either a constant reset (helper
equals the owner's atom) or monotone and extensive. Deleting a nonfinal
copy can therefore only decrease the context: an extensive step enlarges
the prefix, and a reset is made irrelevant by its later identical copy.
On singleton bits each letter acts as identity or a Boolean constant,
so deleting a nonfinal copy preserves every such test exactly.

In particular a safe witness over a specified alphabet exists iff a
PERMUTATION of that alphabet is safe. Repetition is unnecessary for safe
attainment, even when it changes the exact context value. Full marked type
depends only on the used letters, since repeated profile filters are
idempotent.

## Exact triangular compression

Cut the word into blocks ending at the last fi. Block i uses only
fi,...,fm and ends in fi. Its internal repetitions and order do not affect
the unary context, provided fi remains last. Thus keeping one copy per
block gives an equivalent subword of length <=m(m+1)/2.

The reason is uniform over all passive inputs. After the last resetting
block h, the state is its reset owner p. The first later block beta
containing a letter that does not fix p makes the state ambiguous.
The output is then p union ALL helper menus whose last index is >=beta.
Each such last occurrence is at or after that break. Earlier-block helpers
were discarded at the reset or ignored while the state was p.

With no reset the same statement applies to an atomic input; ambiguous
inputs give full union with every helper. These observations also prove
that filling every block with all its permitted letters gives the greatest
triangular context above.

## A closed safety test for a fixed order

For a permutation, let h be the last resetting index at a passive valuation.
If there is none, all helper menus must be contained in C for safety below
C union X. Necessity uses X=N_k for any forbidden k; K>=3 is essential here.

Otherwise p=owner(f_h) must belong to C. For every k outside C let ell_k
be the last index carrying k, or zero. Every letter strictly after h and
at or before ell_k must fix atom p: its owner is p or its helper is {p}.
This excludes exactly a break before the final forbidden contribution.

The test uses only the helper data and a finite last-occurrence order.
Selecting an adequate helper library from arbitrary joint guards remains
the missing step; this is not a full intrinsic guard criterion.

## Quadratic compression is optimal in order

Take s a-owned variable helpers x_i and t b-owned variable helpers y_j,
with a,b,c distinct. The word

    (y1...yt)x1 (y1...yt)x2 ... (y1...yt)xs (y1...yt)

has minimum length st+s+t among equivalent words over THIS SAME elementary
alphabet. Reset tests force all last x_i before all last y_j. Break/carrier
tests force increasing last x_i and a y_j in every consecutive gap, with
another before the first and after the last. These s+1 disjoint gaps require
t(s+1) y-occurrences, plus s x-occurrences. Balanced s,t give
floor(m^2/4)+m, matching the quadratic order of the upper bound.

The alphabet restriction matters: replacing a repeated block by a compound
helper changes the representation problem.
