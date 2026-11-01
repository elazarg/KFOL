# Operators from the archived K-FOG manuscript

The manuscript is in git history: `git show 3ab7496^:archive/manuscript-2026-10-28/algebra.tex`,
with related material in `extensions.tex`, `solutions.tex`, and `other/`.

Nothing here is claimed in the paper. Run `python3 checks/probe_kfog_operators.py`
to reproduce the tests; it takes a few minutes and is not part of `make check`.

Labels: **tested** means exact or brute-force computation at the stated sizes,
**hand** means a sketch not written up, and **lead** means an idea. No prior-art
search has been done for anything here, so none of it should be called new yet.

## 1. One rule covers several kinds of owner

K-FOG's terminal is a K-tuple of objectives, so a play can have several winners or
none. The paper keeps only its one-hot fragment. Let an owner prefer the outcomes
in a set U and be otherwise indifferent. For nonempty sets V, W of outcomes:

    V *_U W = (V ∪ W) ∩ U   if V ⊆ U or W ⊆ U
            = V ∪ W         otherwise

**Tested:** this equals brute-force SPE, with whole-player deviations, on random
trees at K=2,3 with Boolean objectives, and with coalition owners on one-hot leaves.

| Outcomes | U | Gives |
|---|---|---|
| I (one winner) | {r} | the paper's star_r |
| I | empty, or all of I | union: the owner has no stake |
| I | a block B | a coalition owner, keeping who individually wins (section 3) |
| I | I − {r} | misère: "anyone but r", K-FOG's complement read on one-hot games |
| subsets of I | sets containing r | Boolean objectives |

### Two players stop being forcing

This is where K=2 fails to reduce to forcing. Public one-hot K=2 is strong Kleene
logic and does reduce (Appendix "Two players" of the paper). With Boolean objectives
it does not.

- `<ab> +_a <none>` has value {ab}: b surely wins, yet b cannot force a win.
- **Tested:** the leaves generate 12 of the 15 possible values. Distributivity fails
  on 192 of 1728 triples and absorption on 60 of 144 pairs. Seven values share the
  forcing vector (no, no).
- K-FOG's cross-diagonal product (Battleship) reaches this algebra even from zero-sum
  games. **Tested:** `<0>` and `<0> +_0 <1>` both have value {0}, but crossing with `<0>`
  gives {neither} and {neither, B}. So Zermelo values are not a congruence for it.

Question: what is the equational theory of this 12-element algebra? It is the smallest
case in which a non-forcing, two-player owned-choice algebra could have a clean basis.

## 2. Coalition quotients connect SPE winners and forcing

K-FOG's coalition forming relabels owners and leaves along a surjection of roles. With
one-hot leaves this is its OR aggregation. Its AND aggregation gives every block of
size at least two a stake it can never win.

Merging roles is not a function of winner sets. **Tested:** `<b> +_a <c>` and
`<b> +_d <c>` have the same value {b,c}, but merging a with b gives {A} and {A,C}. So
the paper's value is a congruence only for contexts that keep roles apart.

Merging does act on syntax, so `G ↦ (⟦G/π⟧)_π` is a homomorphism into a finite product
indexed by partitions of the roles. This is a single compositional semantics with:

- the finest partition giving SPE winners;
- the two-block partitions giving coalition forcing, by Zermelo at K=2. These values
  are the self-dual monotone functions (the free median algebra), as in the 2026-10-28
  assessment at `19812ec:notes/assessment.md`;
- **tested at K=3,4,5:** in every quotient, a value is the atom {B} exactly when
  coalition B can force a win.

**Tested**, by exact closure over partitions with at least two blocks:

| K | winners only | two-block only | both | all partitions |
|---|---|---|---|---|
| 3 | 7 | 4 | 7 | 7 |
| 4 | 15 | 12 | 68 | 500 |

K=3 is too small to show this: winners determine everything there, and every ambiguous
value forces majority. From K=4 all three layers carry information. Forcing does not
determine winners at any K≥3: the games D and T of Section 2 have the same forcing for
every coalition but values {a,b,c} and {a,c}. **Hand:** neutral union does not survive
merging. If two of its owners merge, idempotence reduces J to one owned choice.

Questions: the size at K=5, and which identities hold in every quotient.

## 3. Why two winners suffice in tests

Coalition-owned choice `S *_B T` on individual winners is a semilattice for every block B
(**tested** at K=3,4). It is not a term of the core when 2 ≤ |B| < K: **tested** by
exact binary clones of C, with 20, 37, 70 functions at K=3,4,5. The reason is that it
tests `S ⊆ B`, while owned choices test only `S = {r}`.

This suggests where the pair theorem comes from. For a family of blocks, let h be the
least size such that every input x and member i of x has a subset y of size at most h
containing i, with `y ⊆ B ⟺ x ⊆ B` for all B in the family. **Hand:** the shrinking
proof of the pair theorem then shows that inputs of size h suffice.

**Tested**, exact on all binary terms (K=5 is a partial closure, which still yields
real witnesses):

| Owner family | K | h | Sizes needed |
|---|---|---|---|
| singletons | 4 | 2 | 2 |
| singletons and ab | 4 | 2 | 2 |
| partition ab\|cd or ab\|c\|d | 4 | 2 | at most 2 |
| abc, abd | 4 | 3 | at most 2 on binary terms |
| all 3-sets | 4 | 4 | at most 2 on binary terms |
| acd, abd, abc, with union | 5 | 4 | 4 |

So h is an upper bound, and it is attained in the K=5 family. A witness there, with
`*0` for union, passes all pair tests and fails at x={a}, y={b,c,e}:

    (x *acd y) *0 (x *abd y) = ((x *0 y) *abd (x *acd y)) *acd (x *abd y)

On this reading, "two winners suffice" is a fact about owners being atoms. It survives
for a coalition structure given by a partition. Question: is h exact with more variables?

## 4. Smaller connections

- **Union is an outsider's choice.** K-FOG's structural players (clock, megaphone) own
  no objective. Give one a real choice and it is union: star_c on subsets of {a,b} is ∪.
  So neutral union J is three real owners simulating an outsider. K=2 has no outsider,
  which is why ∪ is not a term there, and a hidden move restores it through the round
  with matrix [[x,y],[y,x]]. (**Tested** in `checks/check_two_players.py` and this probe.)
- **Tensor versus leaky sequencing.** K-FOG proves that forcing ignores this difference
  for disjoint arenas. For SPE on disjoint roles, **tested:** both orders give the product
  of the values. For coupled games at K=2, sealed = union of the two serial orders (paper,
  two-player appendix). **Tested** at K=3 on all 81 2×2 rounds over leaves: sealed winners
  stay inside the union, strictly in 16 cases, e.g. [[a,b],[b,c]] has sealed {b,c} and
  serial {a,b,c}. Whether the inclusion survives deeper rounds is open.
- **Clock and megaphone.** A paper round is K-FOG's tensor followed by a megaphone. A
  secret retained across a boundary is a clock without the megaphone, the case for which
  the paper has no composition theorem.
- **Cheap talk.** K-FOG's outcome-insensitive binder is `G +_r G`. It is invisible to
  winner sets, by idempotence. It is exactly the paper's failure of idempotence on
  distribution sets: `(δa+δc)/2` in E(T +_b T).
- **Splice.** Gluing a shared move makes one decision serve several parents. That is the
  paper's uniform-copy observation (`game:prop:uniform-observation`), not independent
  copies. It differs from the shared circuits in the uncommitted circuit appendix, which
  share syntax only and still denote independent copies. **Hand.**

## 5. Tried, and not useful for this

- **Admissible strategies.** Requiring undominated play in each subgame removes D's oddity
  (b's win relied on a declining a chance), giving D={a,c}. **Tested:** this has a compositional
  rule on (winners, reachable, forcing), with no mismatch on 3453 random trees and none empty.
  But it does not restore distributivity: T becomes {a}, and 3505 of 18000 instances fail.
- **Implication projection.** Already flagged in the 2026-10-28 assessment: it can be true by
  falsifying the antecedent.
- **Redundancy, orbit-realizability, the relational-algebra reading, MPST translations.** These
  are forcing or protocol questions, and they add nothing to the winner algebra.
