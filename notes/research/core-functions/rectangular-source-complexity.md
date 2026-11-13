# Source rectangles and exact exponential tree complexity

Written mathematics, not a new Lean claim. The complete statements and
proofs are in `sections/appendix-core-rectangles.tex`.

This settles the proposed uniform bound on copies of a chosen source,
even for subordinate witnesses of a single positive probe. It does not
give the remaining intrinsic criterion for joint guard realizability.

## The intrinsic lower bound

Fix distinct owners A,B,C and N=I\{B}. Give the marked source j the
singleton B. On disjoint passive blocks, independently vary A-versus-N
and C-versus-N; keep all other passive variables N. Each occurrence of j
contributes a rectangle in these two axes: its A-owned path filters
depend only on the A-set, and its C-owned filters only on the C-set.
Every other foreign filter is open. This holds even with named union
and additional owners.

The source matrix is therefore covered by at most as many positive
rectangles as there are j occurrences. In particular, m positive probes
with a negative cross between each two require at least m copies.
Prime-guard count alone would not prove this: one occurrence can have
many prime guards inside its individual owner factors.

## A robust exact family

Use distinct variables x,a_0,b_0,...,a_(d-1),b_(d-1) and set

    T_0=x;
    T_(i+1)=(a_i choice_A T_i) choice_B (T_i choice_C b_i).

The circuit has 3d choice gates and 2d+1 input nodes. Its unfolding
has 2^d copies of x, and 2^(d-i-1) copies of each a_i,b_i.

**Theorem.** Every constant-free choice/union word S<=T_d has at least
these occurrence counts. Thus its exact minimum leaf count is

    3*2^d-2,

attained by T_d itself. In particular, every core minorant already
has exponential tree size; no global-minimality assertion is needed.

The proof has two ingredients.

1. Every minorant retains the exact B-profile

       Phi_B(E) = [x in E] AND ALL_i [a_i in E OR b_i in E].

   Positive bits persist by nonemptiness. The A-positive coalition
   {x,b_all} and C-positive coalition {x,a_all} force x in every
   B-winning coalition. Any extra B-coalition E missing a pair is
   ruled out by one bounded rainbow: set x=B, a_i=C inside E and
   A outside E, b_i=A inside E and C outside E. The missing pair
   makes T_d=AC, but the three positive coalitions force a winner
   outside AC.

2. A true/false B-profile separator H,H\{j} forces B at a source-j
   probe whenever every foreign atomic set misses H. Descend to
   a separating child: at foreign gates, the sibling's positive
   B-profile excludes its absorbing singleton by common-source
   intersection. The separating leaf must be j.

For source x the matrix is disjointness:

    C_(x,B)(U,W) = [U intersect W is empty].

The complementary pairs (S,S-complement) are forced positive for
every minorant by ingredient 2. Crossed intersecting pairs are negative
by the upper bound T_d. They form a 2^d-element fooling set.

For a_i, fix every input of T_i and b_i to N, put a_i=B, and vary
the higher pairs. The value of T_(i+1) is I. Choose H containing
x, one variable per lower pair, a_i but not b_i, and the neutral
partner of every higher pair. The separator forces all 2^(d-i-1)
complementary probes. The same argument applies to b_i. Sum the
occurrence bounds to obtain the exact leaf count.

The source-x coefficient is unconditional at observers A,C. At every
other observer k it is the product

    ALL_i (NOT a_i,A OR NOT b_i,C).

## Relation to the reset circuit bound

The existing reset construction has the same disjointness matrix after
fixing its root input z=N and restricting its pair inputs p_i to A/N,
n_i to C/N. Hence its 2^d marked-copy lower bound holds even for
equivalent words using arbitrary owned choices and union, rather than
reset alone. This is `core:cor:reset-ambient-tree-bound`; it is a written
strengthening of the kernel-checked reset-only result.

## Consequence for the characterization route

For any fixed K>=3 and any proposed source-copy bound b, choose d with
2^d>b. Every subordinate witness for T_d already exceeds that bound,
including witnesses of one fixed positive source observation. A union
of words each satisfying that fixed marked-source bound cannot recover
T_d either, since every summand would be a minorant. The lower bound
concerns one chosen source, not a requirement that some input in each
word have bounded multiplicity.

The marked-source CNF and shared circuit remain linear in d. This theorem
therefore rules out bounded-copy word normal forms, not short intrinsic
conditions on the guards.
