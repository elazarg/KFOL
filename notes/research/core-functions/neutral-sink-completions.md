# Least sink completions and exact marked-source linearization

Written mathematical proofs, not Lean claims. The report statements are
`core:prop:sink-completions`, `core:lem:neutral-marked-linearization`,
`core:cor:interval-linear-cover`, and
`core:cor:sink-completion-obstruction` in
[appendix-core-neutral-completions.tex](../../../sections/appendix-core-neutral-completions.tex).
The full cyclic guard-characterization problem remains open.

## A commuting family of closure operators

For source X define S_X(T)=T union partial_X T, with winnerwise neutral
deletion partial_X. This is the least core majorant making X a source sink:
no other complete source predicate depends on X's passive status.
It preserves X's own complete source predicate, and restricts every other
predicate to neutral status at X. A sink G contains partial_X G; therefore
G>=T implies G>=T+partial_X T, proving leastness.

These operators are extensive, monotone, idempotent, and commute. More
explicitly,

    S_A(T) = UNION_(B subseteq A) partial_B T,
    pi_i^(S_A T)(E)=pi_i^T(E with all A-statuses erased).

The own-i status is immaterial in the second formula. Neutral deletion
commutes and distributes over union. Completing all sources gives input
union on the essential support, since the one-input residuals are exactly
their projections. The closures can remove further dependencies, but add
no new ones.

For every nonempty source-reconstructing operation,

    T = INTERSECTION_X S_X(T).

If k is absent, choose an input X containing k. Replacing it by N_k
changes no foreign-k atomic flag and removes only that input's k-source,
so partial_X T still omits k. If no input contains k, provenance applies.

## Universal occurrence-preserving linearization

For ANY marked occurrence o of X in a core word T, there is a primitive
X-linear spine S_o with exactly the same full owner-factor type and

    S_o <= T union partial_X T.

Every helper is an X-free neutral residue. Follow the marked path. At an
r-owned node, skip its sibling if the sibling's deleted r-profile is zero;
otherwise attach that sibling's neutral residue by choice_r. Nonzero
deleted-profile preservation makes each marked factor exact. The new word
uses X exactly once.

Safety is a direct induction using the four-row residual compiler. Write
T1 for the marked child, T2 for its sibling, C1,C2 for their residues, and
a,b for nonzero deleted r-profiles. The induction invariant is
S<=T1+C1. Also T1\C1 is contained in X.

- If b=0, skipping is safe: the parent residue contains C1. Any winner
  lost by the real root is foreign to r and must come from X, while
  T2=r with zero deleted profile forces X=r, a contradiction.
- If b=1 and C2=r, both the new spine and parent residue are r.
- If b=1, C2!=r, a=1, C1=r, preservation gives T1=S=r.
- In every other case the parent residue is C1+C2. Any alleged new
  winner outside the parent and residue lies in T1\C1, hence in X;
  the real sibling can kill it only by being r. Since C2!=r this forces
  X=r, again a contradiction for a foreign winner.

Zero residues use the discard rules. In particular an attached sibling
is always nonempty, and C1=0 fits the final union case.

## Arbitrary one-source intervals admit linear covers

For every actual core interval C<=F(X,v)<=C+X, neutral deletion gives
partial_X F=C. Thus every marked spine is already <=F. Union with C
recovers F: a winner outside C must come from an X-occurrence, and that
occurrence's preserved factors supply it in its compiled spine.

This holds for arbitrary cyclic C, not just the acyclic or profile-maximum
baselines. It preserves every actual full occurrence type exactly.
For arbitrary T, the same spines cover its X-contributions; all other
source contributions lie in partial_X T, since erasing X's foreign atomic
flags only increases their coefficients. Their union is S_X(T).

The neutral completion is essential. An arbitrary core T can fail to have
a one-X minorant at one of its positive observations; adding partial_X T
provides the contributions needed by the linearized helpers. The F5 and
full-support branching examples therefore keep their original force.

## Canonical sink completions still do not glue

For the Gray noncore operation F_d, every proper neutral residual is
input union. Hence each S_i(F_d)=F_d+U_except_i is its greatest single-source
completion and is core. All other sources are unconditional, so it has
a source DAG. Completing two or more sources gives full input union.
Every nonempty simultaneous sink completion is therefore core, all the
completions commute, and their pointwise intersection is still noncore F_d.

The source graph of F_d is complete. Each input i is the unique free
coordinate of a Gray region. Put i=a and all other inputs at that region's
b/c endpoints; pi_i=0. Replacing any other input j by N_a creates two
non-b/c coordinates, avoiding every region and making pi_i=1. Thus j->i
for every j!=i. The obstruction is a single feedback component.

Whole-block intervals also contain the full difficulty. For any operation
F on old inputs, adjoin a retained projection Z and put H=Z+F. Then
H is core iff F is core: one direction is union, the other is neutral
deletion of Z. Applying this to Gray and its deletion patches gives core
extensions in [Z,Z+U_old] with a noncore pairwise intersection and arbitrary
finite interpolation thresholds. The one-source distributive-lattice
theorem cannot simply be transferred to an entire feedback block.

## What this leaves to characterize

The interval theorem reduces witnesses to one marked source and X-free
helpers, even when the passive core has cycles. It does not yet describe
which safe helper profiles exist directly from arbitrary target guards.
Canonical least sink envelopes have exact overlap compatibility but can
still fail to assemble. A full characterization must retain the joint
feedback information lost by these commuting completions.
