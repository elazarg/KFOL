# Read-once core trees are least in their profile fibres

Mathematical proof, without new Lean claims. A read-once tree here uses
primitive owned choices and has distinct variables at distinct leaves.
Union is not a primitive node: its core implementation repeats variables.
The role set I is finite with K>=3.

## A closed lower envelope from positive profiles

For a profile tuple Phi and a valuation w, put

    W_k(w)={j:k in w_j},   E_r(w)={j:w_j={r}}.

Define R_Phi(w) to contain k when there are coalitions A_r, one per owner,
such that

    Phi_r(A_r)=true for every r;
    empty != C=intersection_r A_r subseteq W_k(w);
    E_r(w) intersect intersection_(s!=r) A_s = empty
        for every r!=k.                                      (1)

This is a closed condition on the given profiles and input menus. It
does not ask for a tree, a term, or a recursion. It need not be nonempty
for arbitrary profiles.

**Lower-bound lemma.** If a core operation S has every positive profile
bit in Phi, then R_Phi(w) is contained in S(w), for every w.

For k with a certificate (1), suppose S(w) omitted k. Apply the rainbow
one-bound theorem from [profile-bounds.md](profile-bounds.md), with all
owners demanded and allowed output U=I\{k}. Its projection alternative
would require j in C with w_j contained in U, impossible because every
j in C contains k. Its absorption alternative would require some r!=k
with E_r(w) meeting the intersection of the other coalitions, excluded
by (1). Thus no such bounded S exists. Only the positive profile demands
are used in this argument.

In fact this envelope is exact for positive-profile constraints. Assume the
top bits Phi_r(V) are true and at least one core operation retains all its
positive bits. Then

    R_Phi(w)=intersection {S(w): S core, Phi^S contains Phi}.

For the reverse inclusion, if no such S omits k, its positive profile
requirements are infeasible under the single output bound I\{k}. The
restricted Horn classification of bounded profile relations gives an
infeasible rainbow subpremise: at most one demanded bit per owner, possibly
no bits. Unary same-owner implications cannot require combining two
premises at one owner; a minimal forbidden positive conjunction is rainbow.
The rainbow one-bound criterion supplies the corresponding failure.

Add A_r=V for each missing owner; these are positive bits by assumption.
The common intersection C is unchanged and is nonempty, since some global
core operation satisfies all these positive demands. Failure of the
projection alternative says that every input in C contains k. For a
newly added r!=k, the intersection of the other coalitions is C, so it
contains no r-singleton input. Thus padding introduces no absorption
alternative. The failed budget condition is exactly certificate (1),
so k belongs to R_Phi(w).

## Exactness for a read-once tree

**Theorem.** If T is read-once, then

    T(w)=R_(Phi^T)(w) for every w.                           (2)

Consequently T is the pointwise least core operation in its complete
singleton-profile fibre. The comparison operation may repeat variables
and may use additional ambient variables. In fact, retaining all positive
profile bits of T already forces every winner of T.

It remains to prove T(w) is contained in the right side of (2); the reverse
inclusion is the lower-bound lemma. We prove the stronger certificate:
for every k in T(w), the coalitions in (1) can be chosen with

    A_r subseteq supp(T) for every r,
    intersection_r A_r={j} for some j with k in w_j.         (3)

Induct on T. At a leaf j use A_r={j} for every owner. It wins every required
profile test. The atomic exclusion in (1) holds because w_j contains k
and so cannot be the rival singleton {r}.

Suppose the root is owned by h. Choose a child L with k in L(w), and write
R for the other child. If h!=k, neither child output is {h}; otherwise the
root would be {h}. Choose p in R(w) with p!=h. If h=k, choose any p in
the nonempty R(w). Induction gives certificates A_r^L for (L,k) and
A_r^R for (R,p). Set

    A_h=A_h^L,
    A_r=A_r^L union A_r^R for r!=h.                         (4)

At owner h, the root's singleton profile is the OR of its child profiles,
so A_h is winning. At any other owner the root profile is AND, and the
union in (4) is winning in both children. Distinct leaf variables make
their supports disjoint. Since A_h lies entirely in L, intersecting all
coalitions gives the left certificate's singleton {j}, proving (3).

For r!=h,k, the presence of the A_h factor restricts the intersection
excluding r to L. The required atomic exclusion is exactly the left
certificate's exclusion. For r=h!=k, disjoint supports give

    intersection_(s!=h) (A_s^L union A_s^R)
      = intersection_(s!=h) A_s^L
           union intersection_(s!=h) A_s^R.

The two intersections are taken in their respective child supports. The
left one contains no h-singleton input because k!=h, and the right one
contains none because p!=h. This proves the remaining exclusion. There
is no exclusion to check for r=k. Thus (1) holds, completing the induction.

The proof is combinatorial. It needs no equilibrium existence theorem or
additional strategy semantics. Its crucial step is that intersections of
coalitions supported in disjoint leaf sets identify actual leaves. Repeated
labels can create a common variable by using different occurrences in the
different coalitions; the induction then loses (3).

The formula (1) is therefore an exact intrinsic description for this class,
and a sound lower bound in every profile fibre. It is not a replacement for
the full source-guard criterion: general core terms can have essential
overlapping input reuse, and their profiles alone need not determine their
ambiguous outputs.

## Read-once profiles are maximal admissible

If an admissible profile tuple Psi contains every positive bit of Phi^T
for read-once T, synthesize a core operation S with profiles Psi. The
theorem gives T(w) contained in S(w) at every input. At the usual r-profile
probe for a coalition A, a true Psi_r(A) makes S(w)={r}. Nonemptiness
therefore forces T(w)={r}, so Phi^T_r(A) was already true. Hence Psi=Phi^T.

More generally, when Phi is any maximal admissible tuple, its positive
extensions among core operations are precisely its complete profile fibre.
The exact positive-envelope result identifies R_Phi with the pointwise
intersection of that fibre. A pointwise intersection need not itself be a
nonempty core operation; the read-once theorem supplies that conclusion
in its stated regime.
