# Canonical selectors on atomic-status fibres

Mathematical research, without new Lean claims. This gives common coordinates
for all winner observations, rather than a separate coefficient array for
each observer. It does not characterize which selector codes are core.

Let I be finite with K>=3, let A be its nonempty subsets, and let V be a
finite nonempty set of input variables. An input status
is either an atom r (the input is {r}) or * (the input is ambiguous). Fix a
status pattern e. Let J be its ambiguous input positions and L the set of
roles occurring at its atomic positions.

## Whole-menu selection on one status fibre

**Theorem.** For every core operation F and status pattern e, there are
A_e subseteq L and B_e subseteq J such that for every input v of status e,

    F(v)=A_e union UNION_(j in B_e) v_j.                    (1)

The output is nonempty. In particular A_e and B_e cannot both be empty.
When A_e=I normalize B_e to empty; otherwise the pair is unique.

To prove existence, evaluate the term while retaining only singleton versus
ambiguous status. The status at every subterm depends only on e, by the
singleton-profile recursion. At an owned node, either a child is the owner's
singleton and the output is that singleton, or the output is union. Induction
therefore gives a fixed union of original input menus throughout the entire
status fibre. Its atomic inputs contribute A_e and its ambiguous inputs B_e.
No branch decision depends on the contents of an ambiguous input.

## Canonical recovery

For k in I let N_k=I\{k}. It is ambiguous. Let v^k keep the atomic inputs
of e and give every ambiguous position N_k. Define

    A_e={k:k in F(v^k)}.                                  (2)

Under (1), no ambiguous input contributes k at v^k, so this recovers exactly
the constant part. It also proves A_e subseteq L by conservativity.

If A_e!=I, choose any k outside A_e. For j in J let v^(j,k) be v^k with
input j replaced by I. Then

    j in B_e  iff  k in F(v^(j,k)).                       (3)

The right side is independent of the chosen k outside A_e. Thus (2),(3)
recover the whole code without a chosen representing term. If A_e=I,
(1) is the constant I and the normalized B_e is empty.

Conversely any such pairs, with nonempty right side in (1), define a
statuswise union of whole inputs. Their being canonically determined by the
function does not make all such codes core-realizable.

## Four-point interpolation already forces the selector law

**Theorem.** Every four-point core-interpolable operation F has (1) on
every status fibre, with the canonical recovery (2),(3). Therefore any
failure of this law is witnessed by at most four valuation rows.

First use three-point interpolation to transfer preservation of coordinatewise
union within a fixed status fibre. Three valuations v,w,v union w have
one common core interpolant, which has (1) and hence preserves that union.
Two-point interpolation also transfers the following membership invariance:
on a fixed status fibre, the output's k-bit depends only on which ambiguous
inputs contain k. It holds for every core term by the observer quotient law.

For fixed k, replace every k-containing ambiguous input by I and every
other ambiguous input by N_k. Membership invariance leaves the output's
k-bit unchanged. The standardized valuation is the union of v^k and the
valuations v^(j,k) for the k-containing positions j. Finite union preservation
therefore gives

    k in F(v) iff a_k OR
        OR_(j in J with k in v_j) b_(j,k),                 (4)

where a_k is the k-bit at v^k and b_(j,k) the k-bit at v^(j,k).
The base contributes no new requirement when the family is nonempty:
union preservation gives a_k<=b_(j,k). Here A_e is the set of true a_k.

It remains to synchronize the different winner coordinates. For k,l outside
A_e and a fixed j, take the four valuations

    v^k, v^l, v^(j,k), v^(j,l).

One core interpolant T matches F at all four. Its canonical constant part
omits k and l, by the first two rows. Its single selector B_e^T therefore
makes its two test bits b_(j,k), b_(j,l) equal, by the second two rows.
They are also F's test bits. Hence all b_(j,k) for k outside A_e have one
common value B_e(j). Substituting in (4) proves (1). If A_e=I, (4) gives
the constant I. Nonemptiness excludes A_e=B_e=empty.

The proof of A_e subseteq L uses only one-point interpolation: at v^k with
k absent from L, every input omits k, so a core interpolant's conservativity
forces the k-bit to be false.

## What this compression does and does not remove

The code is shared by all observers and records a whole-menu contribution.
It removes the need to guess separate per-owner selections on one fibre.
Its entries can be computed from the original operation, or from source
guards known to reconstruct it. The remaining problem is compatibility
between the codes at different status patterns.

The [four-variable prime obstruction](face-gluing/README.md) satisfies this
law. In its first affected status fibres, C={c}, D={b}, A is ambiguous,
and B is either {a} or ambiguous. The original H is respectively I or
{b,c} union A union B. The patch turns the whole fibre into
{b,c} union A: when A={b,c} it removes a from B, and when A contains a
both expressions are already I. The second affected fibre is symmetric,
giving {b,c} union B. All other fibres retain H's selectors.

The crown examples satisfy it too: each exceptional region fixes the full
status pattern, including the unique free input's atom or ambiguity status,
and the output there is the constant {b,c}. Elsewhere the selector is input
union. In particular the [unbounded prime obstructions](prime-obstructions.md)
already pass the law by four-point locality. Selector consistency is a
closed cross-observer constraint and a canonical semantic representation;
it does not supply the missing global compatibility criterion.
