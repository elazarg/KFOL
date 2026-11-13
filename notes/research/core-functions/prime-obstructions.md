# Unbounded prime obstructions survive all proper input reductions

Mathematical result, without new Lean claims. The existing exponential crown
construction has a stronger property than locality alone: every proper
identification minor is core, and every proper neutral residual is ordinary
input union. Hence its failure of realizability cannot be reduced to smaller
operations by either of these input reductions or by disjoint factorization.

Fix a finite role set I with K>=3 and write A for its nonempty subsets.
Choose distinct owners a,b,c. For each d>=2 there is an operation F_d on
V=(Fin d) times Bool with all the following properties:

1. It is 2^d-point core-interpolable and fails (2^d+1)-point interpolation.
2. Every minor obtained by identifying any two distinct input variables
   is a core operation. The same holds for any further identifications.
3. Every neutral residual deleting a nonempty proper set of inputs is
   precisely the union of the remaining inputs.
4. It is idempotent, every input is essential, and its singleton profiles
   are unanimity: Phi_r(E) iff E=V for every owner r.
5. Its prime source guards reconstruct the operation and are monotone,
   but have no joint core realization.
6. It has no proper disjoint idempotent decomposition with essential outer
   inputs. Here proper means that both inner and outer arities are smaller
   than |V|.
7. Every proper collection of complete canonical source bundles has one
   common core realizer with these same unanimity profiles, while the
   full bundle family has none. A bundle includes every observer and every
   genuine passive pattern at its source.

The original [Gray-crown proof](exponential-crowns.md) establishes property 1
and supplies the actual core deletion patches used below. The remaining
arguments are direct and require no search over minors or realizers.

## The patch geometry

Index all bitstrings x by a cyclic Gray ordering next. Let

    L_x={(j,x_j):j in Fin d},   U_x=L_x union L_next(x).

The set U_x\L_x consists of one input position. The exceptional region C_x
assigns {c} at L_x, {b} outside U_x, and a value different from both {b}
and {c} at that single remaining position. The lower set is nonempty and
the upper set is proper, because |L_x|=d and |U_x|=d+1<2d.

F_d is input union except that it returns {b,c} on every C_x. For each h,
its deletion patch P_h uses the same rule except on C_h, where it returns
input union. The P_h are genuine core operations on all winner-valued
inputs. In particular F_d and P_h agree away from C_h.

## Separating patches make every identification minor core

**Patch lemma.** Suppose core operations P_h agree with F away from regions
C_h. If for every pair p!=q some C_h contains no valuation with equal
inputs at p,q, every proper identification minor of F is core.

Indeed choose any pair identified by the minor and such an h. Every
valuation in its diagonal image avoids C_h. The minor of F is therefore
the corresponding minor of P_h, which is core. This argument allows
arbitrarily many simultaneous identifications.

The lower transversals L_x separate every pair of distinct input positions.
If p,q lie in the same coordinate pair, choose its bit to include p. If
they lie in different pairs, choose their bits independently to include p
and exclude q. Some index h has exactly that bitstring. On C_h, input p
is {c}, whereas input q is either {b} or the exceptional free menu, which
is different from {c}. Thus C_h avoids the p=q diagonal. The patch lemma
proves property 2.

The ordinary cyclic crown on n>=3 inputs has the same property. To eliminate
an identification involving position i, omit the exceptional region whose
unique c-input is i: every other input in that region differs from {c}.
Thus its proper identification minors are core as well. No minimum-arity
selection or extraction of an unspecified obstruction is needed.

## Neutral residuals are exactly input union

For a queried winner k, put N_k=I\{k}, an ambiguous menu. Delete a nonempty
proper set S of input variables by giving each of them N_k, winnerwise.

If |S|>=2, no C_x can occur: an exceptional region has only one input
that is not a b/c singleton, whereas every input in S is ambiguous.
F_d is then ordinary input union, and the deleted inputs contribute no k.

If S={j}, an exceptional region is possible only when j is its unique free
position. In that case all other inputs are b/c singletons, with at least
one of each because L_x is nonempty and U_x is proper. Their union is
exactly {b,c}, which is also F_d's exceptional value. Again k belongs to
the output exactly when it belongs to one remaining input. This proves
property 3, including simultaneous deletions. Deleting all inputs instead
gives the empty winnerwise residual.

Every residual retaining just one input is projection, so each input is essential.
Ordinary input union has unanimity singleton profiles, and changing its
value to the ambiguous set {b,c} on a region already containing both b and c
does not alter any singleton output. A diagonal valuation cannot be in an
exceptional region, so F_d is idempotent. This proves property 4.

Since 2^d>=4, property 1 includes three-point core interpolation. The proved
local-normal-form theorem consequently supplies source reconstruction and
monotone canonical prime guards for F_d. Non-realizability from property 1
proves property 5. These are genuine canonical-guard counterexamples, not
arbitrary operations outside the source semantics.

## Primeness and the failure of bounded-prime recognition

Suppose F_d admitted a proper disjoint decomposition through idempotent
inner operations. Its outer operation is the block-diagonal minor, hence
core by property 2. It uses every block, since F_d has full essential
support. The [canonical factor-recovery theorem](block-decomposition.md)
then identifies each inner operation with its block neutral residual,
without assuming F_d is core. By property 3 each inner operation is input
union and is core. Composition would make F_d core, a contradiction.
This proves property 6.

Neutral deletion commutes with identification: deleting a variable of an
identification minor deletes its entire original input block winnerwise.
A nonempty proper deleted block has a nonempty proper preimage. By
property 3 the resulting residual is input union, and identifying its
remaining variables still gives input union. Thus any sequence of these
reductions containing a neutral deletion gives input union on its remaining
inputs, or zero when none remain. A sequence of proper identifications
without deletion gives a core operation by property 2. These operations are
therefore minimal noncore operations for the combined input reductions,
at unbounded arity.

The proper identification minors are automatically compatible on every
overlap: taking further identifications in two ways gives the same minor
of F_d. If 2d>|A|, every valuation has two equal inputs, so these diagonal
faces even cover the entire operation table. Their core operations agree
on all overlaps and determine F_d uniquely as a function, yet that function
is not core. Thus semantic compatibility of the lower-arity operations does
not supply a common term realization.

In particular a recognition method cannot stop after checking all proper
identification minors and neutral residuals, nor reduce every case to a
bounded list of prime input arities using those reductions and disjoint
factorization. For any proposed arity bound choose 2d above it. The
operation F_d is prime and all its proper reduced operations are already
core, yet it is not core. It simultaneously passes all 2^d-point tests.

This rules out a bounded-prime route to the full characterization. It does
not rule out a short intrinsic condition with an unbounded family of
configurations; finding that condition remains the target.

## Every proper collection of complete source bundles is realizable

Let q_h be the free input in C_h. Every input j occurs as q_h: a cyclic
Hamilton Gray enumeration visits both values in each coordinate, and hence
flips that coordinate in both directions. Put H_j={h:q_h=j} and take the
nonempty derived union Q_j of the deletion patches P_h with h in H_j.
It restores input union on the regions C_h with h in H_j and agrees with
F_d elsewhere.

On a changed region, every input except j is a b/c singleton, with both
present. Membership of b,c is therefore unchanged. Any other owner k can
only occur at input j. A canonical probe for a source ell!=j fixes that
input to {k}, so it cannot lie in a changed region. Consequently all of
ell's canonical coefficients agree, for every observer and every genuine
passive pattern. Each patch has unanimity profiles; their union does too.

For any proper source set choose j outside it. Then Q_j realizes all its
complete source bundles at once, with the exact prescribed singleton
profiles. Conversely, three-point interpolation gives canonical source
reconstruction, so a core realization of every bundle would be F_d itself,
contradicting nonrealizability. This rules out bounded-source compatibility
tests even when each tested source includes its entire guard table. It does
not concern arbitrary off-domain independent-flag extensions, which are not
canonically determined by the winner operation.
