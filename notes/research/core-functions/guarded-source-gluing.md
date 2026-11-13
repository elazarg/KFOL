# What remains after retained-source normalization

Mathematical research, not new Lean claims. The full direct guard
characterization is still the target. The results below isolate the
interface that prevents the [retained-source normal form](retained-sources.md)
from immediately extending to guarded sources.

## A stronger atomic erasure

For a word t(j,v), fix j={q} and use the fixed-winner erasure compiler.
If q belongs to t({q},v) but not to its erasure g_q(v), a fixed-q leaf
supplies q through a surviving source path in the original word.

Prove this together with the erasure invariant. At a foreign root, whenever
the original root does not absorb, each corrected table row has q-bit equal
to the union of the two erased q-bits. An error therefore traces a child
error. At a q-root the q-bit is OR, so again it traces a child. A discarded
constant-q child supplies the required leaf. To justify that last step,
in a globally constant-q subword replace every ordinary q-containing input
by N_q. The output is still q, and now q can only come from a fixed-q
leaf. Every rival singleton status is unchanged, so the same leaf path
survives before the replacements.

Consequently, with c_(q,j) the original canonical source coefficient,

    t({q},v) = g_q(v) union ({q} if c_(q,j)(v) else empty).

The erasure can omit some redundant q-membership when that source is
active; it is exactly the full cofactor whenever that source is inactive.
An omitted g_q denotes the constant-q case.

## Exact necessary data at one separable source

Assume j is active and its canonical coefficients have shared factors

    c_(k,j) = AND_(r!=k) D_r(E_r),

with D_r antitone and D_r(empty)=true. Other sources need not separate.
Put C=partial_j F and E_r={i!=j:v_i={r}}. The cofactor-dependence theorem
shows that failure of any D_r makes F independent of j at those parameters.
If all D_r hold, the source formula makes F contain its whole j-input.
The unary-context normal form therefore gives, for ambiguous S,

    F(S,v)=C(v) union (S if ALL_r D_r(E_r) else empty).

For atomic inputs there are optional lower-arity core operations g_q<=C
such that

    F({q},v)=g_q(v) union
                 ({q} if ALL_(r!=q) D_r(E_r) else empty).

The stronger erasure statement gives

    g_q(v)=C(v) if D_s(E_s) fails for some s!=q.

These are exact necessary data, but they are not sufficient for gluing.

## The reciprocal example defeats separate cofactor tests

Use the existing four-variable separable hull on A,B,C,W with owners 0,1:

    G=A union W
        union (B if NOT(C=W={1}) else empty)
        union (C if NOT(A=B={0}) else empty).

It is noncore by the three-row persistence proof in
[separable-hull-failure.md](separable-hull-failure.md). Take j=B. Its only
nonconstant source factor is D_1=NOT(C_1 AND W_1), and its neutral
baseline is U=A union C union W. Define lower-arity core operations

    g_0=R_0(C,A) union W,
    g_q=U for every q!=0,
    R_0(C,A)=(C union A) choice_0 A.

Thus R_0(C,A)=A when A={0}, and C union A otherwise. All these g_q are
core and below U. When D_1 fails, C=W={1}, so g_0=U as well.
Direct substitution verifies every atomic and ambiguous formula above.
Nevertheless G is not core.

The missing condition already appears as a one-sided reciprocal law.
Let q,s be distinct, and let L,M be disjoint passive sets not containing i.
For a nonomitted g_q, write c_q^(g_q) for its canonical q-closure.
Every actual realization satisfies

    i in c_q^(g_q)(L) AND NOT D_s(M union {i})
        ==> NOT D_q(L) OR NOT D_s(M).

Indeed choose a third observer k. The three persistence rows have
j=k,i=s,M=s,L=N_k; j=q,i=k,L=q,M=N_k; and
j=k,i=N_k,L=q,M=s, respectively. The first two negative queries follow
from D_s(M+i)=false and the g_q capture. If D_q(L) and D_s(M) both held,
the positive query in the last row would contradict persistence.
For the displayed G use q=0,s=1,i=C,L={A},M={W}.

## Even all reciprocal interfaces are insufficient

The existing three-head private-context construction supplies the next
obstruction for K>=4. Let j,h_1,h_2 have capture owners A,B,C and let
a_0,a_1,a_2 be private anchors. Its only captures are

    {h_1,h_2,a_0} =>_A j,
    {j,h_2,a_1}   =>_B h_1,
    {j,h_1,a_2}   =>_C h_2.

The separable reconstruction is noncore by the complete-head theorem
with a fresh observer D. At source j only
D_A=NOT(h_1,A AND h_2,A AND a_0,A) is nontrivial. Its baseline is union
of the five passive inputs. The atomic erasures g_A,g_D (and any further
owner's erasure) are that union. The other erasures are explicitly core:

    g_B=(h_2 union a_0 union a_1 union a_2)
             union [h_1 choice_B (h_2 choice_A a_1)],
    g_C=(h_1 union a_0 union a_1 union a_2)
             union [h_2 choice_C (h_1 choice_A a_2)].

They obey all the cofactor/default formulas and equal the baseline
where D_A fails. Every reciprocal interface also holds. For q=B the
only captured i is h_1, with L containing h_2,a_1; a nontrivial D_A
premise requires M to contain h_2,a_0. These L,M cannot be disjoint.
The q=C case similarly forces the shared h_1. The remaining closures
are identity. Thus the missing interface is higher than pairwise
reciprocal capture; it is not repaired merely by adding every C2 instance.

## Cofactor erasures need not be canonical intersections

Even in the retained class, take distinct q,s,r and

    F=j union ((j choice_q x) choice_s y).

Then F_q={q} union y, and its neutral baseline is
C=y when y={s}, otherwise x union y. The valid erasure is g_q=y.
At x=I,y={r}, however, F_q intersection C={q,r}. The two menus I,{r}
form a subalgebra of the core, so no binary core word can take that value
there. The literal intersection is not core. An intrinsic choice of
cofactors must allow discarding redundant q-membership, as the compiler does.
