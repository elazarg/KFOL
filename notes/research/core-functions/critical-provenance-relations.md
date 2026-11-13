# Unary critical relations above the high-value boundary

Written mathematics only. This classifies one interval of the invariant
relation lattice of the joint pure-trace algebra P, not all its relations.
It does not settle the direct source-guard characterization.

Use the notation of [pure-trace-quotient.md](pure-trace-quotient.md):
Q={0,alpha,beta}, addition is maximum, and multiplication is zero when
either argument is zero and maximum otherwise. In P=product_r Q_r,
choice_r is multiplication in coordinate r and addition elsewhere.
There are at least three owners.

Put D={u: some coordinate of u is beta}. This is invariant: a foreign
beta survives any owned operation; if all beta coordinates of both inputs
are at the root owner, both inputs are nonzero there, so beta survives.
Let z_S have zeros exactly at S and alpha elsewhere, and h=z_empty.
Every relation containing D is uniquely D union {z_S:S in Z}.

**Classification.** Such a relation is invariant exactly when Z is an
ordinary downset of the Boolean lattice 2^I, or Z={{r}} for some owner r.
The empty downset is allowed.

For necessity, fix S in Z and q in S. Combine z_S at an owned-q gate
with a tuple whose sole beta is at q. By choosing its other coordinates
to be zero or alpha, obtain every z_T with q in T subseteq S. Thus all
nonempty subsets of S belong to Z. If S has at least two elements, this
gives two distinct singleton zero-sets. Their union as P-tuples is h,
forcing the empty set into Z. The same applies whenever Z contains two
different singleton sets. Hence either Z is the stated exceptional family,
or it is downward closed (including the empty set if nonempty).

For sufficiency, two low tuples with zero-sets S,T combine at owner q
to give zero-set

    (S intersection T) union ({q} intersection (S union T)).

This is a subset of one input zero-set, so a downset is closed. Mixing a
low tuple with D either retains a beta, or has zero-set T subseteq S
containing q; thus it also preserves a downset. For the exceptional
Z={{r}}, a beta can disappear in such a mixture only at owner r, and
the result is exactly z_{r}. This proves that exception closed too.

**Critical relations.** The meet-irreducible invariant relations containing
D are precisely

    R_r = D union {z_{r}},

and, for nonempty T subseteq I, the single mixed-height clauses

    C_T(u) iff (exists t in T: u_t != 0)
                 or (exists s outside T: u_s = beta).

Indeed C_T has low zero-sets {S:T is not a subset of S}. A downset is the
intersection of these downsets for its minimal excluded nonempty sets.
Adjoining z_T to C_T gives its unique cover; any larger invariant relation
contains z_T. R_r has unique cover R_r union {h}: any other low tuple
either is h, has a different singleton zero-set and joins z_r to h, or
has two zeros and generates two different singleton zero-sets and hence h.
D itself has multiple covers, for example the R_r and D union {h}.
The classification of Z then proves completeness. Every invariant
superrelation of a relation containing D still contains D, so
meet-irreducibility in this interval agrees with meet-irreducibility in
the full invariant-relation lattice. R_r's cover changes neither any owner marginal
nor the full zero/nonzero-pattern relation: D already realizes every
nonzero pattern, including h's all-positive pattern. These are genuine
mixed provenance holes.

**An intermediate constraint.** These exceptional R_r add information to
the coordinate Q_0 basis and ordinary rainbow nonzero clauses. For distinct
owners A,B take coordinate terms

    g_A(x,y,z) = (x*y)+z,
    g_B(x,y,z) = (x*z)+y,
    g_s(x,y,z) = x+y+z for all other s.

Their singleton profiles are (x or y)z, (x or z)y, and xyz, respectively.
These are admissible: any A- and B-winning coalitions intersect, and all
other winning coalitions are the full variable set. Thus g preserves the
ordinary rainbow clauses, and its coordinate terms preserve the Q_0
relations. Nevertheless the input columns

    x=(0,beta,alpha,...),
    y=(beta,alpha,alpha,...),
    z=(alpha,0,alpha,...)

all belong to R_B and give output h, outside R_B. This is the familiar
parallel-pair closure obstruction expressed by a unary critical relation.
The known four-variable feedback counterexample passes every unary
subalgebra, so this unary classification is not a complete basis of P.
