# What the next adoption can distinguish

Fix three or more owners and use two distinct owners $r,s$. A negative row
$x;r:A$ suppresses the mark of head $x$ when $A$ posts $r$.
For each observer $k\ne r$, the canonical source probe gives $x$ the
$k$-atom and gives all unspecified inputs the complement of $k$.
Write $\Phi_r(A)$ for the positive singleton test on $A$.

## Independent answers at one fixed register

Let $D$ be a set of $d$ data inputs, and let $\mathcal T$ be an antichain
of $M$ subsets of $D$, each of cardinality at least two. Add a head $h$,
a dummy head $j$, and three inputs $U=\{u,v,w\}$. Write
$G=(u\star_r v)\star_s w$ and $B_T=\{h\}\cup U\cup(D\setminus T)$.
The query requests $h$ at the empty posting. Use the following negative rows.

- At $h$, use $r:T$ for every $T\in\mathcal T$.
- At $j$, use $r:\{h\}$ and $s:B_T$ for every $T\in\mathcal T$.
- At each data input $x$, use $r:U$ and $s:D\setminus\{x\}$.
- At $u$, use $r:\{v\}$ and $s:\{w\}$. At $v$, use $r:\{u\}$
  and $s:\{w\}$. At $w$, use $s:\{u,v\}$.

Decline $r:T$ for any prescribed half of the antichain, then adopt
$r:\{h\}$. Each declined offer deletes exactly its own $h$-row; the
adopted offer deletes the first $j$-row. The query and the resulting
register are identical for every such history. For each $T$, offering
$s:B_T$ is a fresh productive move present as the full block of its
remaining $j$-row.

**Claim.** This last offer is safe exactly when $r:T$ occurred in the
declined prefix. Every offer in the prefix and the adoption of $r:\{h\}$
are safe.

Let $\mathcal R$ denote the surviving $h$-rows, identified with their
coalitions. Form the $r$-fold of $h,G$ and the $s$-fold on each
$L\in\mathcal R$. At an $h$-loss, the corresponding $s$-fold gives
$r$, so the outer fold absorbs. At a data $r$-loss, $G$ gives $r$.
At the other row of a data head $x$, every inner fold containing $x$
contains another input posting $s$, so the mark is erased. The five rows
on $U$ suppress their marks inside $G$; the other operands ignore these
inputs. The dummy is unused. Thus the word omits every remaining mark,
wins the $r$-test on $\{h\}$, and wins it on every $L\in\mathcal R$.
It loses the $r$-test on the empty coalition by idempotence. This proves
the safety of the prefix; it also supplies $h$ at the blank query. If
$T\notin\mathcal R$, every $L\in\mathcal R$ meets $D\setminus T$,
so all operands give $s$ on $B_T$, as required.

If $T\in\mathcal R$, the $h$-row $r:T$ survives $s:B_T$. Any word
winning on $r:\{h\}$ obeys the singleton-profile absorption lemma: it
returns $r$ or includes the whole menu of $h$. Omitting the mark at
this row consequently forces $\Phi_r(T)$. This conflicts with
$\Phi_s(B_T)$ because the two coalitions are disjoint.

**Pure closure.** In every half-prefix context there is no nonempty fold
at a single owner omitting all residual marks. A support meeting any data
input, $u$, or $v$ fails a row whose only posting color differs from its
owner. A fold containing $w$ must be at $s$ and must then contain $u$
or $v$. Any fold containing $h$ must be at $r$ and intersect a
surviving data coalition. A fold supported only at $j$ fails a remaining
$j$-row. These observations exclude all nonempty supports. A child with
a positive adopted test automatically omits the rows just deleted by that
offer, so pure-fold justified saturation makes no change.

There are at least $\binom M{\lfloor M/2\rfloor}$ different answer vectors
for the possible next adoption. Any deterministic state summary answering
every such immediate adoption without the history requires
$M-O(\log(M+1))$ bits in the worst case. With all middle-sized subsets of
$D$, this is $2^{n-O(\log n)}$ bits on $n=d+5$ inputs. For polynomial
prime lists partition $D$ into equal blocks of size $m\sim\log d$ and
take the transversals selecting $k=\lfloor m/2\rfloor$ inputs per block.
Every minimal exclusion hitting all transversals contains $m-k+1$
elements of one block. For the family $B_T$, the minimal hits are a
common input from $\{h\}\cup U$ or $k+1$ inputs in one block. Include the
required $r:h$ exclusion at the dummy head on facets seeing its first
row. Thus there are polynomially many primes, while
$M=\binom mk^{d/m}=2^{n-o(n)}$. Slack inputs can be omitted by taking the
subsequence $d=m\,2^m$.

These bits answer a vector of exact optimal child problems. The initial
query itself always wins, and full saturation at the parent can clear
every surviving $h$-row. This gives no time lower bound for recognizing
one operation table.

## Three clones suppress every one-owner fold

Replace each original input $x$ by three ports, evaluated through
$G_x=(x_0\star_r x_1)\star_s x_2$. Expand a negative row by replicating
its passive singleton postings on all three ports of each posted input,
and requiring a separate mark omission at each of the original head's
ports. Within each port triple add the five guard rows used for $G$
above. An original coalition $A$ lifts to all three ports of its members.
A lifted offer removes either all or none of the rows for each original
head, precisely according to its old coverage, and it cannot cover a guard
row, where at most two ports have postings. The five rows at each triple
exclude every possible one-owner fold even across triples: a support
touching port 0 or 1 fails one of its two rows, and a fold at port 2 alone
would need support at 0 or 1 to obey its $s$-row.

At a marked query fix *any one* of the head's ports as the mark. From an
old witness substitute $G_x$ at every input. On a clone probe all passive
triples are diagonal. If one or more ports of the head are marked with the
observer's atom and the others receive its complement, no port is a
foreign atom. The output of $G_x$ contains the observer and is never a
foreign atom. Its observer view therefore matches the original head atom.
All guards are obeyed because each $G_x$ omits its own local mark while
the remaining triples have no such input winner. The same substitution
preserves all diagonal singleton tests. In particular the proof works for
each preselected positive clone.

Conversely, identify the three ports of every input of an expanded witness.
On an original marked probe this sets all three head ports to the mark.
The foreign singleton statuses of all individual inputs are identical on
this diagonal and the three single-clone probes. Consequently every
foreign singleton test at every subterm has the same value on the four
probes. By induction on the term, observer membership on the diagonal is
the disjunction of the memberships on the three separate probes: at a
foreign absorption all four lose the mark, and at any other gate the
membership tests take union. Thus three negative clone omissions imply
diagonal omission, and one successful positive clone implies diagonal
success. The argument applies to every residual along lifted histories.

For full operation tables, set $F'(w)=F((G_x(w))_x)$. Composition and
diagonalization give $F'$ core iff $F$ is core. Whenever $F$ preserves
constant singleton inputs, no nonempty one-owner fold is pointwise below
$F'$. Use the same triple of singleton menus at every old input. For a
fold at $z$ touching position 0 or 1, give that position $z$ and both
other positions $t=r$ if $z\ne r$, $t=s$ otherwise. The fold gives
$z$ while $G$ gives $t$. For a fold confined to position 2 use
$(s,s,r)$; the fold gives $r$ while $G$ gives $s$. A full-table input
failing singleton idempotence already has a negative answer and can map
to a fixed constant-singleton no-instance which bounds no pure fold.
At fixed $K$ the full table grows cubically and its entries are streamable
in logarithmic work space.

For source-probe tables the new bit at port $x_i$ is zero if $G_x$
loses the marked winner there; otherwise use the old table bit at $x$
whose foreign postings come from the outputs of the other gadgets. This
is the source decomposition formula on realizable tables, and is defined
even for inconsistent candidates. Any realizing word for the resulting
table diagonalizes to a realizer of the old bits: with all other input
triples diagonal and the sibling ports of $x_i$ unposted, all three
clone bits equal the old bit. The diagonal OR then reconstructs it.

Run `python3 checks/open-problem/history_pairs_index.py` and
`python3 checks/open-problem/history_pairs_padding.py` for independent
finite checks. The first evaluates the explicit winning terms and refutes
the failed adoptions by exact term-signature closure on a single row plus
two singleton tests. The second checks the three-owner gate identities,
local guards, and the diagonal relation. The two uniform proofs above
do not require those computations as premises.
