# Ordered transport certificates

This note records the complete finite owner-elimination certificate calculus
and its application to canonical source guards. Soundness is proved in
`Core/OwnerElimination`; completeness and finite-sample separation are proved
in `Core/OwnerEliminationComplete`. `Core/SourceCertificates` gives the exact
canonical-guard criterion. The calculus permits finite families of auxiliary
clauses; it does not supply a concise auxiliary-free list of guard laws.

The six-row five-point counterexample has a kernel-checked 32-clause
certificate in `Core/SixValuation`. Its six-patch witnesses work uniformly for
every role type containing three distinct roles. For finite role types, the
non-core operation can also be placed between actual core lower and upper
bounds in one singleton-profile fiber. The independent Python certificate
checker below remains a separate regression.

## The owner-elimination lemma

Write `R_i(t)` for the value of a core term at valuation `R_i`. Fix a target
valuation `Q`, a target owner `a`, and finitely many forbidden observations
`k_i ∈ R_i(t)`. We want the persistence law

```
a ∈ Q(t)  ⇒  ⋁_i k_i ∈ R_i(t).
```

For each owner `r`, start with the rows whose forbidden owner is `r`, and
choose an order on the remaining rows. Suppose the following implications
have already been proved for every core term:

* For each next row `i` in that order,

  ```
  R_i(t) = {r}  ⇒  Q(t) = {r} ∨ ⋁_{j earlier} k_j ∈ R_j(t).
  ```

  Here “earlier” includes all rows with `k_j = r`.
* For `r = a`, there is an anchor implication

  ```
  Q(t) = {a}  ⇒  ⋁_{j : k_j = a} a ∈ R_j(t).
  ```

If the desired persistence law holds for each variable, these certificates
prove it for every core term.

Proof: suppose a parent term, rooted at `⋆_r`, violates the law. The negatives
at rows with forbidden owner `r` pass to both children: an owner membership
cannot disappear at its own choice. If `r ≠ a`, neither child's value at `Q`
is `{r}`, since that would make the parent value `{r}` and remove `a`. If
`r = a`, the anchor and the already inherited negatives give the same
conclusion. Now follow the selected order. The transport implication excludes
the next row's value `{r}` in both children. That row's choice therefore acts
as union, so its forbidden membership is absent in both children. Eventually
both children inherit every negative. A membership in a choice's result comes
from one of its operands, so some child retains `a` at `Q`, contradicting the
induction hypothesis.

Owners outside the support of all supplied valuations need no transport
work: they cannot be singleton outputs, so their choices act as union on
these valuations. Thus a finite matrix can support a certificate even when
the role type itself is infinite.

The useful content of this step is an acyclic order for blocking absorbers.
Its premises are transport implications. The complete finite calculus below
supplies their expanded clauses as simultaneous auxiliary invariants, with
soundness and completeness proved in Lean.

## One pivot per owner

The same argument has a broader form. Describe the failure of a proposed
clause by unary conditions on row outputs. For a fixed root owner, prove that
all conditions except one pass to **both** children, and the remaining pivot
condition passes to **some** child. That child witnesses failure of the same
clause at smaller term height. Useful inheritance rules are:

| Parent condition | Always passes to some child | Passes to both children when |
|---|---|---|
| `k ∈ R` | yes | not asserted in general |
| `k ∉ R` | yes | root owner is k, or neither child at R is the root-owner singleton |
| `R={k}` | yes | root owner differs from k |
| `R≠{k}` | yes | root owner is k |

The second row uses the fact that membership in both operands remains in
their choice. An already proved clause can exclude absorbing singletons and
therefore strengthen inheritance from “some” to “both”. The order in the
previous section is one way to organize those exclusions.

For example, failure of `E=a ⇒ bB or aC` means `E=a`, `b∉B`, `a∉C`.
At owner a, pivot on `E=a`; the a-negative at C passes to both, and
`B=a ⇔ C=a` excludes absorption at B. At owner b, pivot on `a∉C`;
`E=a` and the b-negative at B both pass to both. At owner c, again pivot on
`a∉C`; `E=a` passes to both, and the incompatible pair `E=a, B=c` blocks
absorption at B. Outside these owners the rows are unions and either
negative can be the pivot. This proves the auxiliary bridge by the same
mechanism as the larger cover.

This is a sufficient induction rule. With a fixed, restricted stock of
auxiliary clauses, no completeness claim is made. The semantic completeness
result below permits an unrestricted finite stock of valid dual-Horn
auxiliaries instead.

## Why dual-Horn clauses are a natural target

For finitely many roles and rows, encode an evaluation tuple by its set of
true memberships `P = rows × roles`. In the core with at least three owners,
union is term-definable. Hence each generated evaluation relation is a
nonempty union-closed family of subsets of P.

Every finite nonempty union-closed family has a complete description by
clauses of the forms

```
p ⇒ q₁ or ... or qₘ,       q₁ or ... or qₘ.
```

To separate a set X outside the family, first consider all family members
contained in X. If there are none, every member meets `P \ X`, giving the
second type of clause. Otherwise their union U is in the family. Since
X is not, choose `p ∈ X \ U`; then `p ⇒ ⋁(P \ X)` holds throughout the
family and fails at X.

Thus one positive membership premise, or a pure positive cover, suffices for
*extensional separation*. Atomic tests in transport proofs are auxiliary
abbreviations that make the induction easier. This observation supplies no
arity bound and no direct intrinsic criterion: requiring preservation of all
compatible dual-Horn relations would still be a Pol–Inv reformulation.

## A complete finite certificate calculus

Here is a precise syntactic certificate system, for finite roles and rows.
A clause has an optional single positive membership premise and a finite
head of memberships. Absence of a premise means a pure positive cover.
Repeated head atoms can be removed. A certificate consists of a finite
family F of clauses and the following data:

1. Every variable column satisfies every clause in F.
2. For every clause C in F and root owner r, initialize S to the head atoms
   whose winner is r. Supply a sequence of distinct remaining head atoms,
   added to S one at a time. Each addition has the blockers specified below.
3. At the end, C with its head restricted to S is itself a member of F,
   or is implied by a stronger clause in F. This may be C itself. The
   sequence is allowed to stop before exhausting the head.

For the next head atom `k_i ∈ R_i`, its winner differs from r. If C has
premise `a ∈ Q` with `a ≠ r`, the required blocker is

```
R_i={r} ⇒ Q={r} or ⋁_{j∈S} k_j ∈ R_j.
```

It is supplied syntactically by requiring that F contain each clause, for
`s ≠ r`,

```
s ∈ Q ⇒ (⋁_{k≠r} k ∈ R_i) or ⋁_{j∈S} k_j ∈ R_j.
```

If C is a pure cover, or has premise owner `a = r`, the stronger blocker is
required instead:

```
R_i={r} ⇒ ⋁_{j∈S} k_j ∈ R_j.
```

It is supplied by requiring that F contain the pure positive cover

```
(⋁_{k≠r} k ∈ R_i) or ⋁_{j∈S} k_j ∈ R_j.
```

Nonemptiness of row values makes these expansions equivalent to the atomic
blockers. All certificate obligations are finite: column truth, membership
of explicit clauses in F, and order bookkeeping. A required clause can also
be supplied by a family clause with the same premise or no premise and a
subset of its head; tautologies need no family clause. This elementary
subclause rule is what the checker implements. Allowing arbitrary
propositional consequences of F would preserve soundness, but is unnecessary
for completeness.

### Soundness

Every clause in a certified family holds at every core term. Prove all
clauses simultaneously by induction on term height. At a root `⋆_r`, suppose
C fails. Its initial S-negatives pass to both children because their winner
is r. If C has premise owner `a ≠ r`, its positive membership excludes the
value `{r}` at Q in both children. For each next head atom, the blocker
clauses hold at both children by the simultaneous induction hypothesis;
therefore neither child has the value `{r}` in that row. The parent
negative passes to both children, and the row is added to S.

At the end both children satisfy all S-negatives. They also satisfy the
terminal restricted-head clause, again by induction. For a pure cover this
is an immediate contradiction. For an implication, some child retains the
parent's positive membership, contradicting that child's terminal clause.
This uses only an acyclic order *inside* each owner case; auxiliary clauses
may depend on each other through the simultaneous induction.

### Completeness

Let R be the relation of tuples generated by the variable columns under
coordinatewise owner choices. Choose F to be the finite family of all
dual-Horn clauses valid throughout R. The column condition is immediate.
The following argument supplies an order and terminal clause for every
`C ∈ F` and every r.

Initialize S as prescribed. If the restricted-head clause is valid on R,
stop. Otherwise choose a base tuple `x ∈ R` with all S-memberships absent
and, if C has a premise, with its premise present. Some remaining head atom
must have a valid blocker of the required kind. If not, choose for each
remaining i a witness `y_i ∈ R` that violates its blocker: all S-negatives
hold, its value at `R_i` is `{r}`, and, in the conditional-blocker case,
its value at Q differs from `{r}`.

Fold x and these witnesses using `⋆_r`. The resulting tuple is in R. Every
S-negative survives, since an owner choice is contained in the union of
its operands. Every remaining row has an operand `{r}`; at that row the
fold becomes and stays `{r}`, avoiding its forbidden winner `k_i ≠ r`.
If there is a premise with owner different from r, all Q-operands differ
from `{r}`, so Q remains their union and retains the premise. If the
premise owner is r, its membership persists under its own choice. Thus the
fold violates C, a contradiction. No associativity theorem is needed:
these facts hold for an ordinary left fold.

Choose a valid blocker, add its atom to S, and continue. Its expanded
clauses are valid on R, hence belong to F. The process terminates, at worst
when S is the whole head. Its terminal restricted clause is valid and so
belongs to F. This supplies the complete certificate.

The calculus is therefore sound and complete for dual-Horn consequences of
the input columns. When union is term-definable, these clauses also separate
every tuple outside the generated relation, as proved above. The certificate
itself is entirely syntactic; semantic validity is used only to show that a
certificate exists.

`OwnerEliminationComplete.exists_complete_certificate` formalizes this
construction. `choiceClosed_iff_checked_clauses` identifies finite
choice-closed relations with checked clause presentations, assuming three
distinct owners for union definability. `finite_sample_iff_checked_clauses`
and `truth_table_iff_checked_clauses` give exact interpolation criteria.
Roles and rows are finite; variables need not be finite for the sampled-row
criterion. No bound on the number of auxiliaries or a fixed relational arity
bound is asserted.

`SourceCertificates.source_probes_iff_checked_clauses` specializes the tests to
canonical source probes. For finite role and variable types,
`Sources.guard_table_iff_certified_clauses` states that a guard family is a
core normal form if and only if it is canonical and its raw probe values
satisfy every clause with a checked certificate from the projection columns.
The tests force nonempty probe values as well. This is an exact syntactic
criterion on canonical guards; certificates may contain arbitrary finite
auxiliary families. The completeness construction uses the evaluation
relation to prove existence, while a supplied certificate is checked using
only its finite clauses, owner orders and input columns.

## Reproducing the six-row certificate

From the repository root, run:

```
python3 notes/research/core-functions/verify-five-point-transport.py
```

Add `--clauses` to print the complete family. The checker uses only Python's
standard library and the adjacent `five-point-transport.json`. That JSON
contains the six input rows, 32 clauses, their 96 owner orders, and 264
blocker steps. It contains no generated subpower or term-function tables.
The discovery program and its 7,260-tuple relation are not needed to verify
the artifact and are not dependencies of this checker.

The root conclusion printed by the checker is

```
aQ => aA or bB or aC or aD or bE
```

An atom is encoded by `row * K + role`, with roles a,b,c and rows
Q,A,B,C,D,E in that order. Each auxiliary entry either names a stronger
family clause or marks a tautological expanded blocker. The verifier checks
every variable column, every addition to an owner order, every auxiliary
subclause inclusion, and every terminal restricted-head obligation.

`Core/SixValuation` checks the corresponding finite obligations in Lean and
applies the generic simultaneous-induction soundness theorem. Role
restriction transports the root conclusion to every role type containing
three distinct roles. Thus the six-row law now has a kernel-checked proof
independent of subpower enumeration. The Python artifact independently checks
the same certificate pattern.

## The six-row matrix

The rows, in the order used by the independent finite check, are:

| Row | X,Y,Z,W,V | Observation |
|---|---|---|
| Q | c,b,c,a,b | a present |
| A | b,b,bc,a,c | a absent |
| B | b,a,c,c,c | b absent |
| C | c,a,b,c,b | a absent |
| D | c,bc,bc,b,a | a absent |
| E | a,c,b,c,ac | b absent |

Concatenation denotes a set. The target law is

```
a ∈ Q ⇒ a ∈ A ∨ b ∈ B ∨ a ∈ C ∨ a ∈ D ∨ b ∈ E.
```

Only variable `W` meets the antecedent, and it supplies `a ∈ A`, so the
variable cases are immediate. The required owner orders are:

| Root owner | Initially inherited rows | Subsequent order |
|---|---|---|
| a | A,C,D | B,E |
| b | B,E | C,A,D |
| c | none | D,A,B,C,E |

The anchor is `Q={a} ⇒ A={a}`: these two valuations have exactly the same
`a`-singleton inputs. Similarly `B={a} ⇔ C={a}`.

The remaining sufficient transport implications are listed below. An entry
such as `aD` means membership `a ∈ D`, whereas `Q=c` means the exact singleton
`Q={c}`.

| Premise | Sufficient consequence |
|---|---|
| B=a | aC |
| E=a | bB or aC |
| C=b | Q=b or bE |
| A=b | Q=b or bB or aC or bE |
| D=b | Q=b or aA or bB or aC or bE |
| D=c | Q=c |
| A=c | Q=c or aD |
| B=c | Q=c or aA or aD |
| C=c | Q=c or aA or bB or aD |
| E=c | Q=c or aA or bB or aC or aD |

All these implications hold on the complete 7,260-tuple six-row subpower
computed by the independent checker. The equal-atom implications and
`D=c ⇒ Q=c` follow from singleton-profile invariance and monotonicity. A
short independent term-induction proof has also been derived for
`E=a ⇒ bB or aC`: it uses `B=a ⇔ C=a` and the incompatible atom pair
`E=a, B=c`, whose input supports `{X}` and `{Z,W,V}` are disjoint.
The simultaneous certificate proves the expanded clauses needed for the
root persistence law; Lean now checks that certificate and the resulting
uniform six-row theorem. The displayed transports explain an economical
owner order, while the certified expanded clauses carry the formal proof.

## Why singleton profiles do not finish the proof

Replacing the membership consequents by singleton consequents is invalid.
The computed relation contains, for example,

```
(Q,A,B,C,D,E) = (b,c,c,ab,abc,c).
```

Thus `A=c` holds and `a ∈ D` holds, but neither `Q=c` nor `D=a` holds.
Likewise the relation contains `(c,bc,bc,bc,bc,a)`, which satisfies `E=a`
without `B=b` or `C=a`.

Among the ten clauses above, only `D=c ⇒ Q=c` survives replacement of every
membership consequent by a singleton consequent. The full value semantics,
not merely the admissible singleton-profile classification, is needed for
the proposed transport proof.

## Remaining simplification questions

The complete certificate criterion settles exact recognition by checked
owner-elimination proofs, including its canonical source-guard specialization.
A concise fixed family of auxiliary-free guard laws is not obtained. A
parameterized family of matrices with these certificates could also establish
an unbounded local-interpolation hierarchy, but the existing four- and
five-point obstructions do not by themselves establish such a family.
