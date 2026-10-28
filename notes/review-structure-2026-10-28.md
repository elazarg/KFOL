# Review of b5dbca9: structure.tex, Perspectives.lean, revised report.tex

This review was done by reading only. Nothing was compiled or run.
"Checked" below means checked by hand.

## Verdict

Every statement I checked is correct. That includes the counts 18, 626, 70, 639 and
4110, which I recomputed by hand. The previous review's main point (uniform copies
equal the singleton lift) has been absorbed and taken further: the new D∘H example
shows that the uniform-copy semantics is not preserved by substitution.

The perspective decomposition is the most important new result for the original
project. It is the rational-play counterpart of the old manuscript's "viewpoint
reduction", and it shows that unbiasedness is a theorem rather than a slogan:

- each player's exact contextual view has K+1 values;
- the algebra is a subdirect product of exactly these K views;
- no subdirect decomposition into subdirectly irreducible factors can drop any of
  them (minimum subdirect decomposition).

Under forcing, by contrast, every coalition view collapsed to a Boolean value.

The methods are standard (Leibniz congruence, Moore families, uniform matroids), as
the note says. The contribution is a clean structure theory for one finite algebra.
Two caveats limit how far it currently goes:

1. **The perspective results disappear once role switching is internal (§5).** The
   original syntax, Abramsky's π̂ and the operators −_ij of Olde Loohuis–Venema (OLV)
   all have internal role switching. So the algebra a *logic* needs is probably
   A^sym, not A, and A^sym is subdirectly irreducible.
2. **There is still no axiomatization or proof calculus.**

## Statement-by-statement

**Thm 2.1 (one-player quotient): correct.**
- The two calculations hold:
  - S⋆_rT = {i} iff (r = i and S or T is {i}) or (r ≠ i and S = T = {i});
  - k ∈ S⋆_rT, for k ≠ r, iff (k∈S or k∈T) and neither input is {r}.
- The relation on the right-hand side uses only k-membership and "= {i}" for i ≠ k,
  and both are closed under every ⋆_r. So it is a congruence.
- The separating contexts are x and x⋆_i⟨k⟩.
- There are K+1 classes; the class n needs K ≥ 3.
- Lean's `contextualAt_iff` uses only singleton constants. That is harmless: fewer
  contexts, the same congruence.

**Cor 2.2: correct.** The quotient tables also hold: for owner r ≠ k the order is
a_i < n < p < a_r, and for owner k it is a_i < n < p. At K=2, C_k is Boolean, as it
should be.

**Thm 3.1 (test domains): correct.**
- For sufficiency, the representative replacement preserves the k-view. This is
  faithfully mechanized at every arity in `complete_test_domain`.
- Necessity:
  - R(C=I, E_i = I∖{i,k}, other rows full) differs from the constant I only at {i};
  - F_k = R({k}, ∅) differs from the identity exactly on ambiguous sets omitting k.
- At K=3 the ambiguous sets omitting k are exactly I∖{k}, which gives 6. For K ≥ 4,
  two disjoint pairs give K+2.

**Thm 4.1 (status forms): correct.**
- If J ≠ ∅, the value has at least two elements, so the collapse test on (C,∅) is
  exact.
- Uniqueness uses pairs omitting or containing k, both available at K ≥ 3.
- Calling it a "sound and complete normalization calculus" is too strong. It is a
  decision procedure computed from the semantics, not a calculus.

**Thm 5.1 (congruences): correct.**
- c(S) = ⋃[S], with monotonicity via T θ c(S)∪T.
- The atom collapse uses x⋆_iI.
- In the converse, the case where only one side collapses forces c({i}) = I.
- The count of 18 at K=3 is Σ_X 2^{#pairs inside X} = 1+3+6+8.
- The count of 626 at K=4 is 5 + 12 + 64 + 545. Two triples meet in a pair, so the
  545 is Σ_m C(4,m)·2^{6−C(m,2)}.
- Both counts match.

**Thm 5.2 (subdirectly irreducible images) and Cor 5.3 (minimum decomposition):
correct.**
- F_S is join-irreducible, because S is not an intersection of singletons.
- The monolith pairs S with I. I checked all three collapse routes, including the
  owner-outside-S trick.
- I∖{k} versus I is separated only by F_{I∖{k}}, so all K factors are needed.

**Thm 6.1 (symmetric chain): correct.**
- (K−1)-element sets can be intersected down to every set of size ≤ m because m < K.
- The congruences are exactly the closures c_m, i.e. truncations of the uniform
  matroid of rank m+1.
- Cor 6.2 (A^sym is subdirectly irreducible, with monolith ker c_{K−2}) is correct.
- The claim that a one-player view becomes faithful via π(x) is correct.

**§7 (uniform selection): correct.**
- U(D∘H)({a}) = D({a,c}) = I, whereas U(D)(U(H)({a})) = {a,c}.
- The condition for U(R) = R is right: for each k ∈ C, at most one row omits k.
  This gives (K+1)^K + 2^K − 2, i.e. 70 and 639.
- The image count 2^{K(K−1)} + 2^K − 2 gives 70 and 4110.
- The K ≥ 4 example (C = {d}, E_a = {d}) is not regular. So the lift leaves the
  clone, as claimed.

**Lean (Perspectives.lean).**
- The statements are faithful.
- There is no `sorry` or added axiom.
- Lean covers the easy halves: the congruence, its contextual characterization,
  test-domain sufficiency and atom collapse.
- These are still paper proofs: unary synthesis (on which every lower bound
  depends), the congruence classification, subdirectly irreducible images, the
  symmetric chain and status forms.

## Issues and suggestions

1. **Choose the signature of the logic.** The game syntax has internal role
   switching, and OLV's comparable algebra does too. With it:
   - the K perspectives no longer give a decomposition;
   - the algebra is subdirectly irreducible;
   - its congruences form a chain of ambiguity thresholds.

   That chain is the more natural "logic" result: m = 1 gives unique winners only,
   and larger m keeps more ambiguity. Either motivate A as the logic and A^sym as
   an extension, or the other way round. At present the abstract leads with results
   that only hold without the role switch.
2. **Finite basis: a concrete route (check this; I'm not certain of it).**
   - A has a semilattice term operation (∪ via J). I believe a locally finite
     variety with a semilattice term omits tame-congruence-theory types 1 and 2.
     If so, it is congruence meet-semidistributive.
   - In that case Willard's theorem (JSL 2000) gives a finite basis as soon as V(A)
     has a finite residual bound.
   - So "is V(A) finitely based?" may reduce to bounding the subdirectly irreducible
     members of V(A) = V(C_k : k ∈ I). The note correctly says its result covers
     only images of A itself.
   - The same question applies to A^sym.
3. **Clone.** Status forms give a canonical (C,J) table per status cell. The missing
   step is to characterize which tables are realizable. The unary classification is
   the n = 1 case, and its constraints (a fixed C on multi-element cells, rows inside
   C) suggest the general compatibility conditions. That would complete the
   description of term functions.
4. **Toward the logic.** The matrix ⟨C_k, {p}⟩ ("k may win") is the natural
   single-player consequence relation. A sequent or tableau calculus for it is
   generic (a finite matrix), so on its own it is not a contribution. A *uniform* in
   K presentation would be. So would a calculus whose rules are the per-owner order
   descriptions (a_i < n < p < a_r).
5. **Minor.**
   - Cite Blok–Pigozzi 1989 alongside Font 1993 for the Leibniz operator.
   - Cite Oxley's *Matroid Theory* rather than lecture notes for uniform matroids.
   - "Normalization calculus" should be "decision procedure".
