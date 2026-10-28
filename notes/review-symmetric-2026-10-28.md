# Review of f5796df: symmetric.tex, Synthesis.lean, follow-up edits

This review was done by reading only. Nothing was compiled or run.
"Checked" below means checked by hand.

## Verdict

Every statement I checked is correct. The previous review's points are all taken up:

- internal role switching is now part of the intended signature;
- unary synthesis and the necessity direction of the test-domain theorem are in Lean;
- the Blok–Pigozzi and Oxley citations are added;
- the "calculus" wording is fixed;
- the Willard route is stated with the residual-bound condition left open, which is
  the correct caveat.

The new pair theorem is the best result so far. It is uniform in K and in arity, and
it has the form of a logic result: every failed equation has a countervaluation in
which each variable denotes one or two possible winners. Its proof is short and
robust.

Caution: the three-role unary classification is attractive, but its
partial-permutation structure is a K=3 artifact (point 2 below). Before building on
the symmetric-inverse-monoid narrative, identify the general-K object.

## Statement-by-statement

**Lemma 2.1 (permutation provenance): correct.** On a status cell, collapse happens
exactly when a child is the constant owner singleton. A child with a nonempty P_j
denotes at least two roles. Role switches compose with the coefficients.

**Thm 2.2 (pair countervaluations): correct.**
- Shrinking each ambiguous input to a pair inside it keeps the status cell, so it
  keeps the same provenance.
- The right side, a union of permutation images, can only shrink.
- The left witness k = π(i) survives because i was kept.

**Lemma 2.3 (Reset): correct.**
- At {i}, the ⋆_i step returns {i}.
- Every other owner j sees a current value containing i ≠ j, so it takes a union and
  changes nothing.
- On ambiguous inputs nothing collapses.

**Thm 2.4 (minimum test domain D₂, of size K(K+1)/2): correct.**
- Singleton necessity comes from the reduct separators.
- For a pair P, take k ∉ P and F(x) = x ∪ C ∪ ⋃_{i∉P∪{k}} (i k)(x):
  - x ⊆ P gives C, because P ⊆ C and the transpositions fix x;
  - every other x gives I;
  - Reset(F) and Reset(I) therefore differ only at P.

**Thm 3.1 (751 unary operations at K=3): correct.** I checked each piece.
- *Live provenance bound.* At a node, a value equal to {r} at {i} lies inside the
  bound of the child that equals {r}.
- *Mandatory images.* For owner ≠ k, a live child containing k cannot be the owner
  singleton. A constant child equal to {r} makes the whole expression constant. The
  argument transports through role switches.
- *Threshold.* At K=3, any |A_k| ≥ 2 meets every 2-set, so variable coordinates have
  a single source. Two targets from one source would contradict the fact that each π
  is a function, so p is a partial injection.
- *Rows.* The rows satisfy {p(i)} ⊆ D_i ⊆ C_p ∪ {p(i)}.
- *Synthesis, rank by rank:*
  - rank 3: the permutation itself;
  - rank 2: π followed by R(C_p, E);
  - rank 1: on singleton inputs {b},{c}, ⋆_b is OR, ⋆_c is AND and (b c) is NOT, and
    the relative constants fix {a}. Then precompose with R(C_p, 0) and postcompose
    with R(Z, E_a = Z), which preserves subsets of C_p and I;
  - rank 0: mergers x⋆_a(a b)(x) and permutations give every map I→I; take a union
    of three of them and precompose with R(I, 0).
- *Counts:* 343 + 9·36 + 18·4 + 6 = 745, plus 6 constants, gives 751.

**Thm 4.1 (monoid onto the symmetric inverse monoid 𝓘_I): correct.**
- F_p ∘ F_q = F_{p∘q}. The constant parts work out because
  (I∖ran p) ∪ (ran p ∖ ran(p∘q)) = I ∖ ran(p∘q).
- The formula for composed rows is right.
- The units are exactly the 6 permutations.

**§5 (congruence meet-semidistributivity): correct, and it settles my earlier hedge.**
An independent check: for a locally finite variety with an ACI term s, the terms
w₃ = s(s(x,y),z) and w₄ = s(w₃,w) are weak near-unanimity terms with
w₃(y,x,x) = s(x,y) = w₄(y,x,x,x). By the Kozik–Krokhin–Valeriote–Willard
characterization, the variety is congruence meet-semidistributive. I did not check
Willard's theorem numbering (2.1 and 4.3).

**Synthesis.lean: faithful.**
- `unary_synthesis` produces exact rows {i}∪E_i and the extra set C on ambiguous
  inputs, using only singleton leaves, owned choices and neutral-union terms.
- `test_domain_necessary` derives both conditions from unary completeness.
- `winners_instantiate` is the substitution lemma connecting term instantiation to
  SPE winners. It is a useful bridge.
- There is no `sorry` or added axiom.
- The Lean `Term` type has no role-switch constructor, so none of the
  full-signature results are mechanized yet. The note says this.

## Issues and suggestions

1. **Complexity (cheap corollary of the pair theorem).** A failing valuation in D₂ⁿ
   has polynomial size in n and K, and evaluation is polynomial. So equational
   validity, with K given as part of the input, is in coNP. Hardness is open.
   Boolean structure lives on {b},{c}, but no unary term confines ambiguous inputs
   to singletons, so a reduction needs a different relativization.

2. **The partial-permutation structure is a K=3 artifact.**
   - For general K, a live unary term acts on ambiguous inputs as
     S ↦ C ∪ R[S], where R is the union of the graphs of the permutations in P.
   - Coordinate k is constant exactly when |A_k| ≥ K−1, because a 2-set misses A_k
     only if |A_k| ≤ K−2.
   - At K=3 the variable columns therefore have a single source, which gives
     partial permutations.
   - At K=4, x ∪ (1 2)(x) has A₁ = A₂ = {1,2}. On ambiguous inputs it is not of
     the form F_p for any partial permutation p.
   - The general quotient is therefore a monoid of union-of-permutation relations
     with the columns of size ≥ K−1 truncated into C. Composition of such relations
     stays in the class.
   - Conjecture: the general-K unary classification is (C, truncated R) plus row
     bounds of the same mandatory/excluded shape. Prove that before treating 𝓘_I as
     the governing structure.

3. **Residual bound: a simplification for the reduct.**
   - The reduct generates V(A) = V(C_k : k ∈ I), since A is a subdirect product of
     the C_k and each C_k is a quotient of A.
   - So the reduct's finite-basis question concerns (K+1)-element generators, which
     have 4 elements at K=3.
   - For A^sym the generator is already subdirectly irreducible (7 elements at
     K=3). Sampling quotients of subpowers (`probe_residual.py`) is a fine way to
     explore, but a proof will need structure, e.g. bounding subdirectly irreducible
     subalgebras of powers via the status/provenance description.

4. **Toward an axiomatization.** The normal forms are piecewise by status: each
   variable is either a singleton or ambiguous. Equations cannot split cases
   directly, so any finite basis must simulate the split. The Reset-style
   identities (F(x)⋆_i x, …) show how such splits are internalized.
   Candidate core axioms, all valid:
   - ⋆_r is associative, commutative and idempotent (ACI);
   - ⟨r⟩⋆_r x = ⟨r⟩;
   - π(x⋆_r y) = πx ⋆_{πr} πy;
   - π⟨i⟩ = ⟨πi⟩;
   - the permutation action laws;
   - ⋆_r distributes over the neutral union J;
   - J is independent of its owner triple.

   A first experiment: find which of the 751 unary functions these axioms already
   identify correctly.

5. **Priority of results.** The K=3 classification is the least portable result. The
   pair theorem, provenance and the congruence chain are uniform in K. Lead with
   those, and replace §3 with the general-K statement once point 2 is settled.
