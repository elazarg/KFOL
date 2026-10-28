# K-player choice logic: assessment and claims

Date: 2026-10-28. Scope: the manuscript in this repo (`main.tex` and its inputs), the prior literature, and new results.
Every computational claim below can be reproduced with the scripts in `notes/checks/` (run `python3 <script>` from that directory).

Notation:
- Players are `[K] = {0,…,K-1}`.
- Leaves `⟨j⟩` mean "player j wins" (one-hot). General-sum leaves `⟨S⟩` mean "the players in S win".
- `G ⊕_i H` means player i chooses between G and H. `P_i x.G` means player i chooses x.
- `π·G` relabels the roles by `π ∈ S_K`.
- The manuscript's prenex form `P_{i1}x1…P_{in}xn.⟨φ_0,…,φ_{K-1}⟩` is a fragment of this language.

---

## 0. Verdict

1. **The core idea is already published.** The idea is to replace ∃/∀ by an unbiased, player-indexed choice quantifier, with negation generalised to role permutation and a viewpoint-dependent ∧/∨ (and Σ/Π) reading.
   - Abramsky (2006) has exactly this syntax, `ϕ ⊕_α ψ | Q_α x.ϕ | π̂(ϕ)` with `π ∈ S(A)`, together with parallel and sequential composition and IF quantifiers.
   - Olde Loohuis & Venema (2010) algebraise the propositional version.
   - Xi & Wu's *multirole logic* (2016–18) is the first-order proof theory: coalition-indexed judgments `[A]_R`, role-indexed connectives and quantifiers, and admissible n-ary cut.
   - Wu & Xi built dependent multiparty session types on it, with "unpolarized quantification interpreted per channel end". That is the Σ/Π-by-viewpoint binder.
   - The manuscript cites none of these. Its novelty claims cannot stand as written.
2. **The manuscript's results.** About ten statements are false as stated (§2.1). The rest are correct but routine. Its forceability semantics is the first-order lift of the Olde Loohuis–Venema semantics.
3. **Forceability cannot be the semantics.** Forcing for a coalition C is a two-player game, C against everyone else. So forceability semantics is classical logic applied separately to each split of the players (§3). Even so, a few genuinely new, fully proved facts come out of it:
   - the value algebra (the free median algebra);
   - a realization theorem;
   - a no-go theorem for symmetric connectives;
   - a collapse of unbiased consequence to equivalence.
4. **Where the gold might be.**
   - (a) A rational-play (backward-induction) semantics (§4.1). It is compositional and S_K-equivariant, and it is classical *exactly* in the indifference-free case (two players, constant-sum). Otherwise it is genuinely non-distributive: move order matters, so prenex form is not without loss of generality. This is the first place where K-player choice gives a non-classical logic *with perfect information*. I found no prior work treating it as a logic. Its equational theory and proof theory are open.
   - (b) Proof theory / Curry–Howard for Abramsky's L_A, by giving multirole logic a game semantics (§4.2).
   - (c) A K-sided λμμ̃, i.e. a computational K-ary cut (§5). I found no prior work.
5. **Type theory.** The direct "CIC-style" version is a conservative extension of CIC (a universe of game codes plus decoding at a coalition). That is excellent for mechanization but not a new type theory. A genuinely new type theory needs interaction or rationality as a primitive, and the dependent+control version must get around Herbelin's Σ-degeneracy (§5).

---

## 1. Prior art (checked against the papers' text)

| Work | What it has | Relation |
|---|---|---|
| Abramsky, "Socially responsive, environmentally friendly logic", in *Truth and Games* (Acta Phil. Fennica 78), 2006, pp. 17–45 | A-indexed `⊕_α` and `Q_α`; negation as role permutation `π̂`, `π ∈ S(A)`; `‖` and `·`; IF quantifiers; concurrent-game semantics (CDS, closure-operator strategies); strategy profiles evaluated to outcomes | **Exact match on the core syntax.** Open problems he lists: proof theory ("a semantics of proofs without a syntax"), compositional valuations and validity, multi-ary cut, descriptive completeness (Q5.1), mixed strategies |
| Tulenheimo & Venema, "Propositional logics for three", 2008 | Three-player propositional logics with transposition or permutation negations | Partial |
| Olde Loohuis & Venema, "Logics and algebras for multiple players", *RSL* 3(3), 2010 | Propositional and modal; `∨_i` (i chooses) and role switches; semantics = which players *individually* have a winning strategy; algebra `O_I = 2^I`; representation theorem; complexity. Observes that Belnap's {∧,∨} logic is their two-player case. Leaves open the "logic of single-winner valuations" and says the extension to quantifiers is "easy" | The manuscript's forceability vector `F` is exactly their semantics |
| Xi & Wu, "Multirole logic" (arXiv:1703.06391) and LMRL (arXiv:1611.08888) | First-order sequent calculus over i-formulas `[A]_R` (R a set of roles); `∧_U`/`∀_U` indexed by ultrafilters (= single roles when finite); negation by *endomorphisms* of the role set; mp-cut over partitions; LMRL ↔ multiparty π-calculus | Purely proof-theoretic; **no semantics found** |
| Wu & Xi, dependent (multiparty) session types (arXiv:1704.07004, 1808.00077) | "Indexed types with unpolarized quantification … types for channel ends obtained by interpreting the quantifiers" (as described by Thiemann & Vasconcelos, POPL 2020) | The Σ/Π-by-viewpoint binder |
| Carbone–Montesi–Schürmann–Yoshida (2015/17); Carbone–Lindley–Montesi–Schürmann–Wadler, "Coherence generalises duality" (CONCUR 2016) | Multiparty coherence generalises duality; multiparty cut | Cooperative; no payoffs |
| Harrenstein et al., *Boolean games* (2001); Bonzon et al. (2006); Gutierrez–Harrenstein–Wooldridge, *Iterated Boolean games* (2013/15) | Players own variables; one goal formula each | The manuscript's game setup, propositional and simultaneous |
| Escardó & Oliva (selection functions; e.g. MSCS 2010); Bolt, Hedges & Zahn, arXiv:1811.06810 | Each move is a generalised quantifier `(X→R)→R`, with ∃/∀ as the two-player Boolean case; products of selection functions compute subgame-perfect plays. BHZ: no nondeterministic selection function computes the *set of SPE plays* | Closest prior art for §4.1. §4.1 is about *outcome* sets, not plays |
| Sevenster & Sandu, equilibrium semantics for IF logic (APAL 2010) | Two-player, mixed strategies, value in [0,1] | No K-player version found |
| Rousseau (1967); Baaz, Fermüller & Zach (1993/94); Hähnle (1993) | Generic n-sided (and signed) sequent calculi for any finite-valued logic | Makes any finite-valued proof theory for §3 routine |
| Herbelin, "On the degeneracy of Σ-types in presence of computational classical logic" (TLCA 2005); Miquey, dL_tp (ESOP 2017) | Dependent Σ with control collapses; one way to restrict it | Obstacle for §5 |

I found nothing on: polyadic orthogonality / K-adic concepts as a realizability semantics; a K-ary λμμ̃; SPE outcome sets as truth values of a logic. These are absences from a ~90-query sweep, not proofs of novelty.

---

## 2. Audit of the manuscript

### 2.1 False as stated

1. **Abstraction base case** (`2FOL.tex`). `Abs_i(φ) := ⟨φ,¬φ⟩` does not depend on i, so `Adv_1(Abs_1(p)) = ¬p ≠ p`. The fix is to put φ in coordinate i.
2. **Canonical-embedding proof** (`appendix-proofs.tex`).
   - It relies on "componentwise game ∧". But `⟨p,¬p⟩ ∧ ⟨q,¬q⟩ = ⟨p∧q, ¬p∧¬q⟩`, so `Adv_1 = ¬p∧¬q ≠ ¬(p∧q)`, which violates condition (2).
   - The core grammar has no Boolean connectives on games anyway.
   - The uniqueness claim is either trivial (syntactic) or false (up to equivalence: you can insert dummy binders).
   - The deeper reason is §3, F5: there is no symmetric ∧. Connectives must be indexed by players.
3. **"Negation under cooperation".** Take `P_0 x.⟨x=1, x=1⟩` over {0,1}. Then `Adv_0(Comp Φ) = ∃x. x≠1` is true while `¬Adv_0(Φ)` is false. (The next remark in the manuscript contradicts it anyway.)
4. **"Comp is the unique … player-symmetric nontrivial involution".** The map swapping `0⃗ ↔ 1⃗` and fixing every other vector is an S_K-equivariant nontrivial involution. The claim holds only for *coordinatewise-uniform* maps.
5. **Implication projection reading** (`algebra.tex`). `∃` over coalition 0's moves can make `α→β` true by falsifying α. With `P_0 x.⟨x=1, ⊥⟩`, the projection `∃x(x=1→⊥)` is true, yet when 0 achieves its goal (x=1), coalition 1 does not succeed.
6. **Lemma "soundness of syntax-directed dependence"** (`solutions.tex`). Take `Φ = P_1 c. P_1 a. ⟨c=1, ⊤⟩`.
   - Position 2 (a) is owned by player 1 and is not in `Rel_Φ(0) = {1}`.
   - Yet a deviation `σ_1'` that changes c changes player 0's outcome.
   - The lemma has to restrict deviations to the given position.
7. **IF binders are defined three incompatible ways.**
   - `P_i x / J`: roles J must not depend on x (forward-looking).
   - `P_i x \ V` in the semantics: σ_i ignores *variables* V (backward-looking, Hintikka–Sandu).
   - The session and dependence sections: V is a set of *roles* that don't receive x (forward-looking).
   - The "perfect recall" standing assumption contradicts slashing one's own earlier moves. Signalling through one's own moves is not addressed.
   - The behavioural-strategy factorisation in `ra.tex` needs perfect recall (Kuhn's theorem), which IF can break.
8. **MPST conjecture.** It equates a *local* type `T(Φ)↾_p` with a *two-party global* type. The two sides are different kinds of object.
9. **Where-clause desugaring.** "Every subformula of j's terminal that depends on x" is undefined. The correct form is relativised quantification / assume-guarantee: in the temporal version, the *first violator loses*.
10. **Clock points are semantically vacuous.** A unit-typed variable carries no information, so `Clk(Φ)` and `Φ` agree under every solution concept.

### 2.2 Correct but routine
- S_K equivariance and its corollaries.
- `Adv_i` is sound for `F_i` under perfect information (Skolemisation; uses AC for infinite domains).
- FOL is a retract (after fix 1); rotation = negation on one-hot games (classical determinacy).
- PSPACE-completeness of the core: this is FO expression complexity.
- IF forceability is NEXPTIME-hard via DQBF. It is in fact NEXPTIME-*complete*: guess the strategy table, check all plays.
- Coalition forceability is PSPACE-*complete*.
- "Forceability ignores information flow" (tensor vs leaky) is true, and more generally *opponents' information never matters for `F_i`*: constant opponent strategies realise every play.

### 2.3 Not yet mathematics
Structural combinators: the "normal form lemma" holds by definition and "block uniformity" is undefined. Also splice laws, the RA view, the crypto appendix, the tests section, and cheap talk. None of these is wrong; none is a result.

---

## 3. Forceability, and why it cannot be *the* semantics

Define `C ⊩ G` as "coalition C can force the winner into C" (general-sum version: "can force *some* member of C to win"). Define the *value* `v(G) : 2^[K] → 2` by `v(G)(C) = [C ⊩ G]`.

**F1 (viewpoint reduction).** With perfect information, `C ⊩ G` iff `M ⊨ G^C`, where G^C is the classical FO formula obtained as follows:
- `P_i ↦ ∃` if `i ∈ C`, else `∀`;
- `⊕_i ↦ ∨` if `i ∈ C`, else `∧`;
- the terminal maps to `⋁_{j∈C} φ_j`;
- `π·G ↦ G^{π⁻¹C}`.

Every forceability notion in the manuscript (individual, coalition, k-redundancy, implication projection) is therefore a classical FO formula. *This is why forcing feels wrong:* it is the ∃/∀ bias applied to each of the 2^{K−1} splits of the players into C and its complement.

**F2 (value algebra).** For one-hot G:
- `v(G)` is monotone and self-dual;
- `v(⟨j⟩) = x_j`;
- `v(G ⊕_i H) = m(x_i, v(G), v(H))`, where m is the ternary median (majority);
- `v(P_i x.G) = ⊕_i{ v(G[a/x]) : a }`, a finite ACI join;
- `v(π·G) = v(G)∘π⁻¹`.

So the values form **FM(K)**: the self-dual monotone Boolean functions on K variables. Equivalently, the free median algebra on K generators, or the constant-sum simple games on K players.
- K=2 gives `{x_0, x_1}`, with `⊕_0 = ∨`, `⊕_1 = ∧`, and `(01) = ¬`: exactly Boolean truth.
- K=3 gives `{x_0, x_1, x_2, maj}`. Here `maj` is the kingmaker value (= von Neumann–Morgenstern's essential 3-person game), e.g. `⟨1⟩ ⊕_0 ⟨2⟩`. Nobody can force alone; any two can.
- General-sum terminals give exactly the monotone f with `f(∅) = 0`: 5, 19 and 167 values for K = 2, 3, 4.
- *Checked:* 0 mismatches against brute-force minimax over 3,200 random trees (K = 2..5, one-hot and general-sum).

**F3 (realization).** Every element of FM(K) is `v(G)` for a finite G built from leaves and `⊕_i` alone.

*Proof.*
1. Post: the self-dual monotone functions form the clone generated by `maj`.
2. Let R be the terms `x_j | m(x_i, R, R)`. R is closed under arbitrary m, by induction on the first argument, using the median law `m(m(a,b,c),d,e) = m(a, m(b,d,e), m(c,d,e))` (checked on {0,1}).
3. By F2, R is exactly the set of game values.

*Checked:* the closure reaches 1, 2, 4, 12, 81, 2646 elements for K ≤ 6, which equals the number of self-dual monotone functions (OEIS A001206).

This answers Olde Loohuis–Venema's open "single-winner" question at the level of the value algebra.
- Their `2^I` value is the restriction of v to singletons. It is a strict quotient for K ≥ 4: `maj(x0,x1,x2)` and `maj(x1,x2,x3)` both have no individual winner.

**F4 (the choice operations are a proper reduct).** For K=3, the median `m(a,b,c)` of *variables* is not a term in `{⊕_i, x_j}`. The search was exhaustive: there are 1013 ternary term operations, and the closure terminates.
- An identity `s≈t` is valid iff for every proper nonempty C the lattice identity `s^C = t^C` holds.
- A finite axiomatization is open.

**F5 (no symmetric connective).** Any S_K-equivariant `f: [K]^n → [K]` is *conservative* (returns one of its arguments) once `K ≥ n+2`.
- *Proof:* f(ā) is fixed by the pointwise stabiliser of {a_1,…,a_n}, whose fixed points are exactly those elements.
- *Checked counts.* Binary: 4 operations for K=2 (π1, π2, ¬π1, ¬π2); 3 for K=3 (adding "the third element"); only the two projections for K ≥ 4. Ternary: 24 operations for K ≥ 5.
- *Consequence:* no unbiased ∧ exists. Connectives must be player-indexed, and only the *family* `{⊕_i}` is unbiased. That vindicates the choice construct as the right primitive.

**F6 (unbiased consequence collapses).**
- Self-dual monotone functions form an antichain. If `f ≤ g`, then `g(C)=1 ⇒ g(C̄)=0 ⇒ f(C̄)=0 ⇒ f(C)=1`, so `g ≤ f`.
- Hence "every coalition that wins A wins B" is just equivalence.
- Any consequence relation is either viewpoint-indexed (biased) or the logic is equational.

**Conjecture F7.** Read `[A]_R` as `R ⊩ A`, with one-hot atoms (the Id axiom over partitions says exactly "some block contains the atom's winner"). Then disjunctive multirole logic with permutation negations is sound and complete for this semantics. Endomorphism negations would be coalition formation, the manuscript's `Co_π`.

---

## 4. Semantics that are not forceability

### 4.1 Rational-play (backward-induction) semantics: the strongest candidate

Each player prefers the outcomes in which they win. Let `SPE(G)` be the set of outcomes of subgame-perfect profiles. Write `W_i(U)` for the outcomes in U where i wins, and `L_i(U)` for those where i loses.

**R1 (compositionality).**
- `SPE(⟨o⟩) = {o}`.
- `SPE(⊕_i(G_a)_a) = W_i(U) ∪ (L_i(U) if L_i(SPE(G_a)) ≠ ∅ for every a)`, where `U = ⋃_a SPE(G_a)`. Quantifiers are the same with a ranging over the domain.
- π acts equivariantly.
- *Checked:* 0 mismatches against brute-force enumeration of subgame-perfect profiles on 1470 random trees (K = 2..4, one-hot and general-sum).
- *Proof idea:* one-shot deviation principle.
- This concerns *outcome* sets with win/lose preferences. BHZ's negative result is about play sets.

**R2 (classical at K=2 constant-sum).** All values are singletons, and `⊕_0 = ∨`, `⊕_1 = ∧`: this is Tarski truth. So R1 is a second conservative generalization of classical logic, *different from forcing*.

**R3 (values).**
- One-hot K ≥ 3: every nonempty set of players occurs as a value (7 for K=3, 15 for K=4; checked).
- Two-player general-sum: 12 values (against 5 under forcing).

**R4 (non-distributivity).** Each `⊕_i` is associative, commutative and idempotent. The law `(a ⊕_i b) ⊕_j c = (a ⊕_j c) ⊕_i (b ⊕_j c)` **fails**:
- **K=3 one-hot, smallest case:**
  - `(⟨0⟩ ⊕_0 ⟨1⟩) ⊕_1 ⟨2⟩ ↦ {0,2}`. Player 1 can't win, so it is indifferent.
  - `(⟨0⟩ ⊕_1 ⟨2⟩) ⊕_0 (⟨1⟩ ⊕_1 ⟨2⟩) ↦ {0,1,2}`. Player 0, indifferent between 1 and 2 winning, may hand the game to 1.
  - Under forcing both sides equal `maj`.
- **K=2 general-sum:** with leaves `⟨{1}⟩, ⟨{0}⟩, ⟨∅⟩`, the left side gives `{0,∅}` and the right side gives `{0,1,∅}`.
- **K=2 constant-sum:** 0 failures.

**Conjecture R4'.** The rational-play algebra is distributive iff no player is ever indifferent between distinct outcomes, i.e. iff K=2 and constant-sum. *Classical logic is the indifference-free case.*

**Consequences.**
- (i) Move order matters, so prenex normal form fails. The manuscript's prenex restriction is a real loss of expressiveness under any rationality semantics.
- (ii) The logic is *not* a product of classical viewpoints. This is the first genuinely non-classical K-player phenomenon with perfect information.

**R5 (relation to forcing).**
- `{j} ⊩ G` implies that player j wins in every SPE outcome.
- Coalition forcing gives no such guarantee. In `⟨1⟩ ⊕_0 ⟨2⟩`, coalition {0,1} can force a win for one of its members, yet 2 ∈ SPE.

**Open, and where the work is:**
- (a) An equational axiomatization of `(values, ⊕_i, π)`.
- (b) Quantifier rules, a proof system, and its completeness.
- (c) A principled choice of solution concept. SPE, Nash (which needs forcing information off the path), "pessimistic" etc. each give a different logic. A canonical candidate is the coarsest compositional semantics refining each.
- (d) Imperfect information, where SPE is not compositional (sequential equilibrium? team semantics?).
- (e) How "j-validity" (j wins in all SPE outcomes in all models) behaves.

### 4.2 Meaning = interaction (Abramsky)
In this approach the meaning of a formula is the game itself, and solution concepts are applied afterwards (the manuscript's "parametric success"). This already exists. The open part is a proof theory.
- **Conjecture:** derivations in multirole logic are coalition winning strategies in Abramsky's games (additive + quantifier fragment), with a full-completeness theorem. This would join Abramsky, Olde Loohuis–Venema and Xi–Wu into one Curry–Howard picture.

---

## 5. Type theory

**What is conservative.** Define `inductive Game` (leaves, `choice i`, `move i (A:Type) (A→Game)`, and `perm`) and `Wins C : Game → Type`, with Σ when the mover is in C, Π otherwise, and ⊤/⊥ at leaves.
- Viewpoint typing, the S_K action (with definitional equations by recursion on codes) and K-ary "play" are then all *definable in CIC/Lean*.
- At K=2 this is proofs and refutations with strong negation as role swap (Nelson-style).
- Unpolarized quantification is in Wu–Xi.
- So this is a *library*, ideal for mechanization, not a new type theory.

**What could be new.**
1. **A K-sided λμμ̃.**
   - K sorts of agents, one per player or coalition, and K-ary commands `⟨t_0|…|t_{K−1}⟩`. β-reduction is broadcast: the mover's pair meets everyone else's λ.
   - `μ_j` lets player j capture the other agents. K-way critical pairs force an evaluation *priority*; K=2 recovers CBN/CBV (Curien–Herbelin).
   - Claims: subject reduction; strong normalization and confluence per priority; S_K conjugates the priority calculi; cut elimination corresponds to multirole logic's mp-cut.
   - I found no prior work.
2. **A dependent version.**
   - Herbelin's Σ-degeneracy already bites at K=2.
   - Target: a K-player analogue of Miquey's dL_tp.
3. **Rationality as typing.**
   - A judgment certifying that a choreography or profile is subgame-perfect: an optimality certificate per node, with projection to endpoints ("deviation-proof choreographies").
   - Related but different: rational verification (Gutierrez–Wooldridge, model checking) and choreographic λ-calculi (Montesi; Hirsch–Garg).
   - Novelty unverified; it fits the blockchain motivation.

---

## 6. Claims ledger (mechanization order)

| ID | Statement | Status |
|---|---|---|
| F1 | Viewpoint reduction (strategy-based ⇔ recursive; AC for infinite domains) | Proof sketch; standard |
| F2 | Value theorem; values = FM(K); K=2 Boolean | Proved; checked K ≤ 5 |
| F3 | Realization of all of FM(K) by finite games | Proved (Post + median law); checked K ≤ 6 |
| F4 | Median not a term for K=3; validity = all nonconstant ∨/∧-colourings | Checked exhaustively (K=3); axiomatization open |
| F5 | Equivariant outcome operations are conservative for K ≥ n+2 | Proved; checked K ≤ 6 |
| F6 | Unbiased forcing consequence = equivalence | Proved |
| F7 | Multirole logic sound and complete for forcing semantics | Conjecture |
| R1 | Compositional SPE outcome sets | Proof idea; checked (1470 trees) |
| R2 | K=2 constant-sum = classical | Proved |
| R3 | Value sets (all nonempty subsets for one-hot K ≥ 3) | Checked K ≤ 4 |
| R4 | Non-distributivity (explicit counterexamples) | Proved by example |
| R4' | Distributive iff indifference-free | Conjecture |
| R5 | Individual forcing ⇒ SPE wins; coalitions don't | Proved |
| T1 | Game codes in CIC are conservative | Routine |
| T2 | K-sided λμμ̃ metatheory | Design needed |

Everything in F1–F6 and R1–R5 is finite or combinatorial and well suited to Lean (`Fin K`, `Finset`, decidable).

---

## 7. Recommendations for the manuscript
- **Reposition it** against Abramsky 2006, Olde Loohuis–Venema 2010, Xi–Wu and Wu–Xi, Boolean games, and Escardó–Oliva.
- **Fix or drop** §2.1.
- **Decide on the semantics.** If forcing, the honest content is F2–F6 (plus F7 if proved). If rational play, §4.1 is the paper.
- **Drop** clocks/megaphones, the RA view, the crypto appendix and the tests section. Keep IF only after fixing its definition.
- **State the prenex restriction** as a real restriction (R4).
