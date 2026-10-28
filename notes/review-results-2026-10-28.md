# Review of current results (HEAD fb8c513, 2026-10-28 evening)

Scope:
- research/minimal/: report.tex, Basic.lean, check.py and README;
- the manuscript's rational.tex, the full-strategy part of interpretations.tex, and
  disclosure.tex;
- research/REVIEW_RESPONSE.

This review was done by reading only. Nothing was compiled or run. Every hand
verification below is marked as such.

## Verdict

- **Everything I checked is correct, and the scoping is honest.** The research
  notes, the report and the revised manuscript no longer overclaim.
- **The best material is the finite algebra of possible SPE winners.**
  `research/minimal` gives it a faithful Lean model of full profiles and
  whole-player deviations, a neat neutral-union gadget, and a clean classification
  of unary contexts.
- **The results are still small.** There is no logic yet: no proof system, no
  equational basis, and nothing about contexts with more than one variable.
- **One headline result is weaker than its framing suggests.** "Uniform copies
  suffice" is special to the union gadget. In general, uniform copies give a
  *different* semantics: the singleton-lifted ("Kleisli") one. In that semantics
  the ambiguity structure behind the unary classification disappears (U1 below).
  This is both a correction and the first concrete answer to Target B of the
  proposal.

## research/minimal

**Verified by hand:**
- The recurrence (eq. own) matches my earlier SPE formula: W_i(U) ∪ (L_i(U) if
  every child has an i-losing outcome).
- Neutral union J. I checked all three collapse cases.
- The occurrence lower bound, including the choice j ∉ {r,k}, which needs K ≥ 3.
- The upper bound of the unary classification and the synthesis via g_k and
  suppression by ⋆_i.
- Uniqueness of parameters.
- The count (1+2^{K-1})^K + 2^K − 2, which gives 131, 6575 and 1419887.
- The composition formula for parameters.
- The example D(x), which fixes singletons and sends a multi-winner set S to
  S∪{a,b}.
- The unique-winner collapse, which is a congruence onto a (K+1)-element quotient.
- The comparison with OLV. Def. 3.20 is O_I = 2^I, and (P6) is their distributive
  axiom; I checked both in the PDF.
- The distributivity counterexample.

**The Lean development is faithful.**
- `Profile` is a full profile.
- `Change i` lets i alter every node i owns, in both subtrees.
- `Nash` uses 0/1 utilities.
- `SPE` is Nash at every subtree.
- `spe_node_iff` is the one-shot-deviation lemma, proved from whole-player
  deviations rather than assumed.
- There is no `sorry`, `admit` or added axiom.

**Not in Lean, and stated as such in the report:**
- the decomposition from a term to its path for the lower bound;
- the fold showing that every subset is realized;
- unary synthesis, uniqueness, count and composition.

### U1. Uniform copies: the general statement, and why it matters

Theorem 4.1 is correct, but it is a special case of a one-line generalisation that
cuts the other way.

> For any context f[x] (any number of occurrences of x) and closed G, the winners
> of ordinary SPE profiles that use one fixed full SPE profile of G in every copy
> are exactly ⋃_{g ∈ B(G)} f({g}).

Proof: this is `uniformProfile_spe` generalised. With every copy fixed to an SPE
profile p, local optimality at an outer node depends only on the child winners, so
each copy behaves like the leaf ⟨winner p⟩.

Hence uniform copies preserve B on f exactly when f(S) = ⋃_{s∈S} f({s}) on the
realized inputs. J satisfies this. The report's own D(x) does not:

- Take I = {a,b,c} and G = ⟨a⟩ ⊕_b ⟨c⟩, so B(G) = {a,c}.
- Ordinary B gives D({a,c}) = {a,b,c}. Witness:
  - copy 1 of G yields a, and copy 2 yields c;
  - a takes ⟨b⟩, being indifferent between c and b;
  - b takes its b-winning child;
  - c, indifferent between a and b, takes the right subtree, so b wins.
  - Every node is locally optimal.
- Uniform copies give D({a}) ∪ D({c}) = {a,c}. With both copies yielding c, c takes
  copy 1 at the root. With both yielding a, everything yields a.

Consequences:
- The parameter C in Reg(C,E), together with the remark that "atomic inputs alone
  do not determine a context", depends on the copies of a repeated subterm
  re-solving *independently*.
- Under uniform selection, contexts become ∪-homomorphisms determined by their
  singleton rows. The unary algebra changes and is roughly 2^{K(K−1)} + 2^K − 2 in
  size; I haven't verified that count.
- The proposal's table of three readings of repetition becomes three exact
  semantics:
  - independent copies: B;
  - uniform selection: the singleton lift above;
  - a shared decision with uniform deviations: imperfect information, where the
    hidden-bit example shows existence can fail.
- Two of these three now have closed forms. That comparison is more of a result than
  Theorem 4.1 as it stands. Rewrite §4 around it, and keep J as the positive case
  and D as the separating case.

### U2. Smaller points
- **The lower bound is correct but limited.** As the report says, J uses x only
  inside additive choices, so it says nothing about linear or affine typing.
  "Three binary nodes are optimal" follows from having four leaves.
- **Finite quantifiers add nothing new.** ⋆_r is ACI, so Q_r over a finite A is the
  fold. The k-ary formula in rational.tex is the same operation. Saying so in the
  note closes the gap between quantifier and binary choice. For infinite A at
  finite depth, the k-ary formula still holds classically.
- **The natural next results are missing:**
  1. the binary, and ideally the full, clone of (P₊(I), ⋆_r). Every term function
     is ⊆-monotone, which I checked; that is one invariant relation, but not enough;
  2. whether the equational theory is finitely based. For a finite algebra this is
     not automatic, and here the ⋆_r neither distribute over each other nor absorb;
  3. contexts with two or more variables.

  A finite basis together with a completeness theorem is what would turn this into
  "a logic".
- **The unique-winner collapse is the most conceptually useful fact here.** If only
  "who surely wins" is observable, the semantics collapses to individual
  forceability (OLV), which you rejected. So the intended semantics needs the
  existential "can win in some SPE" observation. The manuscript's intro should
  make this point.

## Manuscript

- **rational.tex**
  - The k-ary formula and the binary operation are correct.
  - The generation proof is correct: for |S| ≥ 3 the owner comes from S∖{s}.
  - Cor. no-Boolean-product is correct. The identity holds for all four meet/join
    pairings, so it holds in every product.
  - This section duplicates the minimal note, and the uniform-copy point (U1) needs
    to reach it as well.
- **interpretations.tex: full strategies.**
  - S_i at an owned choice is A × Π_x S_i(H), matching Escardó–Oliva Def. 4.1 per
    role.
  - The counterexample with the same plan but different SPE status is correct.
    Alice owns x and y; strategy 1 plays y = 0 after x = 1, which is not
    subgame-perfect.
  - It is a textbook example; cite it as one.
- **disclosure.tex: the hiding theorem is correct.**
  - Unmarked cells have types formed in unmarked supports, so their instantiated
    types agree.
  - Marked cells never enter Γ_i.
  - i's own supports lie inside Γ_i, so i's binds are unmarked.
  - The fixed schedule rules out implicit flows.
- **Two caveats on the disclosure section:**
  - Phase preservation inserts c into the middle of a recipient's context. That needs
    strengthening and exchange in D, not only weakening, because the premise forms
    A in the whole Γ_i, not in its prefix. State the requirement.
  - The theorem is standard noninterference with a declassification boundary,
    specialised to straight-line code. Cite Volpano–Smith–Irvine 1996 and
    Sabelfeld–Sands on declassification. The dependent twist (marked cells may have
    different instantiated types in the two runs) is real but small.
- **My earlier suggestion needs correcting.** I proposed hiding "until Pub(c)" from
  audiences alone. The response's copy-and-publish counterexample is right: a
  dependency/release condition is necessary.

## Recommendation

Make research/minimal the paper's centre, and lead with the three-semantics
comparison of repetition from U1. Then attack a finite equational basis, or failing
that the binary clone, for (P₊(I), ⋆_r, ∪). That is the shortest path to an actual
logic of rational owned choice. The dependent and disclosure layers can wait until
the algebra says which structural rules are sound.
