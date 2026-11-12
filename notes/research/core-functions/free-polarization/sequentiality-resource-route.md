# Sequentiality comparison and a bound on single-cross relations

Research note, 12 November 2026; these results are not yet Lean statements.

## Primary-source check

Pucella–Panangaden, [On the Expressive Power of First-Order Boolean Functions in PCF](https://arxiv.org/html/cs/0405085v1), Definition 3.1 and Proposition 3.2: the relative first-order PCF theorem uses intersections of the indexed presequentiality relations. Preserving the individual indexed relations gives only a coarser inexpressibility invariant. Relative preservation of intersections is stronger because a defining operation may preserve an intersection without preserving its components. This differs from the case of a fixed base known to preserve every component.

Bucciarelli–Leperchey, [Hypergraphs and Degrees of Parallelism: A Completeness Result](https://www.irif.fr/~buccia/HDR/Annexes/C.pdf), Definitions 1–5 and Theorems 9,13: trace hypergraphs capture coherence; timed morphisms retain finite nesting data. Their soundness is general, but completeness assumes subsequentiality. They give a counterexample to unrestricted completeness. Their proof does not remove all presentation witnesses.

These statements do not give a core-clone theorem: PCF supplies constants and conditional tests absent from the idempotent resource-preserving core. No transfer is claimed.

The second paper was read directly from the author-hosted URL.

## A directly proved limitation of elementary resource relations

Let W_K be the nonempty subsets of a K-element owner set, K>=3, with all owned choices. For nonempty proper subsets B_i of W_K, define the m-ary cross

    R(B_1,...,B_m) = { (A_1,...,A_m) : some A_i belongs to B_i }.

**Theorem.** If this cross is preserved by every owned choice, then m<=K.

**Proof.** First every B_i is a subalgebra: apply a chosen owned choice to two tuples whose i-th entries lie in B_i and whose other entries are fixed outside their respective B_j. If the resulting i-th entry left B_i, the output tuple would leave the cross. Thus B_i is closed under all owned choices, hence under derived nonempty union.

Each proper B_i misses at least one singleton. Otherwise closure under union would give B_i=W_K.

An owner r cannot be missed by both B_i and B_j. Choose a in B_i and b in B_j. In the i-th coordinate take the input pair (a,{r}); in the j-th coordinate take ({r},b). Hold every other coordinate at any fixed value outside its B_l. The first tuple belongs to the cross by coordinate i, the second by coordinate j. Owned choice r gives {r} outside B_i and B_j at both selected coordinates, and retains all other outside values by idempotence. It therefore leaves the cross, a contradiction.

Every coordinate misses an owner, and every owner is missed at most once. Hence m<=K. QED.

Dummy full/empty coordinate events can first be removed: a full event makes the relation total; an empty event does not contribute. The bound concerns the remaining nonempty proper events.

Consequently single invariant OR-of-unary-escape relations, and intersections of such individually invariant relations, cannot give a complete schema in the presence of the established unbounded-locality crowns. A resource-preserving sequentiality schema must retain coupled clause families or another genuine branch condition. This does not rule out Sieber-style indexed families whose intersections are invariant even when their components are not.

## Why the coupling matters here

Whole-set inclusion A_i subseteq A_j is invariant because every owned choice is monotone under ordinary set inclusion. Its individual membership implications need not be invariant. With distinct owners r,k,s, take

    first:  i={s},   j={r},
    second: i={k},   j={k}.

Both tuples satisfy 'k in coordinate i implies k in coordinate j'. Choice r gives i={s,k}, j={r}, violating the implication. Their whole-set inclusions do not both hold, so no contradiction to monotonicity occurs.

Thus choosing each clause to be invariant on its own discards valid coupled relations even at arity two.
