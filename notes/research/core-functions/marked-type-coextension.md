# Joint type compatibility: coextension and a fixed-carrier completion law

These are research observations, not a characterization of arbitrary guards.

## Arbitrary marked cotree coextension

Fix a genuine core operation F. Let T_1,...,T_m be any finite family of actual full occurrence-factor types appearing in possibly different terms realizing F. Choose one such marked occurrence in each realizing term. Take ANY owner-colored cotree on m leaves and replace its i-th macro leaf by the corresponding F realizer.

The resulting term still realizes F: all macro subtrees evaluate to F, by idempotence of every owned choice. Each marked occurrence retains its exact full type. Indeed, for any owner q and set E of q-atomic rival inputs, its old factor B_q(E)=true implies that F is not the q singleton at that pure-q probe: the marked source supplies another owner, every other rival factor is true at its empty atomic set, and B_q retains that source. The q-singleton profile depends only on E, so this implication holds at every passive pattern with the same E. Each new macro q-owned sibling evaluates to F, hence adds no filter where B_q was true. Where B_q was false, conjoining extra filters changes nothing.

Consequently the marked occurrences induce exactly the arbitrarily chosen macro cotree coloring. In particular ANY TWO actual full types of F can be connected by ANY owner color in some F representation. A semantic pairwise allowed-edge-color graph on actual types is therefore the complete unrestricted list graph.

This does not rule out a carefully normalized canonical representation. It does rule out obtaining informative forbidden edge colors merely from the fact that a pair of full types coexists in an F term. Even finite induced marked cotree patterns carry no additional obstruction beyond individual realizability of the selected types. Exact/maximal clique obligations and their unmarked companions must remain visible.

## A closed list-color completion law on a fixed carrier

Let O be a fixed finite vertex set. For every unordered pair x,y give a set A_xy of permitted owner colors. There exists a colored cograph/Gurvich cotree on O using only permitted colors iff

    for every S⊆O with |S|≥2, some owner r makes the graph
    on S with edges {x,y} satisfying r∉A_xy disconnected.      (LC)

Necessity follows by restricting a realizing cotree to S: its root splits S into nonempty parts with every crossing edge color r, so no forbidden-r edge crosses those parts.

For sufficiency, induct on |O|. Select r and the connected components of the forbidden-r graph. All crossing pairs permit r. Apply the hereditary condition (LC) to each component, realize it inductively, and join these cotrees under an r root.

Thus once a canonical carrier and pairwise color lists have genuinely been obtained, the graph-completion existential can be removed by a single closed subset condition. The present obstacle is obtaining those lists while retaining maximal-clique semantics and repeated occurrence identifications. The coextension observation above explains why raw full-type pair compatibility does not supply them.
