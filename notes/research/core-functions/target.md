# Characterization target — unresolved

The goal is a short structural characterization of the jointly realizable
canonical source guards, comparable to the closed monotonicity and
common-source conditions for singleton profiles.

The recursive row-deletion theorem is a correct recognition procedure. It
does not settle that goal. It reduces full-value interpolation to repeated
singleton-profile tests; it does not replace the recursion by closed structural
conditions. The main discussion and verification appendix must preserve this
distinction.

## Concrete next question: finite relatedness

Fix K ≥ 3 and let A_K be the nonempty subsets of the K roles, with owned
choice operations. Let C_K be their term clone, and let L_m(f) mean that,
for every tuple of m valuations, some core term agrees with f on all of them.
Valuations may repeat. The existing finite-interpolation theorem identifies
L_m(f) with preservation of every invariant m-ary relation.

The question is whether

    ∃ m ≥ 1, ∀ n ≥ 1, ∀ f : A_K^n → A_K, L_m(f) ⇒ f ∈ C_K.

The bound may depend on K; it must not depend on n. A positive answer can be
proved by an explicit finite relational basis and a completeness argument.
A negative answer requires

    ∀ m ≥ 1, ∃ n ≥ 1, ∃ f : A_K^n → A_K,
      L_m(f) and f ∉ C_K.

Increasing K with m does not prove a negative answer for any fixed K. A
counterexample at locality six, or at any other single locality, does not
prove a negative answer either. A construction for K=3 does not automatically
transfer to larger carriers: finite relatedness need not pass to subalgebras.
A uniform family of coherent core patches using three named owners would
supply such a transfer if its coherence is proved for arbitrary additional
passive values.

The current theorem `Core.exists_five_local_obstruction` rules out locality
five for every role type containing three distinct roles. The stronger
`Core.exists_five_local_profile_fiber_nonconvex` also fixes the singleton
profiles and core lower/upper bounds. Neither theorem quantifies over all m.

Finite relatedness is a concrete part of the characterization question. A
negative answer rules out every characterization by a fixed finite family of
invariant relations, but does not rule out all possible short structural laws
with unbounded quantification.

## Identification-minor route

A useful equivalent criterion asks whether sufficiently high-arity operations
whose every variable-identification minor is a term operation are themselves
term operations. For arities larger than |A_K|, every input tuple has repeated
values, so a consistent family of such minors determines the operation.
The unresolved issue is whether these compatible local term representations
can be glued to one term.

Primary references for this criterion are Peter Mayr, *On finitely related
semigroups*, Lemma 2.1
(https://doi.org/10.1007/s00233-012-9455-6), and Daniel Glasson,
*Finitely and non-finitely related words*, Theorem 2.1
(https://doi.org/10.1007/s00233-024-10452-8). The semigroup-specific conclusions
of those papers do not apply to the core without a separate argument.
