module
public import KFOL.Complexity.OwnerCountCompleteness
@[expose] public section
namespace KFOLTest.OwnerCount
open KFOL KFOL.Complexity Turing.MultiTapeTM
-- The two observed owners have easy individual observations; the third is hard.
example : Cslib.Complexity.coNPComplete encBits
    (Owner.Language ({0,1} : Finset (Fin 3)) Eq) :=
  OwnerCountCompleteness.equality_language_coNPComplete (Function.Embedding.refl _) _ (by decide)
example : Cslib.Complexity.coNPComplete encBits
    (Owner.Language ({0,1} : Finset (Fin 3)) (fun x y => 2 ∈ x.val → 2 ∈ y.val)) :=
  OwnerCountCompleteness.implication_language_coNPComplete _ 2 (by decide)
example : Cslib.Complexity.coNPComplete encBits
    (Owner.Language ({0,1} : Finset (Fin 3)) (fun x y => 2 ∈ x.val ↔ 2 ∈ y.val)) :=
  OwnerCountCompleteness.equivalence_language_coNPComplete _ 2 (by decide)
-- Additional selected owners, including the observer, do not invalidate the lower bound.
example : Cslib.Complexity.coNPComplete encBits
    (Owner.Language (Finset.univ : Finset (Fin 5)) (fun x y => 4 ∈ x.val → 4 ∈ y.val)) :=
  OwnerCountCompleteness.implication_language_coNPComplete _ 4 (by decide)
end KFOLTest.OwnerCount
