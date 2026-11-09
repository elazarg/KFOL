module
public import KFOL.Complexity.OwnerObservationFrontend
public import KFOL.Owner.JointObservation
@[expose] public section
namespace KFOLTest.OwnerObservation
open KFOL KFOL.Complexity Turing.MultiTapeTM
-- An owner observes two-owner syntax in P, while full equality is not asserted here.
example : Owner.Language ({0,1} : Finset (Fin 3))
    (fun x y => 0 ∈ x.val ↔ 0 ∈ y.val) ∈ Cslib.Complexity.P encBits :=
  OwnerObservationFrontend.equivalence_language_mem_P (Function.Embedding.refl _) _ 0 (by decide)
example : Owner.Language ({0,1} : Finset (Fin 3))
    (fun x y => 1 ∈ x.val → 1 ∈ y.val) ∈ Cslib.Complexity.P encBits :=
  OwnerObservationFrontend.implication_language_mem_P (Function.Embedding.refl _) _ 1 (by decide)
-- No-owner and one-owner equality share the original full owner-signature codec.
example : Owner.Language (∅ : Finset (Fin 3)) Eq ∈ Cslib.Complexity.P encBits :=
  OwnerObservationFrontend.equality_language_mem_P (Function.Embedding.refl _) _ (by decide)
example : Owner.Language ({0} : Finset (Fin 3)) Eq ∈ Cslib.Complexity.P encBits :=
  OwnerObservationFrontend.equality_language_mem_P (Function.Embedding.refl _) _ (by decide)
-- Guard compilation is exact even when the semantic easy-branch premise fails.
example (term : Owner.Term (Fin 3) ℕ) :
    ((term.compileObservation 2).withOwner false).guards true = term.guards 2 :=
  Owner.Term.guards_compileObservation 2 term
example :
    let equation := Owner.jointObservationEquation (0 : Fin 3) 1
    equation.1.eval (Owner.jointObservationValuation 0 1 2) ≠
      equation.2.eval (Owner.jointObservationValuation 0 1 2) :=
  Owner.joint_observations_separate 0 1 2 (by decide) (by decide) (by decide)
end KFOLTest.OwnerObservation
