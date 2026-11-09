module

public import KFOL.Core.UpperClone

/-! # Transporting rigid upper clones along embeddings -/

@[expose] public section

namespace KFOL.Core

universe u v w

open FirstOrder

variable {Role : Type u} {M : Type v} {N : Type w}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]
variable [(Equational.language (Equational.CoreSymbol Role)).Structure N]

/-- An injective homomorphism extends canonically to the upper clones.
Injectivity is used precisely to reflect the absorbing equality at e. -/
noncomputable def upperMap (f : M →[Equational.language (Equational.CoreSymbol Role)] N)
    (hf : Function.Injective f) (e : M) :
    letI := upperStructure (Role := Role) e
    letI := upperStructure (Role := Role) (f e)
    Option M →[Equational.language (Equational.CoreSymbol Role)] Option N := by
  classical
  letI := upperStructure (Role := Role) e
  letI := upperStructure (Role := Role) (f e)
  refine {
    toFun := Option.map f
    map_fun' := ?_ }
  intro n sym args
  cases sym with
  | choice owner =>
    rw [funMap_choice,funMap_choice]
    change Option.map f (upperChoice e owner (args 0) (args 1)) =
      upperChoice (f e) owner (Option.map f (args 0)) (Option.map f (args 1))
    have htest (c : M) : operation owner (f e) (f c) = f e ↔ operation owner e c = e := by
      rw [← hom_operation f]
      exact hf.eq_iff
    cases hx : args 0 <;> cases hy : args 1
    · rfl
    · simp only [upperChoice,Option.map_none,Option.map_some,htest]
      split_ifs <;> simp only [Option.map_none,Option.map_some,hom_operation f]
    · simp only [upperChoice,Option.map_none,Option.map_some,htest]
      split_ifs <;> simp only [Option.map_none,Option.map_some,hom_operation f]
    · simp only [upperChoice,Option.map_some,hom_operation f]

@[simp] theorem upperMap_apply (f : M →[Equational.language (Equational.CoreSymbol Role)] N)
    (hf : Function.Injective f) (e : M) (x : Option M) : upperMap f hf e x = x.map f := rfl

end KFOL.Core
