module

public import KFOL.Equational.Preservation

/-! # Generated subalgebras whose generators lie in a homomorphic range -/

@[expose] public section

namespace KFOL.Equational

universe u v w z

open FirstOrder

variable {σ : ℕ → Type u} {A : Type v} {M : Type w} {N : Type z}
variable [(language σ).Structure A] [(language σ).Structure M] [(language σ).Structure N]

/-- No injectivity of the covering map is needed: its actual range is a
surjective image, and every generated subalgebra of that range is a member. -/
theorem InVariety.generated_of_range (hM : InVariety σ A M)
    (f : M →[language σ] N) (X : Set N)
    (hX : ∀ x ∈ X, x ∈ f.range)
    [Nonempty (Language.Substructure.closure (language σ) X)] :
    InVariety σ A (Language.Substructure.closure (language σ) X) := by
  let ontoRange := f.codRestrict f.range f.mem_range_self
  have onto : Function.Surjective ontoRange := by
    intro x
    obtain ⟨y,hy⟩ := x.property
    exact ⟨y,Subtype.ext hy⟩
  have hR := hM.of_surjective ontoRange onto
  have contained := Language.Substructure.closure_le.mpr hX
  let lift : Language.Substructure.closure (language σ) X →[language σ] f.range := {
    toFun := fun x => ⟨x.val,contained x.property⟩
    map_fun' := by intro n sym args; rfl
    map_rel' := by intro n rel args hrel; exact hrel }
  exact hR.of_injective lift (fun x y h => Subtype.ext (congrArg (fun t : f.range => t.val) h))

end KFOL.Equational
