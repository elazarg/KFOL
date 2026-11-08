module

public import KFOL.Equational.Logic

/-! # Identity preservation and equational variety membership -/

@[expose] public section

namespace KFOL.Equational

universe u v w z i

open FirstOrder

variable {σ : ℕ → Type u} {M : Type v} {N : Type w}
variable [(language σ).Structure M] [(language σ).Structure N]

/-- Reflect validity through an injective homomorphism. -/
theorem Identity.holds_of_injective (e : Identity σ) (f : M →[language σ] N)
    (hf : Function.Injective f) (he : e.Holds N) : e.Holds M := by
  intro v
  apply hf
  rw [← Language.HomClass.realize_term f, ← Language.HomClass.realize_term f]
  exact he (f ∘ v)

/-- A surjective homomorphism preserves validity, including nullary identities. -/
theorem Identity.holds_of_surjective (e : Identity σ) (f : M →[language σ] N)
    (hf : Function.Surjective f) (he : e.Holds M) : e.Holds N := by
  intro v
  choose w hw using fun i => hf (v i)
  have hv : f ∘ w = v := funext hw
  have h := congrArg f (he w)
  rw [← Language.HomClass.realize_term f, ← Language.HomClass.realize_term f, hv] at h
  exact h

/-- Subalgebras use mathlib's carrier and restricted operations. -/
theorem Identity.holds_substructure (e : Identity σ) (S : (language σ).Substructure M)
    (he : e.Holds M) : e.Holds S :=
  e.holds_of_injective S.subtype.toHom S.subtype.injective he

/-- Realization in a product is coordinatewise, at arbitrary variable types. -/
theorem realize_product {Var : Type v} {Index : Type i} (A : Index → Type z)
    [∀ j, (language σ).Structure (A j)] (t : Term σ Var)
    (v : Var → ∀ j, A j) (j : Index) :
    letI := productStructure (σ := σ) A
    t.realize v j = t.realize (fun x => v x j) := by
  let _ := productStructure (σ := σ) A
  induction t with
  | var => rfl
  | func f args ih =>
    change Language.Structure.funMap (L := language σ) f (fun k => (args k).realize v j) = _
    congr 1
    exact funext ih

/-- Preservation by arbitrary dependent products, including an empty product. -/
theorem Identity.holds_product (e : Identity σ) {Index : Type i} (A : Index → Type z)
    [∀ j, (language σ).Structure (A j)] (he : ∀ j, e.Holds (A j)) :
    letI := productStructure (σ := σ) A
    e.Holds (∀ j, A j) := by
  let _ := productStructure (σ := σ) A
  change ∀ v : Fin e.arity → (∀ j, A j), e.lhs.realize v = e.rhs.realize v
  intro v
  funext j
  rw [realize_product A, realize_product A]
  exact he j (fun x => v x j)

/-- Theory satisfaction transfers through surjective homomorphisms. -/
theorem Models.of_surjective {T : Theory σ} (f : M →[language σ] N)
    (hf : Function.Surjective f) (h : Models T M) : Models T N :=
  fun e he => e.holds_of_surjective f hf (h e he)

theorem Models.substructure {T : Theory σ} (h : Models T M) (S : (language σ).Substructure M) :
    Models T S := fun e he => e.holds_substructure S (h e he)

/-- A basis must hold in every nonempty model with the generator's identities. -/
theorem InVariety.models {A : Type z} [(language σ).Structure A] {T : Theory σ}
    (h : InVariety σ A M) (hT : Models T A) : Models T M := fun e he => h.2 e (hT e he)

/-- Equational membership is reflexive for nonempty algebras. -/
theorem InVariety.refl [Nonempty M] : InVariety σ M M := ⟨inferInstance, fun _ h => h⟩

theorem InVariety.trans {A : Type z} [(language σ).Structure A]
    (hAM : InVariety σ A M) (hMN : InVariety σ M N) : InVariety σ A N :=
  ⟨hMN.1, fun e he => hMN.2 e (hAM.2 e he)⟩

/-- Nonempty subalgebras of a variety member remain in the variety. -/
theorem InVariety.substructure {A : Type z} [(language σ).Structure A]
    (h : InVariety σ A M) (S : (language σ).Substructure M) [Nonempty S] : InVariety σ A S :=
  ⟨inferInstance, fun e he => e.holds_substructure S (h.2 e he)⟩

/-- Surjective images of a variety member remain nonempty and satisfy its identities. -/
theorem InVariety.of_surjective {A : Type z} [(language σ).Structure A]
    (h : InVariety σ A M) (f : M →[language σ] N) (hf : Function.Surjective f) : InVariety σ A N :=
  ⟨h.1.map f, fun e he => e.holds_of_surjective f hf (h.2 e he)⟩

theorem InVariety.of_injective {A : Type z} [(language σ).Structure A] [Nonempty M]
    (h : InVariety σ A N) (f : M →[language σ] N) (hf : Function.Injective f) : InVariety σ A M :=
  ⟨inferInstance, fun e he => e.holds_of_injective f hf (h.2 e he)⟩

/-- Coordinatewise products of variety members remain in the variety. -/
theorem InVariety.product {A : Type z} [(language σ).Structure A]
    {Index : Type i} (B : Index → Type w) [∀ j, (language σ).Structure (B j)]
    (h : ∀ j, InVariety σ A (B j)) :
    let _ := productStructure (σ := σ) B
    InVariety σ A (∀ j, B j) := by
  let _ := productStructure (σ := σ) B
  let _ : ∀ j, Nonempty (B j) := fun j => (h j).1
  exact ⟨inferInstance, fun e he => e.holds_product B (fun j => (h j).2 e he)⟩

end KFOL.Equational
