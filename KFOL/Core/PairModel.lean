module

public import KFOL.Core.ModelLaws

/-! # Two-factor core models and their projections -/

@[expose] public section

namespace KFOL.Core

universe u v w z

open FirstOrder

variable {Role : Type u} {M : Type v} {N : Type w}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]
variable [(Equational.language (Equational.CoreSymbol Role)).Structure N]

@[instance_reducible] def pairStructure :
    (Equational.language (Equational.CoreSymbol Role)).Structure (M × N) where
  funMap f args :=
    (Language.Structure.funMap f (fun i => (args i).1),
      Language.Structure.funMap f (fun i => (args i).2))
  RelMap r := nomatch r

attribute [local instance] pairStructure

theorem operation_pair (r : Role) (x y : M × N) :
    operation r x y = (operation r x.1 y.1, operation r x.2 y.2) := by
  change (Language.Structure.funMap _ (fun i => (if i = 0 then x else y).1),
    Language.Structure.funMap _ (fun i => (if i = 0 then x else y).2)) = _
  simp only [funMap_choice]
  rfl

def fstHom : M × N →[Equational.language (Equational.CoreSymbol Role)] M where
  toFun := Prod.fst
  map_fun' := by intro n f args; rfl
  map_rel' := by intro n r; exact nomatch r

def sndHom : M × N →[Equational.language (Equational.CoreSymbol Role)] N where
  toFun := Prod.snd
  map_fun' := by intro n f args; rfl
  map_rel' := by intro n r; exact nomatch r

theorem pair_inVariety
    (hM : letI := Equational.coreStructure Role
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (hN : letI := Equational.coreStructure Role
      Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) N) :
    letI := Equational.coreStructure Role
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) (M × N) := by
  let _ := Equational.coreStructure Role
  have : Nonempty M := hM.1
  have : Nonempty N := hN.1
  refine ⟨inferInstance, ?_⟩
  intro e he v
  apply Prod.ext
  · have hs (t : Equational.Term (Equational.CoreSymbol Role) (Fin e.arity)) :=
      Language.HomClass.realize_term (fstHom (Role := Role) (M := M) (N := N)) (t := t) (v := v)
    change fstHom (Role := Role) (M := M) (N := N) (e.lhs.realize v) =
      fstHom (Role := Role) (M := M) (N := N) (e.rhs.realize v)
    rw [← hs e.lhs, ← hs e.rhs]
    exact hM.2 e he (Prod.fst ∘ v)
  · have hs (t : Equational.Term (Equational.CoreSymbol Role) (Fin e.arity)) :=
      Language.HomClass.realize_term (sndHom (Role := Role) (M := M) (N := N)) (t := t) (v := v)
    change sndHom (Role := Role) (M := M) (N := N) (e.lhs.realize v) =
      sndHom (Role := Role) (M := M) (N := N) (e.rhs.realize v)
    rw [← hs e.lhs, ← hs e.rhs]
    exact hN.2 e he (Prod.snd ∘ v)

end KFOL.Core
