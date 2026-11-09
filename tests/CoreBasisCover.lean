module

public import KFOL.Core.TypedCover

/-! A concrete instantiation exercises the full generated-cover theorem. -/

@[expose] public section

namespace KFOLTest.CoreCover

open KFOL KFOL.Core FirstOrder

@[instance_reducible] private def unitStructure : (Equational.language (Equational.CoreSymbol (Fin 3))).Structure Unit where
  funMap _ _ := ()
  RelMap r := nomatch r

attribute [local instance] unitStructure Native.structureOf Equational.coreStructure

private def three : Fin 3 ↪ Fin 3 := Function.Embedding.refl _

private theorem unit_mem : Equational.InVariety (Equational.CoreSymbol (Fin 3))
    (WinnerSet (Fin 3)) Unit := ⟨inferInstance, fun _ _ _ => Subsingleton.elim _ _⟩

private def lower : Native.atomicRestriction (∅ : Set (Fin 3)) := by
  refine ⟨.lower, ?_⟩
  constructor
  · intro r he
    cases he
  · change Native.lower ≠ Native.upper
    decide

private def eta : ideal unit_mem three () →[Equational.language (Equational.CoreSymbol (Fin 3))]
    Native.atomicRestriction (∅ : Set (Fin 3)) where
  toFun _ := lower
  map_fun' := by intro n f args; cases f; rfl
  map_rel' := by intro n r; exact nomatch r

private def label : Unit →[Equational.language (Equational.CoreSymbol (Fin 3))]
    Native.atomicRestriction (∅ : Set (Fin 3)) where
  toFun _ := lower
  map_fun' := by intro n f args; cases f; rfl
  map_rel' := by intro n r; exact nomatch r

private def q : Unit →[Equational.language (Equational.CoreSymbol (Fin 3))] Unit where
  toFun := id
  map_fun' := by intro n f args; rfl
  map_rel' := by intro n r; exact nomatch r

example :
    letI := upperStructure (Role := Fin 3) ()
    Equational.InVariety (Equational.CoreSymbol (Fin 3)) (WinnerSet (Fin 3)) (Option Unit) := by
  apply typed_upper_clone_cover three unit_mem ()
    (fun _ _ _ => Subsingleton.elim _ _) (∅ : Set (Fin 3)) (by
      intro h
      have hm : (0 : Fin 3) ∈ (∅ : Set (Fin 3)) := h.symm ▸ Set.mem_univ 0
      exact hm) eta
    (fun c r => by
      change Native.lower = Native.atom r ↔ operation r () c.val ≠ ()
      simp only [reduceCtorEq, false_iff, not_not]) unit_mem q
    (fun x => ⟨x, rfl⟩) label
  intro u hu
  rfl

end KFOLTest.CoreCover
