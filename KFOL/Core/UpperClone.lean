module

public import KFOL.Core.TypedCover
public import KFOL.Core.Folds

/-! # Canonical inclusion and derived join in rigid upper clones -/

@[expose] public section

namespace KFOL.Core

universe u v w

open FirstOrder

variable {Role : Type u} {M : Type v} {Var : Type w}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]

attribute [local instance] Equational.coreStructure

@[simp] theorem operation_upper (e : M) (r : Role) (x y : Option M) :
    letI := upperStructure (Role := Role) e
    operation r x y = upperChoice e r x y := rfl

/-- The original algebra is a canonical subalgebra of its upper clone. -/
noncomputable def upperInclusion (e : M) :
    letI := upperStructure (Role := Role) e
    M →[Equational.language (Equational.CoreSymbol Role)] Option M := by
  letI := upperStructure (Role := Role) e
  exact {
    toFun := some
    map_fun' := by
      intro n f args
      cases f with
      | choice r => rw [funMap_choice, funMap_choice]; rfl }

@[simp] theorem upperInclusion_apply (e x : M) : upperInclusion (Role := Role) e x = some x := rfl

theorem hom_join {N : Type*} [(Equational.language (Equational.CoreSymbol Role)).Structure N]
    (f : M →[Equational.language (Equational.CoreSymbol Role)] N)
    (three : Fin 3 ↪ Role) (x y : M) : f (join three x y) = join three (f x) (f y) := by
  simp only [join, hom_operation]

@[simp] theorem upper_join_some (e : M) (three : Fin 3 ↪ Role) (x y : M) :
    letI := upperStructure (Role := Role) e
    join three (some x) (some y) = some (join three x y) := by
  let _ := upperStructure (Role := Role) e
  exact (hom_join (upperInclusion e) three x y).symm

@[simp] theorem upper_join_none_lower
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (e : M) (three : Fin 3 ↪ Role) :
    letI := upperStructure (Role := Role) e
    join three none (some e) = none := by
  let _ := upperStructure (Role := Role) e
  simp only [join, operation_upper, upperChoice, operation_idem hM, ite_true]

/-- Equality of the displayed fold's input values is enough to compare
evaluations; no unused-variable assignment is exposed to the conclusion. -/
theorem fold_realize_congr (r : Role)
    (xs : List (Equational.Term (Equational.CoreSymbol Role) Var))
    (last : Equational.Term (Equational.CoreSymbol Role) Var) (v w : Var → M)
    (hlast : last.realize v = last.realize w)
    (hxs : ∀ t ∈ xs, t.realize v = t.realize w) :
    (foldTerm r xs last).realize v = (foldTerm r xs last).realize w := by
  induction xs with
  | nil => exact hlast
  | cons t ts ih =>
    change (choiceTerm r t (foldTerm r ts last)).realize v =
      (choiceTerm r t (foldTerm r ts last)).realize w
    rw [realize_choice, realize_choice, hxs t (by simp), ih (fun t ht => hxs t (by simp [ht]))]

end KFOL.Core
