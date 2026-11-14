module

public import KFOL.Representation.Cooperations
public import KFOL.Representation.Morphisms
public import KFOL.Core.ModelLaws
public import KFOL.Core.ChoiceUnion.Laws

/-! # Canonical ideal representations of arbitrary winner-variety models

The carrier is an arbitrary model of the identity theory, not necessarily
the finite winner-set generator. The representation recovers all positive
compact elements and preserves each owned operation by its biideal
co-operation.
-/

@[expose] public section

namespace KFOL.IdealDuality

universe u v w z

open FirstOrder

section Reducts

variable {σ : ℕ → Type u} {τ : ℕ → Type v} {A : Type w} {M : Type z}
variable [(Equational.language τ).Structure A] [(Equational.language τ).Structure M]

/-- Identity-theory membership passes along every reduct of languages. -/
theorem inVariety_reduct (φ : Equational.language σ →ᴸ Equational.language τ)
    (hM : Equational.InVariety τ A M) :
    letI := φ.reduct A
    letI := φ.reduct M
    Equational.InVariety σ A M := by
  let _ := φ.reduct A
  let _ := φ.reduct M
  refine ⟨hM.1, ?_⟩
  intro e he ν
  let e' : Equational.Identity τ := ⟨e.arity, φ.onTerm e.lhs, φ.onTerm e.rhs⟩
  have hv : e'.Holds A := by
    intro μ
    change (φ.onTerm e.lhs).realize μ = (φ.onTerm e.rhs).realize μ
    rw [Language.LHom.realize_onTerm, Language.LHom.realize_onTerm]
    exact he μ
  have hm := hM.2 e' hv ν
  change (φ.onTerm e.lhs).realize ν = (φ.onTerm e.rhs).realize ν at hm
  simpa only [Language.LHom.realize_onTerm] using hm

end Reducts

/-- The core operations as symbols of the original full winner language. -/
def coreToFull (Role : Type u) :
    Equational.language (Equational.CoreSymbol Role) →ᴸ
      Equational.language (Equational.FullSymbol Role) where
  onFunction {_} f := match f with | .choice r => .choice r
  onRelation {_} r := nomatch r

/-- The core operations as symbols of the permutation-free public language. -/
def coreToPublic (Role : Type u) :
    Equational.language (Equational.CoreSymbol Role) →ᴸ
      Equational.language (Equational.PublicSymbol Role) where
  onFunction {_} f := match f with | .choice r => .choice r
  onRelation {_} r := nomatch r

section Core

variable {Role : Type u} {M : Type v}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]

attribute [local instance] Equational.coreStructure

/-- Distribution over derived neutral union holds in every abstract core
model by transfer of its actual finite identity. -/
theorem operation_join_right
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (r : Role) (x y z : M) :
    Core.operation r x (Core.join three y z) =
      Core.join three (Core.operation r x y) (Core.operation r x z) := by
  simpa using Core.equation_of_inVariety hM
    (Core.choiceTerm r (.var (0 : Fin 3))
      (Core.unionTerm three (.var 1) (.var 2)))
    (Core.unionTerm three
      (Core.choiceTerm r (.var (0 : Fin 3)) (.var 1))
      (Core.choiceTerm r (.var (0 : Fin 3)) (.var 2)))
    (fun ν => by
      simp only [Core.realize_choice, Core.realize_union, Language.Term.realize_var,
        Core.join_winner, Core.operation_winner]
      exact Dissemilattice.winner_mul_add r (ν 0) (ν 1) (ν 2)) ![x, y, z]

theorem operation_join_left
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (r : Role) (x y z : M) :
    Core.operation r (Core.join three x y) z =
      Core.join three (Core.operation r x z) (Core.operation r y z) := by
  rw [Core.operation_comm hM r, operation_join_right hM three,
    Core.operation_comm hM r z x, Core.operation_comm hM r z y]

/-- An abstract owned choice as a genuine curried mathlib join homomorphism. -/
def modelBimorphism
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (r : Role) :
    letI := Core.modelSemilattice hM three
    SupHom M (SupHom M M) := by
  letI := Core.modelSemilattice hM three
  exact
    { toFun := fun x =>
        { toFun := Core.operation r x
          map_sup' := fun y z => operation_join_right hM three r x y z }
      map_sup' := fun x y => DFunLike.ext _ _ fun z => operation_join_left hM three r x y z }

/-- Every model in the generated core variety has an ideal-lattice
representation recovering its whole carrier and every owned operation. -/
theorem core_model_representation
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := Core.modelSemilattice hM three
    ∃ e : M ≃o PositiveCompact (Ideals M),
      ∀ r x y, reconstruct (canonicalCooperation (modelBimorphism hM three r))
        (e x) (e y) = e (Core.operation r x y) := by
  let _ := Core.modelSemilattice hM three
  exact ⟨principalEquiv, fun r x y =>
    reconstruct_canonicalCooperation (modelBimorphism hM three r) x y⟩

end Core

section Expanded

variable {Role : Type u} {M : Type v}

attribute [local instance] Equational.fullStructure Equational.publicStructure Equational.coreStructure

private theorem full_reduct_winner :
    (coreToFull Role).reduct (WinnerSet Role) = Equational.coreStructure Role := by
  ext n f args
  · cases f
    rfl
  · cases f

private theorem public_reduct_winner :
    (coreToPublic Role).reduct (WinnerSet Role) = Equational.coreStructure Role := by
  ext n f args
  · cases f
    rfl
  · cases f

/-- The abstract core reduct of every full winner model belongs to the
core variety; no HSP certificate or concrete representation is assumed. -/
theorem full_core_inVariety
    [(Equational.language (Equational.FullSymbol Role)).Structure M]
    (hM : Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) M) :
    letI := (coreToFull Role).reduct M
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M := by
  have h := inVariety_reduct (coreToFull Role) hM
  rw [full_reduct_winner] at h
  exact h

/-- The same core representation applies to every model with winner
constants but without internal role renamings. -/
theorem public_core_inVariety
    [(Equational.language (Equational.PublicSymbol Role)).Structure M]
    (hM : Equational.InVariety (Equational.PublicSymbol Role) (WinnerSet Role) M) :
    letI := (coreToPublic Role).reduct M
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M := by
  have h := inVariety_reduct (coreToPublic Role) hM
  rw [public_reduct_winner] at h
  exact h

end Expanded

section Full

variable {Role : Type u} {M : Type v}
variable [(Equational.language (Equational.FullSymbol Role)).Structure M]

attribute [local instance] Equational.fullStructure Equational.coreStructure

local instance fullWinnerExpansion :
    (coreToFull Role).IsExpansionOn (WinnerSet Role) where
  map_onFunction := by
    intro n f args
    cases f
    rfl
  map_onRelation := by intro n r; exact nomatch r

/-- Interpretation of one internal role permutation in an abstract full model. -/
def fullRename (p : Equiv.Perm Role) (x : M) : M :=
  Language.Structure.funMap (L := Equational.language (Equational.FullSymbol Role))
    (.rename p) (fun _ => x)

def renameTerm (p : Equiv.Perm Role)
    (t : Equational.Term (Equational.FullSymbol Role) (Fin 2)) :
    Equational.Term (Equational.FullSymbol Role) (Fin 2) :=
  .func (.rename p) (fun _ => t)

@[simp] theorem realize_renameTerm (p : Equiv.Perm Role)
    (t : Equational.Term (Equational.FullSymbol Role) (Fin 2)) (ν : Fin 2 → M) :
    (renameTerm p t).realize ν = fullRename p (t.realize ν) := rfl

theorem fullRename_winner (p : Equiv.Perm Role) (x : WinnerSet Role) :
    fullRename p x = WinnerSet.rename p x := rfl

/-- Abstract role renaming preserves the derived semilattice join. -/
def modelRename
    (hM : Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) (p : Equiv.Perm Role) :
    letI := (coreToFull Role).reduct M
    letI := Core.modelSemilattice (full_core_inVariety hM) three
    SupHom M M := by
  let _ := (coreToFull Role).reduct M
  let _ := Core.modelSemilattice (full_core_inVariety hM) three
  refine ⟨fullRename p, ?_⟩
  intro x y
  change fullRename p (Core.join three x y) =
    Core.join three (fullRename p x) (fullRename p y)
  let s : Equational.Term (Equational.FullSymbol Role) (Fin 2) :=
    renameTerm p ((coreToFull Role).onTerm (Core.unionTerm three (.var 0) (.var 1)))
  let t : Equational.Term (Equational.FullSymbol Role) (Fin 2) :=
    (coreToFull Role).onTerm (Core.unionTerm three (.var 0) (.var 1)) |>.subst
      (fun i => renameTerm p (.var i))
  have hv : ∀ ν : Fin 2 → WinnerSet Role, s.realize ν = t.realize ν := by
    intro ν
    simp only [s, t, Language.Term.realize_subst, realize_renameTerm,
      Language.LHom.realize_onTerm, Core.realize_union, Language.Term.realize_var,
      Core.join_winner, fullRename_winner]
    exact WinnerSet.rename_union p (ν 0) (ν 1)
  have he := hM.2 ⟨2, s, t⟩ hv ![x, y]
  simpa only [s, t, Language.Term.realize_subst, realize_renameTerm,
    Language.LHom.realize_onTerm, Core.realize_union, Language.Term.realize_var,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

end Full

end KFOL.IdealDuality
