module

public import KFOL.Representation.WinnerModels
public import KFOL.Representation.FrameRecovery

/-! # Representation isomorphisms in the original winner signatures

Owned choices on the represented carriers are reconstructed from biideal
co-operations. Winner constants are positive compact points, and internal
renamings are reconstructed from inverse-image maps of ideal lattices.
-/

@[expose] public section

namespace KFOL.IdealDuality

universe u v

open FirstOrder

variable {Role : Type u} {M : Type v}

attribute [local instance] Equational.coreStructure Equational.publicStructure Equational.fullStructure

section Core

variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]

/-- The represented core structure uses the adjoints of its canonical
biideal co-operations for all owned choices. -/
@[instance_reducible] noncomputable def coreFrameStructure
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := Core.modelSemilattice hM three
    (Equational.language (Equational.CoreSymbol Role)).Structure
      (PositiveCompact (Ideals M)) := by
  let _ := Core.modelSemilattice hM three
  exact
    { funMap := fun f args => match f with
        | .choice r => reconstruct (canonicalCooperation (modelBimorphism hM three r))
            (args 0) (args 1)
      RelMap := fun r => nomatch r }

/-- Every abstract core-variety model is isomorphic, in its original
signature, to the positive compact algebra of its canonical ideal lattice. -/
noncomputable def coreRepresentationEquiv
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := Core.modelSemilattice hM three
    letI := coreFrameStructure hM three
    M ≃[Equational.language (Equational.CoreSymbol Role)] PositiveCompact (Ideals M) := by
  let _ := Core.modelSemilattice hM three
  let _ := coreFrameStructure hM three
  exact
    { principalEquiv.toEquiv with
      map_fun' := by
        intro n f args
        cases f with
        | choice r =>
          rw [Core.funMap_choice]
          exact (reconstruct_canonicalCooperation (modelBimorphism hM three r)
            (args 0) (args 1)).symm
      map_rel' := by intro n r; exact nomatch r }

/-- Complete paper-facing representation statement for the core variety. -/
theorem core_variety_representation
    (hM : Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := Core.modelSemilattice hM three
    IsCompactlyGenerated (Ideals M) ∧ Nontrivial (Ideals M) ∧
      (letI := coreFrameStructure hM three
       Nonempty (M ≃[Equational.language (Equational.CoreSymbol Role)]
         PositiveCompact (Ideals M))) := by
  let _ := Core.modelSemilattice hM three
  let _ : Nonempty M := hM.1
  exact ⟨inferInstance, inferInstance, ⟨coreRepresentationEquiv hM three⟩⟩

end Core

section Public

variable [(Equational.language (Equational.PublicSymbol Role)).Structure M]

/-- The public representation additionally names each winner by its
positive compact point. -/
@[instance_reducible] noncomputable def publicFrameStructure
    (hM : Equational.InVariety (Equational.PublicSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := (coreToPublic Role).reduct M
    letI := Core.modelSemilattice (public_core_inVariety hM) three
    (Equational.language (Equational.PublicSymbol Role)).Structure
      (PositiveCompact (Ideals M)) := by
  let _ := (coreToPublic Role).reduct M
  let _ := Core.modelSemilattice (public_core_inVariety hM) three
  exact
    { funMap := fun f args => match f with
        | .winner r => principalEquiv
            (Language.Structure.funMap (L := Equational.language (Equational.PublicSymbol Role))
              (.winner r) Fin.elim0 : M)
        | .choice r => reconstruct
            (canonicalCooperation (modelBimorphism (public_core_inVariety hM) three r))
            (args 0) (args 1)
      RelMap := fun r => nomatch r }

/-- Representation in the signature with winner constants. -/
noncomputable def publicRepresentationEquiv
    (hM : Equational.InVariety (Equational.PublicSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := (coreToPublic Role).reduct M
    letI := Core.modelSemilattice (public_core_inVariety hM) three
    letI := publicFrameStructure hM three
    M ≃[Equational.language (Equational.PublicSymbol Role)] PositiveCompact (Ideals M) := by
  let _ := (coreToPublic Role).reduct M
  let _ := Core.modelSemilattice (public_core_inVariety hM) three
  let _ := publicFrameStructure hM three
  exact
    { principalEquiv.toEquiv with
      map_fun' := by
        intro n f args
        cases f with
        | winner r =>
          have hargs : args = Fin.elim0 := funext fun i => Fin.elim0 i
          rw [hargs]
          rfl
        | choice r =>
          change principalEquiv
              (Language.Structure.funMap
                (L := Equational.language (Equational.CoreSymbol Role)) (.choice r) args) = _
          rw [Core.funMap_choice]
          exact (reconstruct_canonicalCooperation
            (modelBimorphism (public_core_inVariety hM) three r) (args 0) (args 1)).symm
      map_rel' := by intro n r; exact nomatch r }

/-- Complete representation statement with all named winner constants. -/
theorem public_variety_representation
    (hM : Equational.InVariety (Equational.PublicSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := (coreToPublic Role).reduct M
    letI := Core.modelSemilattice (public_core_inVariety hM) three
    IsCompactlyGenerated (Ideals M) ∧ Nontrivial (Ideals M) ∧
      (letI := publicFrameStructure hM three
       Nonempty (M ≃[Equational.language (Equational.PublicSymbol Role)]
         PositiveCompact (Ideals M))) := by
  let _ := (coreToPublic Role).reduct M
  let _ := Core.modelSemilattice (public_core_inVariety hM) three
  let _ : Nonempty M := hM.1
  exact ⟨inferInstance, inferInstance, ⟨publicRepresentationEquiv hM three⟩⟩

end Public

section Full

variable [(Equational.language (Equational.FullSymbol Role)).Structure M]

/-- The full representation reconstructs permutations through their ideal
inverse-image maps, in addition to choices and winner constants. -/
@[instance_reducible] noncomputable def fullFrameStructure
    (hM : Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := (coreToFull Role).reduct M
    letI := Core.modelSemilattice (full_core_inVariety hM) three
    (Equational.language (Equational.FullSymbol Role)).Structure
      (PositiveCompact (Ideals M)) := by
  let _ := (coreToFull Role).reduct M
  let _ := Core.modelSemilattice (full_core_inVariety hM) three
  exact
    { funMap := fun f args => match f with
        | .winner r => principalEquiv
            (Language.Structure.funMap (L := Equational.language (Equational.FullSymbol Role))
              (.winner r) Fin.elim0 : M)
        | .choice r => reconstruct
            (canonicalCooperation (modelBimorphism (full_core_inVariety hM) three r))
            (args 0) (args 1)
        | .rename p => IdealMap.onCompacts (comap (modelRename hM three p)) (args 0)
      RelMap := fun r => nomatch r }

/-- Every model of the full winner variety is represented in its entire
original signature, including constants and internal role permutations. -/
noncomputable def fullRepresentationEquiv
    (hM : Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := (coreToFull Role).reduct M
    letI := Core.modelSemilattice (full_core_inVariety hM) three
    letI := fullFrameStructure hM three
    M ≃[Equational.language (Equational.FullSymbol Role)] PositiveCompact (Ideals M) := by
  let _ := (coreToFull Role).reduct M
  let _ := Core.modelSemilattice (full_core_inVariety hM) three
  let _ := fullFrameStructure hM three
  exact
    { principalEquiv.toEquiv with
      map_fun' := by
        intro n f args
        cases f with
        | winner r =>
          have hargs : args = Fin.elim0 := funext fun i => Fin.elim0 i
          rw [hargs]
          rfl
        | choice r =>
          change principalEquiv
              (Language.Structure.funMap
                (L := Equational.language (Equational.CoreSymbol Role)) (.choice r) args) = _
          rw [Core.funMap_choice]
          exact (reconstruct_canonicalCooperation
            (modelBimorphism (full_core_inVariety hM) three r) (args 0) (args 1)).symm
        | rename p =>
          have hargs : args = fun _ : Fin 1 => args 0 := by
            funext i
            congr 1
            exact Subsingleton.elim _ _
          rw [hargs]
          exact (onCompacts_comap (modelRename hM three p) (args 0)).symm
      map_rel' := by intro n r; exact nomatch r }

/-- Complete representation statement in the full signature: both winner
constants and internal permutations are part of the isomorphism. -/
theorem full_variety_representation
    (hM : Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) M)
    (three : Fin 3 ↪ Role) :
    letI := (coreToFull Role).reduct M
    letI := Core.modelSemilattice (full_core_inVariety hM) three
    IsCompactlyGenerated (Ideals M) ∧ Nontrivial (Ideals M) ∧
      (letI := fullFrameStructure hM three
       Nonempty (M ≃[Equational.language (Equational.FullSymbol Role)]
         PositiveCompact (Ideals M))) := by
  let _ := (coreToFull Role).reduct M
  let _ := Core.modelSemilattice (full_core_inVariety hM) three
  let _ : Nonempty M := hM.1
  exact ⟨inferInstance, inferInstance, ⟨fullRepresentationEquiv hM three⟩⟩

end Full

end KFOL.IdealDuality
