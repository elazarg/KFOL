module

public import KFOL.Complexity.UniformSourceCorrectness
public import KFOL.Complexity.TablePeelingUniform

/-! # Uniform recognition from the complete source table

The verifier guesses the full menu at each listed probe, checks its
prescribed observer bit and asks for a common interpolating word.
A fixed slice with three roles supplies the lower bound.
-/

@[expose] public section
namespace KFOL.Complexity.UniformSourceSpace

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity UniformSourceSamples

def language : Set Input :=
  {x | ∃ h : 3 ≤ x.1, x.2 ∈ AddressedSourceOutput.language (Fin.castLEEmb h)}

/-- The menu certificates have one bit per role and input probe. -/
theorem mem_PSPACE : language ∈ PSPACE sourceEncoding := by
  have sampleSpace : {p : Proof | (p.1.1, samples p) ∈ TablePeelingUniform.language} ∈ PSPACE proofEncoding :=
    PolyTimeReducible.mem_PSPACE ⟨_,((fst _ _).comp (fst sourceEncoding encBits)).prod samples_poly,
      fun _ => Iff.rfl⟩ TablePeelingUniform.mem_PSPACE
  have checkSpace : {p : Proof | consistent p = true} ∈ PSPACE proofEncoding :=
    P_subset_PSPACE ⟨_,consistent_poly,fun _ => Iff.rfl⟩
  convert setOf_exists_mem_PSPACE (inter_mem_PSPACE checkSpace sampleSpace) width_poly using 1
  ext x
  change (∃ h : 3 ≤ x.1, x.2 ∈ AddressedSourceOutput.language (Fin.castLEEmb h)) ↔
    ∃ w, w.length = width x ∧ consistent (x,w) = true ∧
      ∃ h : 3 ≤ x.1, TablePeeling.Accepts (by omega : 0 < x.1) (samples (x,w))
  constructor
  · rintro ⟨h,yes⟩
    obtain ⟨w,len,check,word⟩ := (source_iff_completion x (Fin.castLEEmb h)).mp yes
    exact ⟨w,len,check,h,word⟩
  · rintro ⟨w,len,check,h,word⟩
    exact ⟨h,(source_iff_completion x (Fin.castLEEmb h)).mpr ⟨w,len,check,word⟩⟩

theorem complete : PSPACEComplete sourceEncoding language := by
  refine ⟨mem_PSPACE,(ExplicitSourceHardness.pspaceHard (Fin.castLEEmb (le_refl 3))).trans ?_⟩
  exact ⟨fun x => (3,x),(const 3).prod id',
    fun x => ⟨fun h => ⟨le_refl 3,h⟩, fun ⟨_,h⟩ => h⟩⟩

end KFOL.Complexity.UniformSourceSpace
