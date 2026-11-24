module

public import KFOL.Complexity.ExplicitOwnerEncoding
public import KFOL.Complexity.TablePeelingWinnerUniform
public import KFOL.Complexity.UniformSourceSpace

/-! # Explicit-table recognition with a binary owner count

The owner count is part of the input for both table formats. Three owners
already suffice for hardness, and every accepted table bounds its owner
count by the number of entries.
-/

@[expose] public section
namespace KFOL.Complexity.ExplicitTableUniform

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity ExplicitOwnerEncoding

abbrev winnerEncoding := encPair encNat AddressedPoint.tableEncoding
abbrev sourceEncoding := encPair encNat AddressedSourceOutput.sourceEncoding

/-- Recognition from the whole winner table, with K supplied in binary. -/
theorem winner_complete :
    PSPACEComplete winnerEncoding TablePeelingWinnerUniform.language := by
  apply complete_binary (L := TablePeelingWinnerUniform.language) (limit := fun x : AddressedPoint.TableInput => x.2.length) _
    (fun _ yes => winner_bound yes.2) (fun _ yes => by have := yes.1; omega)
    TablePeelingWinnerUniform.complete
  exact (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length
    AddressedEnvelope.namesEncoding)).comp (snd encUnary AddressedPoint.menusEncoding)

/-- Recognition from the packed Boolean source table, with K supplied in binary. -/
theorem source_complete :
    PSPACEComplete sourceEncoding UniformSourceSpace.language := by
  apply complete_binary (L := UniformSourceSpace.language) (limit := fun x : ℕ × List Bool => x.2.length) _
    (fun _ ⟨h,yes⟩ => source_bound (Fin.castLEEmb h) yes)
    (fun _ ⟨h,_⟩ => by omega) UniformSourceSpace.complete
  exact length_bits.comp (snd encUnary encBits)

end KFOL.Complexity.ExplicitTableUniform
