module

import KFOL.Complexity.CoreExtractionWord

namespace KFOL.Tests.CoreExtractionNative
open Turing.MultiTapeTM
open KFOL.FullTermCode

/-- Complete actual original-input machine and semantic boundary. K and all
sparse names are binary; every occurring permutation is an explicit array. -/
theorem uniform_checked_extraction :
    ComputableInPolyTime extractWord encBits (encOption encBits) ∧
    ∀ input : Input, extractWord (encodeInput input) =
      (input.2.extractCore? 1).map (fun core => encodeInput ⟨input.1,core⟩) :=
  ⟨KFOL.Complexity.CoreExtraction.extractWord_polyTime,extractWord_encodeInput⟩

/-- Neither the native validation certificate nor complete extraction
introduces a fixed K or an uncharged permutation-group enumeration. -/
example : ComputableInPolyTime (fun p : ℕ × Raw => valid p.1 p.2)
    (encPair encNat KFOL.Complexity.FullTermMachines.termEncoding) encBool :=
  KFOL.Complexity.CoreExtraction.valid_polyTime

example (K name : ℕ) : extractWord (encodeInput ⟨K,.var name⟩) =
    some (encodeInput ⟨K,.var name⟩) := by
  rw [extractWord_encodeInput]
  simp [Term.extractCore?]

#print axioms uniform_checked_extraction
#print axioms KFOL.Complexity.CoreExtraction.annotation_encoding_bound

end KFOL.Tests.CoreExtractionNative
