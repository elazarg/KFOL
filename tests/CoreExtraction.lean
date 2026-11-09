module

import KFOL.Algorithms.FullTermCode.Core

namespace KFOL.Tests.CoreExtraction
open KFOL.FullTermCode

/-- The original-input extractor is uniformly correct for every binary K,
including physically absent identity arrays and the empty role carrier. -/
example (K name : ℕ) : extractWord (encodeInput ⟨K,.var name⟩) =
    some (encodeInput ⟨K,.var name⟩) := by
  rw [extractWord_encodeInput]
  simp [Term.extractCore?]

example {K : ℕ} (role : Fin K) : extractWord (encodeInput ⟨K,.winner role⟩) = none := by
  rw [extractWord_encodeInput]
  rfl

/-- Accumulated permutation cancellation transports the original choice owner,
retains both variable occurrences, and erases all switch nodes. -/
example {K : ℕ} (p : Equiv.Perm (Fin K)) (owner : Fin K) :
    extractWord (encodeInput ⟨K,.rename p (.choice owner
      (.rename p.symm (.var 0)) (.rename p.symm (.var 1)))⟩) =
      some (encodeInput ⟨K,.choice (p owner) (.var 0) (.var 1)⟩) := by
  rw [extractWord_encodeInput]
  simp [Term.extractCore?]

example : Action.isIdentity none = true := rfl
example : Action.isIdentity (some [0,1,2]) = true := rfl
example : Action.isIdentity (some [1,0,2]) = false := rfl
example : Action.compose (some [1,0,2]) (some [0,2,1]) = some [1,2,0] := rfl
example : Action.compose (some [0,2,1]) (some [1,0,2]) = some [2,0,1] := rfl

example : validArray 3 [0,1,1] = false := rfl
example : validArray 3 [0,1] = false := rfl
example : validArray 3 [0,1,3] = false := rfl

#print axioms extractWord_encodeInput
#print axioms valid_iff

end KFOL.Tests.CoreExtraction
