module

public import KFOL.Complexity.ResetUnionSource
public import KFOL.Reductions.ResetUnionCorrectness

/-! # Machine-level coNP hardness of native reset/union equations -/

@[expose] public section

namespace KFOL.Complexity.ResetUnionHardness

open Turing.MultiTapeTM
open KFOL.ResetUnion
open KFOL.Complexity.ResetUnionMachines

/-- The actual CNF construction and imported complete source machine prove
hardness, with no reduction correctness or complexity hypothesis supplied. -/
theorem coNPHard {Role : Type*} (three : Fin 3 ↪ Role) :
    Cslib.Complexity.coNPHard equationEncoding {equation | Valid Role equation} :=
  ResetUnionSource.coNPHard_of_equation_correct
    (fun formula => KFOL.Reductions.ResetUnion.valid_equation_iff three formula)

private theorem language_encode_iff {Role : Type*} (equation : Equation) :
    Code.encodeEquation equation ∈ Language Role ↔ Valid Role equation := by
  constructor
  · rintro ⟨other, he, hv⟩
    exact Code.encodeEquation_injective he ▸ hv
  · intro hv
    exact ⟨equation, rfl, hv⟩

/-- Hardness also holds for the full original binary language, whose
independent definition rejects every malformed equation code. -/
theorem language_coNPHard {Role : Type*} (three : Fin 3 ↪ Role) :
    Cslib.Complexity.coNPHard encBits (Language Role) := by
  apply Cslib.Complexity.coNPHard.trans (coNPHard three)
  refine ⟨Code.encodeEquation, ?_, fun equation => (language_encode_iff equation).symm⟩
  exact ComputableInPolyTime.of_eq (fun _ => rfl)

end KFOL.Complexity.ResetUnionHardness
