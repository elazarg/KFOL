module
public import KFOL.Complexity.RawSubsignatureCompleteness
public import KFOL.Complexity.RawResetFrontend
@[expose] public section
namespace KFOLTest.ComplexityRawSubsignature
open KFOL KFOL.Complexity Turing.MultiTapeTM
private def selected : Finset (Raw.Operation (Fin 3)) := {.reset, .union, .choice 0, .choice 1}
example : 1 < selected.card := by decide
example : Cslib.Complexity.coNPComplete encBits (Raw.Language selected) :=
  RawSubsignatureCompleteness.language_coNPComplete selected (Function.Embedding.refl (Fin 3)) (by decide)
example {Role : Type} (signature : Finset (Raw.Operation Role)) (three : Fin 3 ↪ Role)
    (hcard : 1 < signature.card) : Cslib.Complexity.coNPHard encBits (Raw.Language signature) :=
  RawSubsignatureCompleteness.language_coNPHard signature three hcard
example {Role : Type} (signature : Finset (Raw.Operation Role))
    (operations : Bool → {op // op ∈ signature}) : ComputableInPolyTime
    (Raw.Term.ofRawPair operations) RawPairMachines.termEncoding (RawSubsignatureMachines.termEncoding signature) :=
  RawSubsignatureMachines.ofRawPair_polyTime signature operations
example {Role : Type} (signature : Finset (Raw.Operation Role)) (hr : Raw.Operation.reset ∈ signature)
    (hu : Raw.Operation.union ∈ signature) : ComputableInPolyTime
    (Raw.Reduction.resetUnion signature hr hu) RawPairMachines.cnfEncoding (RawSubsignatureMachines.equationEncoding signature) :=
  RawSubsignatureMachines.resetUnion_polyTime signature hr hu
-- All structurally distinct positive cases, including the empty signature.
example (signature : Finset (Raw.Operation (Fin 3))) (small : signature.card ≤ 1) :
    Raw.Language signature ∈ Cslib.Complexity.P encBits :=
  RawResetFrontend.small_signature_language_mem_P signature (Function.Embedding.refl _) small
example : Raw.Language (∅ : Finset (Raw.Operation (Fin 3))) ∈ Cslib.Complexity.P encBits :=
  RawResetFrontend.small_signature_language_mem_P _ (Function.Embedding.refl _) (by decide)
example (r : Fin 3) : Raw.Language {.choice r} ∈ Cslib.Complexity.P encBits :=
  RawResetFrontend.small_signature_language_mem_P _ (Function.Embedding.refl _) (by simp)
example : Raw.Language ({.union} : Finset (Raw.Operation (Fin 3))) ∈ Cslib.Complexity.P encBits :=
  RawResetFrontend.small_signature_language_mem_P _ (Function.Embedding.refl _) (by decide)
example : Raw.Language ({.reset} : Finset (Raw.Operation (Fin 3))) ∈ Cslib.Complexity.P encBits :=
  RawResetFrontend.small_signature_language_mem_P _ (Function.Embedding.refl _) (by decide)
end KFOLTest.ComplexityRawSubsignature
