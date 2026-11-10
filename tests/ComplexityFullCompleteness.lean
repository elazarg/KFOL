module
import KFOL.Complexity.FullCompleteness
namespace KFOL.Tests.ComplexityFullCompleteness
open KFOL KFOL.FullTermCode KFOL.Complexity Turing.MultiTapeTM

-- These are literal binary-word languages, with binary K and explicit arrays.
example : Cslib.Complexity.coNPComplete encBits FullLanguage := FullCompleteness.full_coNPComplete
example : Cslib.Complexity.coNPComplete encBits PublicLanguage := FullCompleteness.public_coNPComplete
example : Cslib.Complexity.coNPComplete encBits CoreLanguage := FullCompleteness.core_coNPComplete
example (K : ℕ) (hK : 3 ≤ K) :
    Cslib.Complexity.coNPComplete (FullHardness.originalEquationEncoding K)
      {e | ∀ v : ℕ → WinnerSet (Fin K), e.1.eval v = e.2.eval v} :=
  FullCompleteness.fixed_full_coNPComplete K hK
example (K : ℕ) (hK : 3 ≤ K) :
    Cslib.Complexity.coNPComplete (FullHardness.originalEquationEncoding K)
      {e | e.1.IsPublic ∧ e.2.IsPublic ∧ ∀ v : ℕ → WinnerSet (Fin K), e.1.eval v = e.2.eval v} :=
  FullCompleteness.fixed_public_coNPComplete K hK
example (K : ℕ) (hK : 3 ≤ K) :
    Cslib.Complexity.coNPComplete (FullHardness.originalEquationEncoding K)
      {e | e.1.IsCore ∧ e.2.IsCore ∧ ∀ v : ℕ → WinnerSet (Fin K), e.1.eval v = e.2.eval v} :=
  FullCompleteness.fixed_core_coNPComplete K hK

-- Array length is checked against binary K; unused enormous carriers are not enumerated.
example : validArray 1000000000 [] = false := rfl
example : validArray 3 [0,0,2] = false := rfl
example : validArray 3 [0,1,3] = false := rfl
example : validArray 3 [2,0,1] = true := rfl
example : FullCounterVerifier.verifier false ([],[]) = true := rfl
example : FullCounterVerifier.sourceOk false (2,(.var 0,.var 0)) = false := rfl
example (values : List ℕ) (padding : List Bool) :
    FullCounterVerifier.decodeWitness (FullCounterVerifier.witnessWord values ++ padding) = some values :=
  FullCounterVerifier.decodeWitness_witnessWord_append values padding
example : FullPublicReduction.check (.func (.winner 1000000000) Fin.elim0) = true := rfl
example : FullCorePredicate.check (.func (.winner 0) Fin.elim0) = false := rfl
example : FullPublicReduction.check (.func (.rename [2,0,1]) (fun _ => .var 0)) = false := rfl
example (word : List Bool) : word ∈ PublicLanguage ↔ FullPublicReduction.reduce word ∈ FullLanguage :=
  FullPublicReduction.reduce_correct word
example (coreOnly : Bool) (word : List Bool)
    (outside : word ∉ (if coreOnly then CoreLanguage else FullLanguage)) :
    ∃ certificate, certificate.length ≤ 16*(word.length+1)^2 ∧
      ∀ padding, FullCounterVerifier.verifier coreOnly (word,certificate ++ padding) = true :=
  FullCounterVerifier.verifier_complete coreOnly word outside

#print axioms FullCompleteness.full_coNPComplete
#print axioms FullCompleteness.public_coNPComplete
#print axioms FullCompleteness.core_coNPComplete
#print axioms FullCompleteness.fixed_full_coNPComplete
#print axioms FullCompleteness.fixed_public_coNPComplete
#print axioms FullCompleteness.fixed_core_coNPComplete
#print axioms FullCounterVerifier.verifier_polyTime
#print axioms FullCounterVerifier.verifier_sound
#print axioms FullCounterVerifier.verifier_complete
end KFOL.Tests.ComplexityFullCompleteness
