module
import KFOL.Complexity.Canonicalization
import KFOL.Complexity.FullHardnessPublic
import KFOL.Complexity.FullCertificateSize
namespace KFOL.Tests.FullHardness
open Turing.MultiTapeTM
open KFOL.Complexity
open FullHardness

example : Cslib.Complexity.coNPHard encBits FullTermCode.FullLanguage := full_coNPHard
example : Cslib.Complexity.coNPHard encBits FullTermCode.CoreLanguage := core_coNPHard
example : Cslib.Complexity.coNPHard encBits FullTermCode.PublicLanguage := public_coNPHard
example {K : ℕ} (a b d : Fin K) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    Cslib.Complexity.coNPHard (originalEquationEncoding K)
      {e | e.1.IsCore ∧ e.2.IsCore ∧ ∀ v : ℕ → WinnerSet (Fin K), e.1.eval v = e.2.eval v} :=
  fixed_core_coNPHard a b d hab had hbd
example : ofPair (0 : Fin 3) 1 (RawPair.Term.node true (.var 1000000000) (.var 7)) =
    Term.choice 0 (.var 1000000000) (.var 7) := rfl
example : ofPair (0 : Fin 3) 1 (RawPair.Term.node false (.var 7) (.var 7)) =
    Term.choice 1 (.var 7) (.var 7) := rfl
example (t : RawPairMachines.Tree) : (ofPair (0 : Fin 3) 1 t).IsCore := ofPair_isCore _ _ _
example {K : ℕ} (a b : Fin K) : ComputableInPolyTime
    (fun t => (⟨ofPair a b t,ofPair_isCore a b t⟩ : CoreTerm K))
      RawPairMachines.termEncoding (originalCoreTermEncoding K) := ofPair_core_polyTime a b

example {K : ℕ} (a b d : Fin K) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (canonicalize : CoreTerm K → List Bool)
    (runtime : ComputableInPolyTime canonicalize (originalCoreTermEncoding K) encBits)
    (compare : List Bool × List Bool → Bool)
    (comparison : ComputableInPolyTime compare (encPair encBits encBits) encBool)
    (complete : ∀ s t : CoreTerm K, compare (canonicalize s,canonicalize t) = true ↔
      ∀ v : ℕ → WinnerSet (Fin K), s.val.eval v = t.val.eval v) :
    Cslib.Complexity.P encBits = Cslib.Complexity.NP encBits :=
  Canonicalization.original_core_comparator a b d hab had hbd canonicalize runtime compare comparison complete

#print axioms full_coNPHard
#print axioms core_coNPHard
#print axioms Canonicalization.original_core_comparator
end KFOL.Tests.FullHardness
