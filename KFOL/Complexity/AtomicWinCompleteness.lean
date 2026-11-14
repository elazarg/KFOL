module

public import KFOL.Definitions.AtomicProblems
public import KFOL.Complexity.AtomicWinHardness
public import KFOL.Complexity.AtomicWinWordVerifier
public import KFOL.Complexity.AtomicWinPublic

/-! # Exact NP completeness for the original atomic possible-win problem -/

@[expose] public section

namespace KFOL.Complexity.AtomicWin

theorem npComplete {K : ℕ} (a b : Fin K) (different : a ≠ b) :
    Cslib.Complexity.NPComplete (Problems.fullTermEncoding K)
      {term | term.AtomicPossibleWin a} :=
  ⟨AtomicWinVerifier.atomicPossibleWin_mem_NP a, AtomicWinHardness.npHard a b different⟩

/-- Completeness includes malformed-word rejection and actual explicit-array
input codes, not a promise about Boolean-valued output or valid encodings. -/
theorem language_npComplete {K : ℕ} (a b : Fin K) (different : a ≠ b) :
    Cslib.Complexity.NPComplete Turing.MultiTapeTM.encBits
      (Problems.atomicPossibleWinLanguage K a) :=
  ⟨AtomicWinVerifier.wordLanguage_mem_NP a, AtomicWinHardness.encoded_npHard a b different⟩

theorem language_npComplete_of_two {K : ℕ} (two : 2 ≤ K) (winner : Fin K) :
    Cslib.Complexity.NPComplete Turing.MultiTapeTM.encBits
      (Problems.atomicPossibleWinLanguage K winner) := by
  let _ : Nontrivial (Fin K) := Fin.nontrivial_iff_two_le.mpr two
  obtain ⟨other, different⟩ := exists_ne winner
  exact language_npComplete winner other different.symm

theorem public_language_mem_P {K : ℕ} (winner : Fin K) :
    Problems.publicAtomicPossibleWinLanguage K winner ∈
      Cslib.Complexity.P Turing.MultiTapeTM.encBits :=
  AtomicWinPublic.wordLanguage_mem_P winner

end KFOL.Complexity.AtomicWin
