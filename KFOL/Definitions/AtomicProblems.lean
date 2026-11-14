module

public import KFOL.Definitions.AtomicDecision
public import KFOL.Definitions.Complexity

/-! # The original binary language of atomic possible-win instances -/

@[expose] public section

namespace KFOL.Problems

/-- A genuine original term has an atomic input valuation allowing the
queried player to win. Malformed words are excluded by the encoding. -/
def atomicPossibleWinLanguage (K : ℕ) (winner : Fin K) : Set (List Bool) :=
  encodedLanguage (fullTermEncoding K) (fun term => term.AtomicPossibleWin winner)

/-- The original public signature excludes internal role permutations. -/
def publicAtomicPossibleWinLanguage (K : ℕ) (winner : Fin K) : Set (List Bool) :=
  encodedLanguage (fullTermEncoding K)
    (fun term => term.IsPublic ∧ term.AtomicPossibleWin winner)

end KFOL.Problems
