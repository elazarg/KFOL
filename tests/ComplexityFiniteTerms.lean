module

public import KFOL.Complexity.FiniteTermMachines

/-! Finite-signature tree boundary checks, including constants and ternary nodes. -/

@[expose] public section

namespace KFOLTest.ComplexityFiniteTerms

open KFOL
variable {σ : ℕ → Type} [Fintype (FiniteTermCode.Operation σ)]

example (operation : FiniteTermCode.Operation σ) :
    operation.1 ≤ FiniteTermCode.maxArity σ := FiniteTermCode.arity_le_maxArity operation

example (constant : σ 0) :
    FiniteTermCode.decode σ (FiniteTermCode.encode σ (.func constant Fin.elim0)) =
      some (.func constant Fin.elim0) := FiniteTermCode.decode_encode _

example (ternary : σ 3) (children : Fin 3 → Equational.Term σ ℕ) :
    FiniteTermCode.decode σ (FiniteTermCode.encode σ (.func ternary children)) =
      some (.func ternary children) := FiniteTermCode.decode_encode _

example (ternary : σ 3) (children : Fin 3 → Equational.Term σ ℕ) :
    FiniteTermCode.encode σ (.func ternary children) = true ::
      (Words.delimit (FiniteTermCode.encodeOperation σ ⟨3, ternary⟩) ++
        (List.ofFn (fun i => FiniteTermCode.encode σ (children i))).flatten) := rfl

example : FiniteTermCode.decode σ [] = none := by
  simp [FiniteTermCode.decode, FiniteTermCode.parse]

example : FiniteTermCode.decode σ [true] = none := by
  simp [FiniteTermCode.decode, FiniteTermCode.parse, Words.unpair?]

example : FiniteTermCode.decode σ [false] = none := by
  simp [FiniteTermCode.decode, FiniteTermCode.parse, Words.unpair?]

example (term : Equational.Term σ ℕ) {word : List Bool}
    (h : FiniteTermCode.decode σ word = some term) :
    FiniteTermCode.encode σ term = word := FiniteTermCode.encode_of_decode h

open Turing.MultiTapeTM

example : ComputableInPolyTime
    (fun p : FiniteTermCode.Operation σ × List (Equational.Term σ ℕ) =>
      Complexity.FiniteTermMachines.construct p.1 p.2)
    (encPair Complexity.FiniteTermMachines.operationEncoding
      (encList Complexity.FiniteTermMachines.termEncoding))
    Complexity.FiniteTermMachines.termEncoding :=
  Complexity.FiniteTermMachines.construct_polyTime

end KFOLTest.ComplexityFiniteTerms
