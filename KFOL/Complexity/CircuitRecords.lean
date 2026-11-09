module

public import KFOL.Algorithms.CircuitCode
public import KFOL.Complexity.FiniteTermMachines

/-! Native data records for finite-signature shared circuits. -/

@[expose] public section

namespace KFOL.Complexity.CircuitMachine

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
variable {σ : ℕ → Type} [Fintype (Operation σ)]

/-- Native implementation record. Absent opcode means input; the other fields
then have canonical view (name,[]). Present opcode means (0,refs). -/
abbrev RawGate (σ : ℕ → Type) := Option (Operation σ) × (ℕ × List ℕ)
noncomputable abbrev gateEncoding := encPair (encOption (FiniteTermMachines.operationEncoding (σ := σ)))
  (encPair encNat (encList encNat))

/-- Exact numeric-order view used by the native cached implementation. -/
def viewGate : Circuit.Gate σ ℕ → RawGate σ
  | .input j => (none, (j, []))
  | @Circuit.Gate.func _ _ n symbol refs => (some ⟨n, symbol⟩, (0, List.ofFn refs))


abbrev RawEquation (σ : ℕ → Type) := List (RawGate σ) × (ℕ × ℕ)
noncomputable abbrev dataEncoding :=
  encPair (encList (gateEncoding (σ := σ))) (encPair encNat encNat)

def view (equation : Circuit.Equation σ ℕ) : RawEquation σ :=
  (equation.gates.map viewGate, (equation.left, equation.right))

end KFOL.Complexity.CircuitMachine
