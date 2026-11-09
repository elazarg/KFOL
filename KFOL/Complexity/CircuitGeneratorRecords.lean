module

public import KFOL.Complexity.CircuitRecords

/-! # Canonical reset operation and exact shared-gate implementation records -/

@[expose] public section

namespace KFOL.Complexity.CircuitGenerator

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode
open CircuitMachine

/-- Reset's actual operation alphabet is a singleton, independently of the
number or bit length of source variable names. -/
def resetOperationEquiv : Operation Reset.Symbol ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨2,.reset⟩
  left_inv := by rintro ⟨n,operation⟩; cases operation; rfl
  right_inv := by intro value; cases value; rfl

instance resetOperationFintype : Fintype (Operation Reset.Symbol) :=
  Fintype.ofEquiv Unit resetOperationEquiv.symm

noncomputable abbrev gateEncoding := CircuitMachine.gateEncoding (σ := Reset.Symbol)
noncomputable abbrev equationEncoding := CircuitMachine.dataEncoding (σ := Reset.Symbol)

/-- An original input gate carries its sparse binary name exactly once. -/
def inputGate (name : ℕ) : RawGate Reset.Symbol := (none,(name,[]))

/-- An original reset gate carries two cache references, not unfolded trees. -/
def resetGate (left right : ℕ) : RawGate Reset.Symbol :=
  (some ⟨2,.reset⟩,(0,[left,right]))

@[simp] theorem view_input (name : ℕ) :
    viewGate (Circuit.Gate.input (σ := Reset.Symbol) name) = inputGate name := rfl

@[simp] theorem view_reset (left right : ℕ) :
    viewGate (Circuit.Gate.reset (Var := ℕ) left right) = resetGate left right := by
  simp [viewGate,Circuit.Gate.reset,resetGate,List.ofFn_succ]

theorem inputGate_polyTime : ComputableInPolyTime inputGate encNat gateEncoding :=
  (const none).prod ((id' (encIn := encNat)).prod (const []))

theorem resetGate_polyTime : ComputableInPolyTime (fun p : ℕ × ℕ => resetGate p.1 p.2)
    (encPair encNat encNat) gateEncoding :=
  (const (some (⟨2,.reset⟩ : Operation Reset.Symbol))).prod
    ((const 0).prod (cons' (fst encNat encNat) (cons' (snd encNat encNat) (const []))))

end KFOL.Complexity.CircuitGenerator
