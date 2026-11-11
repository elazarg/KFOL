module

public import KFOL.Core.StatusModel
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation

/-! # A kernel-checked coherent family on formal input statuses

The five finite expressions are checked on every assignment of a named atom or
an independent passive marker. The semantic transfer and actual core-term
witnesses are proved in `MinorantFivePatches`.
-/

@[expose] public section

namespace KFOL.Core.FivePatch

open WinnerSet WinnerSet.StatusModel

def formalInput (s : Fin 4) (j : Fin 5) : Value (Fin 3 ⊕ Fin 5) :=
  if h : s.val < 3 then Value.singleton (.inl ⟨s.val, h⟩) else Value.singleton (.inr j)

def formalCandidates (s : Fin 5 → Fin 4) : Fin 5 → Value (Fin 3 ⊕ Fin 5) :=
  let X := formalInput (s 0) 0
  let Y := formalInput (s 1) 1
  let Z := formalInput (s 2) 2
  let W := formalInput (s 3) 3
  let V := formalInput (s 4) 4
  ![(Value.union (Value.union (Value.union (Value.choice (.inl 0) (Value.choice (.inl 2) X W) (Value.choice (.inl 2) Y (Value.union Z V))) (Value.choice (.inl 1) X (Value.choice (.inl 0) V (Value.choice (.inl 1) Z (Value.union Y W))))) (Value.union (Value.choice (.inl 2) X Z) (Value.choice (.inl 1) X (Value.choice (.inl 1) W V)))) (Value.choice (.inl 0) Y (Value.choice (.inl 1) X (Value.choice (.inl 1) V (Value.choice (.inl 2) Z W))))),
    (Value.union (Value.union (Value.union (Value.union (Value.union (Value.choice (.inl 2) Y (Value.union V (Value.choice (.inl 1) Z (Value.union X W)))) (Value.choice (.inl 1) Y (Value.union X (Value.choice (.inl 2) X (Value.union Z W))))) (Value.choice (.inl 2) X (Value.choice (.inl 2) Y (Value.choice (.inl 2) V (Value.choice (.inl 0) Z W))))) (Value.choice (.inl 2) Y (Value.choice (.inl 0) Z (Value.choice (.inl 1) W V)))) (Value.choice (.inl 1) X (Value.choice (.inl 1) Y (Value.choice (.inl 0) Z V)))) (Value.choice (.inl 1) X (Value.choice (.inl 1) Y (Value.choice (.inl 1) W V)))),
    (Value.union (Value.union (Value.union (Value.union (Value.union (Value.union Z (Value.choice (.inl 1) X (Value.choice (.inl 0) Y (Value.choice (.inl 1) Z V)))) (Value.choice (.inl 0) (Value.choice (.inl 1) Z W) (Value.choice (.inl 1) Y (Value.choice (.inl 2) X W)))) (Value.choice (.inl 1) X (Value.choice (.inl 1) W (Value.choice (.inl 1) V (Value.choice (.inl 0) Y Z))))) (Value.choice (.inl 0) Z (Value.choice (.inl 2) Y (Value.choice (.inl 1) W V)))) (Value.choice (.inl 0) Z (Value.choice (.inl 2) X (Value.choice (.inl 2) Y V)))) (Value.choice (.inl 1) (Value.choice (.inl 0) Y X) Z)),
    (Value.union (Value.union (Value.union (Value.union (Value.choice (.inl 0) (Value.choice (.inl 2) Y V) (Value.choice (.inl 2) W (Value.choice (.inl 1) X Z))) (Value.choice (.inl 0) W (Value.choice (.inl 2) (Value.choice (.inl 1) X Y) (Value.union Y Z)))) (Value.choice (.inl 0) (Value.choice (.inl 2) Z W) (Value.choice (.inl 1) X (Value.choice (.inl 1) Y V)))) (Value.choice (.inl 0) (Value.choice (.inl 2) Z W) (Value.choice (.inl 2) X (Value.choice (.inl 2) Y V)))) (Value.choice (.inl 2) (Value.choice (.inl 1) (Value.choice (.inl 0) Y X) Z) W)),
    (Value.union (Value.union (Value.choice (.inl 0) V (Value.union Y (Value.choice (.inl 1) Z (Value.union X W)))) (Value.choice (.inl 2) X (Value.choice (.inl 2) V (Value.union W (Value.choice (.inl 0) Y Z))))) (Value.choice (.inl 1) V (Value.choice (.inl 2) Z (Value.choice (.inl 0) W (Value.choice (.inl 1) X Y)))))]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
theorem formal_coherent : ∀ s : Fin 5 → Fin 4,
    let p := formalCandidates s
    ∃ bad : Fin 5, ∀ i : Fin 5, i ≠ bad → p i = (if p 0 = p 1 then p 0 else p 2) := by
  decide +kernel

end KFOL.Core.FivePatch
