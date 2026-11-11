module

public import KFOL.Core.StatusModel
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation

/-! # Six coherent core patches on formal input statuses

The finite certificate records five-of-six agreement and the first patch's
containment in the common value. `FivePointInterpolation` connects these
computable expressions to actual core terms and arbitrary role sets.
-/

@[expose] public section

namespace KFOL.Core.SixPatch

open WinnerSet WinnerSet.StatusModel

def candidates {α : Type*} [DecidableEq α] (owners : Fin 3 → α)
    (v : Fin 5 → Value α) : Fin 6 → Value α :=
  let X := v 0
  let Y := v 1
  let Z := v 2
  let W := v 3
  let V := v 4
  ![(Value.union (Value.union (Value.choice (owners 1) (Value.choice (owners 1) (Value.choice (owners 0) (Value.choice (owners 1) X V) Y) W) V) (Value.choice (owners 2) (Value.union (Value.choice (owners 1) (Value.choice (owners 2) X Y) W) (Value.choice (owners 2) (Value.choice (owners 1) X W) Y)) Z)) (Value.choice (owners 2) (Value.union (Value.choice (owners 2) (Value.choice (owners 0) (Value.union Y V) W) V) (Value.choice (owners 2) (Value.choice (owners 1) Y W) (Value.union Z V))) X)),
    (Value.union (Value.union (Value.choice (owners 1) (Value.union (Value.union (Value.choice (owners 1) (Value.union (Value.union (Value.union (Value.choice (owners 0) X Y) (Value.choice (owners 0) (Value.choice (owners 0) X Y) Z)) (Value.choice (owners 2) Y Z)) Y) V) (Value.choice (owners 2) (Value.choice (owners 0) (Value.choice (owners 1) Y Z) X) V)) (Value.choice (owners 2) (Value.choice (owners 0) X Z) V)) W) (Value.choice (owners 2) (Value.union (Value.choice (owners 2) X V) (Value.choice (owners 2) Z W)) Y)) (Value.choice (owners 2) Z W)),
    (Value.union (Value.union (Value.choice (owners 1) (Value.union (Value.union (Value.choice (owners 0) (Value.choice (owners 1) (Value.union Z V) Y) X) (Value.choice (owners 1) (Value.union (Value.choice (owners 0) X Z) V) X)) (Value.choice (owners 2) X Y)) W) (Value.choice (owners 2) (Value.choice (owners 2) (Value.choice (owners 1) Y W) (Value.union Z V)) X)) (Value.choice (owners 2) (Value.union (Value.choice (owners 1) (Value.choice (owners 2) X Y) W) (Value.choice (owners 2) (Value.choice (owners 1) X W) Y)) Z)),
    (Value.union (Value.union (Value.union (Value.choice (owners 1) (Value.union (Value.choice (owners 1) (Value.choice (owners 0) X Y) (Value.union W V)) (Value.choice (owners 1) (Value.choice (owners 0) (Value.choice (owners 0) X Y) Z) Y)) W) (Value.choice (owners 2) (Value.choice (owners 1) (Value.choice (owners 2) X W) Y) Z)) (Value.choice (owners 2) (Value.choice (owners 1) Y W) (Value.union (Value.choice (owners 2) X V) Z))) (Value.choice (owners 2) (Value.choice (owners 2) (Value.union (Value.choice (owners 2) W V) Z) X) Y)),
    (Value.union (Value.union (Value.union (Value.choice (owners 1) (Value.union (Value.choice (owners 1) (Value.union (Value.choice (owners 0) (Value.choice (owners 1) X V) Y) (Value.choice (owners 1) (Value.choice (owners 0) (Value.choice (owners 0) X Y) Z) Y)) W) (Value.choice (owners 2) (Value.choice (owners 2) (Value.union X Y) Y) Z)) V) (Value.choice (owners 2) (Value.choice (owners 1) (Value.choice (owners 2) X Y) (Value.choice (owners 2) X W)) Z)) (Value.choice (owners 2) (Value.choice (owners 1) (Value.choice (owners 2) X Y) W) (Value.union Z V))) (Value.choice (owners 2) (Value.union (Value.union (Value.choice (owners 0) (Value.choice (owners 1) Y Z) X) (Value.choice (owners 0) (Value.union (Value.choice (owners 2) Y W) Z) X)) (Value.choice (owners 2) Y W)) V)),
    (Value.union (Value.union (Value.union (Value.choice (owners 1) (Value.choice (owners 1) (Value.choice (owners 0) X Y) (Value.union Z V)) W) (Value.choice (owners 2) (Value.choice (owners 2) (Value.choice (owners 1) X W) (Value.union X Y)) Z)) (Value.choice (owners 2) (Value.choice (owners 2) (Value.union Y W) X) V)) Z)]

def formalCandidates (s : Fin 5 → Fin 4) : Fin 6 → Value (Fin 3 ⊕ Fin 5) :=
  candidates Sum.inl (fun j => formalInput (s j) j)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 50000000 in
theorem formal_certificate : ∀ s : Fin 5 → Fin 4,
    let p := formalCandidates s
    (∃ bad : Fin 6, ∀ i : Fin 6, i ≠ bad → p i = (if p 0 = p 1 then p 0 else p 2)) ∧
      (p 0).val ⊆ (if p 0 = p 1 then p 0 else p 2).val := by
  decide +kernel

end KFOL.Core.SixPatch
