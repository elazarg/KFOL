/- The singleton/ambiguity quotient: reset comparison and a four-variable
near-unanimity term for three owners. The arbitrary-K veto construction,
explicit atomic basis, and canonical ideal quotients are written proofs. -/
import CoreObstruction
import Reset

set_option autoImplicit false
namespace MinimalChoice.CoreAtomic
open CoreObstruction ResetCalculus

theorem reset_comm_iff {α : Type} (X Y : S α) :
    reset X Y = reset Y X ↔ (Multiple X ∧ Multiple Y) ∨ X = Y := by
  classical
  constructor
  · intro h
    have hs : Multiple X ↔ Multiple Y := by
      have he : Multiple (reset Y X) ↔ Multiple (reset X Y) := by rw [h]
      simpa only [reset_multiple] using he
    by_cases hx : Multiple X
    · exact Or.inl ⟨hx, hs.mp hx⟩
    · have hy : ¬ Multiple Y := fun hy => hx (hs.mpr hy)
      exact Or.inr (by simpa [reset, hx, hy] using h.symm)
  · rintro (⟨hx, hy⟩ | h)
    · simp only [reset, hx, hy, ↓reduceIte]
      funext i
      apply propext
      exact Or.comm
    · rw [h]

def veto : List Player → List (CoreTerm (Fin 4)) → CoreTerm (Fin 4)
  | [], leaves => leaves.headD (.input 0)
  | r :: rs, leaves =>
    let branches := (List.range leaves.length).map (fun j => veto rs (leaves.eraseIdx j))
    match branches with
    | [] => .input 0
    | t :: ts => ts.foldl (fun u v => .node r u v) t

def nu4 : CoreTerm (Fin 4) :=
  veto [.a, .b, .c] [.input 0, .input 1, .input 2, .input 3]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem near_unanimity (x y : Marker) (hx : x ≠ .p) (hy : y ≠ .p)
    (j : Fin 4) : nu4.marker (fun k => if k = j then y else x) = x := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl | rfl | rfl <;> cases x <;> cases y <;>
    (first | exact False.elim (hx rfl) | exact False.elim (hy rfl) | decide)

def markerReset (x y : Marker) : Marker :=
  [.a, .b, .c].foldl (fun z r => Marker.own r z y) (Marker.join x y)

theorem flat_reset (x y : Marker) (hx : x ≠ .p) (hy : y ≠ .p) :
    markerReset x y = y := by
  cases x <;> cases y <;>
    (first | exact False.elim (hx rfl) | exact False.elim (hy rfl) | decide)

def winnerReset (x y : Winner) : Winner :=
  [.a, .b, .c].foldl (fun z r => Winner.own r z y) (Winner.join x y)

theorem singleton_quotient_kernel (x y : Winner) :
    Drop.p.quotient x = Drop.p.quotient y ↔ winnerReset x y = winnerReset y x := by
  cases x <;> cases y <;> decide

end MinimalChoice.CoreAtomic

#print axioms MinimalChoice.CoreAtomic.reset_comm_iff
#print axioms MinimalChoice.CoreAtomic.near_unanimity
#print axioms MinimalChoice.CoreAtomic.flat_reset
#print axioms MinimalChoice.CoreAtomic.singleton_quotient_kernel
