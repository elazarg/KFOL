/- A generic mixed-owner law and a finite countermodel to the candidate
core basis, even after adding owner exhaustion. -/
import CoreModels

set_option autoImplicit false
namespace MinimalChoice.CoreMixed

theorem mixed_absorption {α : Type} (a b : α) (X Y Z : S α)
    (hX : NE X) (hY : NE Y) (hZ : NE Z) :
    own a X (own b Y (own a Y Z)) =
      own a X (own b Y (own a X (own a Y Z))) := by
  classical
  by_cases hx : X = atom a
  · simp [own, hx]
  by_cases hy : Y = atom a
  · simp [own, hy]
  by_cases hz : Z = atom a
  · simp [own, hz]
  have hu : NE (join Y Z) := by
    obtain ⟨y, h⟩ := hY
    exact ⟨y, Or.inl h⟩
  have hua : join Y Z ≠ atom a := by
    intro he
    exact hy ((join_eq_atom_iff Y Z hY hZ a).mp he).1
  have hva : join X (join Y Z) ≠ atom a := by
    intro he
    exact hx ((join_eq_atom_iff X _ hX hu a).mp he).1
  have hayz : own a Y Z = join Y Z := by simp [own, hy, hz]
  have haxu : own a X (join Y Z) = join X (join Y Z) := by simp [own, hx, hua]
  rw [hayz, haxu]
  by_cases hyb : Y = atom b
  · simp [own, hyb]
  have hub : join Y Z ≠ atom b := by
    intro he
    exact hyb ((join_eq_atom_iff Y Z hY hZ b).mp he).1
  have hvb : join X (join Y Z) ≠ atom b := by
    intro he
    exact hub ((join_eq_atom_iff X _ hX hu b).mp he).2
  have hbu : own b Y (join Y Z) = join Y Z := by
    simp only [own, hyb, hub, or_self, ↓reduceIte]
    funext i
    apply propext
    simp only [join]
    grind
  have hbv : own b Y (join X (join Y Z)) = join X (join Y Z) := by
    simp only [own, hyb, hvb, or_self, ↓reduceIte]
    funext i
    apply propext
    simp only [join]
    grind
  rw [hbu, hbv, haxu]
  simp only [own, hx, hva, or_self, ↓reduceIte]
  funext i
  apply propext
  simp only [join]
  grind

namespace Six

abbrev Carrier := Fin 6

def add (x y : Carrier) : Carrier :=
  let rows : Array (Array Carrier) := #[
    #[0, 2, 2, 3, 4, 5], #[2, 1, 2, 4, 4, 5], #[2, 2, 2, 4, 4, 5],
    #[3, 4, 4, 3, 4, 5], #[4, 4, 4, 4, 4, 5], #[5, 5, 5, 5, 5, 5]]
  rows[x.val]![y.val]!

def first (x y : Carrier) : Carrier :=
  let rows : Array (Array Carrier) := #[
    #[0, 0, 0, 3, 3, 3], #[0, 1, 2, 3, 4, 5], #[0, 2, 2, 3, 4, 5],
    #[3, 3, 3, 3, 3, 3], #[3, 4, 4, 3, 4, 5], #[3, 5, 5, 3, 5, 5]]
  rows[x.val]![y.val]!

def last (x y : Carrier) : Carrier :=
  let rows : Array (Array Carrier) := #[
    #[0, 1, 2, 3, 4, 5], #[1, 1, 1, 1, 1, 5], #[2, 1, 2, 4, 4, 5],
    #[3, 1, 4, 3, 4, 5], #[4, 1, 4, 4, 4, 5], #[5, 5, 5, 5, 5, 5]]
  rows[x.val]![y.val]!

def choice (i : Fin 3) : Carrier → Carrier → Carrier :=
  if i = 0 then first else if i = 1 then add else last

def semilattice (f : Carrier → Carrier → Carrier) : Prop :=
  (∀ x, f x x = x) ∧ (∀ x y, f x y = f y x) ∧
    (∀ x y z, f (f x y) z = f x (f y z))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem candidate :
    semilattice add ∧
    (∀ i, semilattice (choice i)) ∧
    (∀ i x y z, choice i x (add y z) = add (choice i x y) (choice i x z)) ∧
    (∀ i j x y, choice i x (choice j x y) = choice j x (choice i x y)) ∧
    (∀ i j x y, i ≠ j → add (choice i x y) (choice j x y) = add x y) ∧
    (∀ a b c x y, a ≠ b → a ≠ c → b ≠ c →
      choice c (choice a x y) (choice b x y) = add x y) ∧
    (∀ c x y z,
      add c (add (choice 0 c x) (add (choice 1 c y) (choice 2 c z))) =
        add (choice 0 c x) (add (choice 1 c y) (choice 2 c z))) := by
  unfold semilattice
  decide

theorem mixed_failure :
    choice 0 0 (choice 2 1 (choice 0 1 5)) = 3 ∧
    choice 0 0 (choice 2 1 (choice 0 0 (choice 0 1 5))) = 0 := by decide

end Six
end MinimalChoice.CoreMixed

#print axioms MinimalChoice.CoreMixed.mixed_absorption
#print axioms MinimalChoice.CoreMixed.Six.candidate
#print axioms MinimalChoice.CoreMixed.Six.mixed_failure
