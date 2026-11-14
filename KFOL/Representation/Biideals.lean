module

public import KFOL.Representation.Ideals

/-! # Biideal completion and the co-operation of a join-bilinear map -/

@[expose] public section

namespace KFOL.IdealDuality.BiIdeal

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}
variable [SemilatticeSup A] [SemilatticeSup B] [SemilatticeSup C]

instance : InfSet (BiIdeal A B) where
  sInf S :=
    { carrier := {p | ∀ R ∈ S, p ∈ R}
      lower' := fun ha hb h R hR => R.lower' ha hb (h R hR)
      sup_left' := fun h h' R hR => R.sup_left' (h R hR) (h' R hR)
      sup_right' := fun h h' R hR => R.sup_right' (h R hR) (h' R hR) }

instance : CompleteLattice (BiIdeal A B) :=
  completeLatticeOfInf (BiIdeal A B) fun _S =>
    ⟨fun R hR _p hp => hp R hR, fun _R hR _p hp _Q hQ => hR hQ hp⟩

@[simp] theorem mem_sInf (S : Set (BiIdeal A B)) (p : A × B) :
    p ∈ sInf S ↔ ∀ R ∈ S, p ∈ R := Iff.rfl

@[simp] theorem not_mem_bot (p : A × B) : p ∉ (⊥ : BiIdeal A B) := by
  let E : BiIdeal A B :=
    { carrier := ∅
      lower' := fun _ _ h => h.elim
      sup_left' := fun h _ => h.elim
      sup_right' := fun h _ => h.elim }
  exact fun h => (bot_le : (⊥ : BiIdeal A B) ≤ E) h

@[simp] theorem mem_top (p : A × B) : p ∈ (⊤ : BiIdeal A B) := by
  let U : BiIdeal A B :=
    { carrier := Set.univ
      lower' := fun _ _ _ => trivial
      sup_left' := fun _ _ => trivial
      sup_right' := fun _ _ => trivial }
  exact (le_top : U ≤ (⊤ : BiIdeal A B)) trivial

@[simp] theorem mem_rectangle (a x : A) (b y : B) :
    (x, y) ∈ rectangle a b ↔ x ≤ a ∧ y ≤ b := Iff.rfl

theorem rectangle_le_iff {a : A} {b : B} {R : BiIdeal A B} :
    rectangle a b ≤ R ↔ (a, b) ∈ R := by
  constructor
  · intro h
    exact h ⟨le_rfl, le_rfl⟩
  · intro h p hp
    exact R.lower' hp.1 hp.2 h

theorem rectangle_sup_left (a a' : A) (b : B) :
    rectangle (a ⊔ a') b = rectangle a b ⊔ rectangle a' b := by
  apply le_antisymm
  · apply rectangle_le_iff.mpr
    exact (rectangle a b ⊔ rectangle a' b).sup_left'
      (rectangle_le_iff.mp le_sup_left) (rectangle_le_iff.mp le_sup_right)
  · apply sup_le
    · intro p hp
      exact ⟨hp.1.trans le_sup_left, hp.2⟩
    · intro p hp
      exact ⟨hp.1.trans le_sup_right, hp.2⟩

theorem rectangle_sup_right (a : A) (b b' : B) :
    rectangle a (b ⊔ b') = rectangle a b ⊔ rectangle a b' := by
  apply le_antisymm
  · apply rectangle_le_iff.mpr
    exact (rectangle a b ⊔ rectangle a b').sup_right'
      (rectangle_le_iff.mp le_sup_left) (rectangle_le_iff.mp le_sup_right)
  · apply sup_le
    · intro p hp
      exact ⟨hp.1, hp.2.trans le_sup_left⟩
    · intro p hp
      exact ⟨hp.1, hp.2.trans le_sup_right⟩

/-- A nonempty directed join of biideals is its set union. -/
theorem mem_sSup_iff_of_directed (S : Set (BiIdeal A B)) (_hne : S.Nonempty)
    (hdir : DirectedOn (· ≤ ·) S) (p : A × B) :
    p ∈ sSup S ↔ ∃ R ∈ S, p ∈ R := by
  let U : BiIdeal A B :=
    { carrier := {p | ∃ R ∈ S, p ∈ R}
      lower' := by
        rintro a a' b b' ha hb ⟨R, hR, hp⟩
        exact ⟨R, hR, R.lower' ha hb hp⟩
      sup_left' := by
        rintro a a' b ⟨R, hR, hp⟩ ⟨Q, hQ, hp'⟩
        obtain ⟨T, hT, hRT, hQT⟩ := hdir R hR Q hQ
        exact ⟨T, hT, T.sup_left' (hRT hp) (hQT hp')⟩
      sup_right' := by
        rintro a b b' ⟨R, hR, hp⟩ ⟨Q, hQ, hp'⟩
        obtain ⟨T, hT, hRT, hQT⟩ := hdir R hR Q hQ
        exact ⟨T, hT, T.sup_right' (hRT hp) (hQT hp')⟩ }
  have hU : sSup S = U := by
    apply le_antisymm
    · exact sSup_le fun R hR p hp => ⟨R, hR, hp⟩
    · rintro p ⟨R, hR, hp⟩
      exact le_sSup hR hp
  rw [hU]
  rfl

theorem rectangle_compact (a : A) (b : B) : IsCompactElement (rectangle a b) := by
  rw [isCompactElement_iff_le_of_directed_sSup_le]
  intro S hne hdir hle
  obtain ⟨R, hR, hab⟩ := (mem_sSup_iff_of_directed S hne hdir (a, b)).mp
    (rectangle_le_iff.mp hle)
  exact ⟨R, hR, rectangle_le_iff.mpr hab⟩

theorem rectangle_ne_bot (a : A) (b : B) : rectangle a b ≠ ⊥ := by
  intro h
  exact not_mem_bot (a, b) (h ▸ (show (a, b) ∈ rectangle a b from ⟨le_rfl, le_rfl⟩))

theorem sSup_rectangles (R : BiIdeal A B) :
    sSup {Q | ∃ a b, (a, b) ∈ R ∧ Q = rectangle a b} = R := by
  apply le_antisymm
  · apply sSup_le
    rintro Q ⟨a, b, hab, rfl⟩
    exact rectangle_le_iff.mpr hab
  · intro p hp
    have hP : rectangle p.1 p.2 ≤ sSup
        {Q : BiIdeal A B | ∃ a b, (a, b) ∈ R ∧ Q = rectangle a b} :=
      le_sSup ⟨p.1, p.2, hp, rfl⟩
    exact hP ⟨le_rfl, le_rfl⟩

instance : IsCompactlyGenerated (BiIdeal A B) where
  exists_isLUB R := ⟨{Q | ∃ a b, (a, b) ∈ R ∧ Q = rectangle a b}, by
    rintro Q ⟨a, b, _, rfl⟩
    exact rectangle_compact a b, by
      have h := isLUB_sSup {Q : BiIdeal A B | ∃ a b, (a, b) ∈ R ∧ Q = rectangle a b}
      rw [sSup_rectangles R] at h
      exact h⟩

/-- Inverse image of an ideal under a separately join-preserving map. -/
def operation (f : SupHom A (SupHom B C)) (J : Ideals C) : BiIdeal A B where
  carrier := {p | (f p.1 p.2 : WithBot C) ∈ J}
  lower' := by
    intro a a' b b' ha hb h
    apply J.lower _ h
    exact WithBot.coe_le_coe.mpr
      ((OrderHomClass.mono (f a') hb).trans ((OrderHomClass.mono f ha) b))
  sup_left' := by
    intro a a' b h h'
    change (f (a ⊔ a') b : WithBot C) ∈ J
    rw [map_sup]
    change ((f a b ⊔ f a' b : C) : WithBot C) ∈ J
    rw [WithBot.coe_sup]
    exact Order.Ideal.sup_mem h h'
  sup_right' := by
    intro a b b' h h'
    change (f a (b ⊔ b') : WithBot C) ∈ J
    rw [map_sup, WithBot.coe_sup]
    exact Order.Ideal.sup_mem h h'

@[simp] theorem mem_operation (f : SupHom A (SupHom B C)) (J : Ideals C) (p : A × B) :
    p ∈ operation f J ↔ (f p.1 p.2 : WithBot C) ∈ J := Iff.rfl

end KFOL.IdealDuality.BiIdeal
