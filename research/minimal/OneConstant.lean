/- One fixed winner leaves only constant or inflationary unary contexts. -/
import Separation

set_option autoImplicit false
namespace MinimalChoice.OneConstant

theorem own_common_sub {α : Type} (p : α) (X A B : S α)
    (ha : Sub X A) (hb : Sub X B) : Sub X (own p A B) := by
  classical
  unfold own
  split
  · rename_i h
    rcases h with h | h
    · simpa only [h] using ha
    · simpa only [h] using hb
  · exact fun x hx => Or.inl (ha x hx)

inductive Term (α : Type) where
  | input : Term α
  | point : Term α
  | node : α → Term α → Term α → Term α

noncomputable def Term.denote {α : Type} (t : Term α) (r : α) (X : S α) : S α :=
  match t with
  | .input => X
  | .point => atom r
  | .node p left right => own p (left.denote r X) (right.denote r X)

theorem Term.dichotomy {α : Type} (t : Term α) (r : α) :
    (∀ X, t.denote r X = atom r) ∨ (∀ X, Sub X (t.denote r X)) := by
  classical
  induction t with
  | input => exact Or.inr (fun _ _ h => h)
  | point => exact Or.inl (fun _ => rfl)
  | node p left right hl hr =>
    rcases hl with hl | hl <;> rcases hr with hr | hr
    · left
      intro X
      simp only [Term.denote, hl, hr, own_idem]
    · by_cases hp : p = r
      · subst p
        left
        intro X
        simp only [Term.denote, hl]
        simp [own]
      · right
        intro X
        rw [Term.denote, hl, own_comm]
        have hn : atom r ≠ atom p := fun h => hp (atom_inj.mp h).symm
        exact fun x hx => own_left_sub p _ _ hn x (hr X x hx)
    · by_cases hp : p = r
      · subst p
        left
        intro X
        simp only [Term.denote, hr]
        simp [own]
      · right
        intro X
        rw [Term.denote, hr]
        have hn : atom r ≠ atom p := fun h => hp (atom_inj.mp h).symm
        exact fun x hx => own_left_sub p _ _ hn x (hl X x hx)
    · right
      intro X
      exact own_common_sub p X _ _ (hl X) (hr X)

/-- One nontrivial atomic test detects a constant in the one-constant fragment. -/
theorem Term.rigidity {α : Type} (t : Term α) (r q : α) (hne : q ≠ r)
    (h : t.denote r (atom q) = atom r) : ∀ X, t.denote r X = atom r := by
  rcases t.dichotomy r with hc | he
  · exact hc
  · have hw := he (atom q) q rfl
    rw [h] at hw
    exact False.elim (hne hw)

theorem Term.inflationary_of_atomic_identity {α : Type} (t : Term α)
    (r q : α) (hne : q ≠ r) (h : t.denote r (atom q) = atom q) :
    ∀ X, Sub X (t.denote r X) := by
  rcases t.dichotomy r with hc | he
  · have ha := (hc (atom q)).symm.trans h
    exact False.elim (hne (atom_inj.mp ha).symm)
  · exact he

end MinimalChoice.OneConstant

#print axioms MinimalChoice.OneConstant.Term.dichotomy
#print axioms MinimalChoice.OneConstant.Term.rigidity
