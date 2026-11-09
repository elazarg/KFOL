module

public import KFOL.Core.Native

/-! # Closure of typed upper-marker guards under arbitrary owned choices -/

@[expose] public section

namespace KFOL.Core.Native

universe u

variable {Role : Type u} [DecidableEq Role]

/-- An atomic output is bounded by any compatible owned Boolean bit
that bounds both atomic inputs. -/
theorem bit_positive_of_atom_step (a owner : Role) (x y : Native Role) (bx by' : Bool)
    (hx : x = .atom a → bx = true) (hy : y = .atom a → by' = true)
    (h : choice owner x y = .atom a) :
    (if owner = a then bx || by' else bx && by') = true := by
  by_cases ho : owner = a
  · subst owner
    have hp := (choice_eq_atom_owner a x y).mp h
    rcases hp with hp | hp
    · simp [hx hp]
    · simp [hy hp]
  · have hp := (choice_eq_atom_other owner a ho x y).mp h
    simp [ho,hx hp.1,hy hp.2]

/-- A missing typed label protects a marker through one arbitrary node.
The positive-bit guard excludes all atoms on positive siblings; the
tracked role's atom is absent on all siblings. -/
theorem upper_of_gap_step (a owner : Role) (bx by' : Bool) (vx vy lx ly : Native Role)
    (hx : bx = true → lx ≠ .atom a → vx = .upper)
    (hy : by' = true → ly ≠ .atom a → vy = .upper)
    (absentX : vx ≠ .atom a) (absentY : vy ≠ .atom a)
    (avoidX : bx = true → ∀ role, vx ≠ .atom role)
    (avoidY : by' = true → ∀ role, vy ≠ .atom role)
    (hbit : (if owner = a then bx || by' else bx && by') = true)
    (hlabel : choice owner lx ly ≠ .atom a) :
    choice owner vx vy = .upper := by
  by_cases ho : owner = a
  · subst owner
    have hb : bx = true ∨ by' = true := by simpa only [ite_true,Bool.or_eq_true] using hbit
    have hlx : lx ≠ .atom a := fun he => hlabel ((choice_eq_atom_owner a lx ly).mpr (Or.inl he))
    have hly : ly ≠ .atom a := fun he => hlabel ((choice_eq_atom_owner a lx ly).mpr (Or.inr he))
    rcases hb with hb | hb
    · exact (choice_eq_upper a vx vy).mpr ⟨Or.inl (hx hb hlx),absentX,absentY⟩
    · exact (choice_eq_upper a vx vy).mpr ⟨Or.inr (hy hb hly),absentX,absentY⟩
  · have hb : bx = true ∧ by' = true := by
      simpa only [ite_eq_right ho,Bool.and_eq_true] using hbit
    by_cases hlx : lx = .atom a
    · have hly : ly ≠ .atom a := fun he =>
        hlabel ((choice_eq_atom_other owner a ho lx ly).mpr ⟨hlx,he⟩)
      exact (choice_eq_upper owner vx vy).mpr
        ⟨Or.inr (hy hb.2 hly),avoidX hb.1 owner,avoidY hb.2 owner⟩
    · exact (choice_eq_upper owner vx vy).mpr
        ⟨Or.inl (hx hb.1 hlx),avoidX hb.1 owner,avoidY hb.2 owner⟩

end KFOL.Core.Native
