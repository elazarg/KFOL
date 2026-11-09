module

public import KFOL.Core.GridSeparation

/-! # Elimination of the third atom below the grid's lower tuple -/

@[expose] public section

namespace KFOL.Core.Grid

universe u

variable {Role : Type u} [DecidableEq Role]

attribute [local instance] Native.structureOf

/-- A different index, available uniformly once the grid side has length two. -/
def other {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Fin n :=
  if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

@[simp] theorem other_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : other hn i ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  simp only [other] at hv
  split_ifs at hv <;> simp only at hv <;> omega

/-- At most one private row variable and one private column variable. -/
def privateProfile {r s : ℕ} (i : Option (Fin r)) (j : Option (Fin s))
    (x : Option (Variable r s)) : Bool :=
  decide ((∃ k, i = some k ∧ x = some (row k)) ∨ (∃ l, j = some l ∧ x = some (col l)))

/-- For a private variable, choose the marker-only row with no third atom.
The choices for cells and for the lower generator are irrelevant. -/
def privateRow {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role) :
    Option (Variable r s) → Option (Variable r s) → Native Role
  | some (.inr (.inl i)) => rawValue three (.inl (⟨(i, other hr i), Ne.symm (other_ne hr i)⟩, none))
  | some (.inr (.inr j)) => rawValue three (.inr (.inl (⟨(j, other hs j), Ne.symm (other_ne hs j)⟩, none)))
  | _ => fun _ => Native.lower

omit [DecidableEq Role] in
theorem privateRow_marker {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (i : Option (Fin r)) (j : Option (Fin s)) (x : Option (Variable r s))
    (hx : privateProfile i j x = true) : privateRow hr hs three x x = Native.upper := by
  have hx' := of_decide_eq_true hx
  rcases hx' with ⟨k, _, rfl⟩ | ⟨l, _, rfl⟩
  · simp [privateRow, rawValue, row, fMarker]
  · simp [privateRow, rawValue, col, gMarker]

omit [DecidableEq Role] in
theorem privateRow_absent {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (x z : Option (Variable r s)) : privateRow hr hs three x z ≠ Native.atom (three 2) := by
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  cases x with
  | none => simp [privateRow]
  | some x =>
    rcases x with ⟨i,j⟩ | (i | j)
    · simp [privateRow]
    · cases z with
      | none => simp [privateRow, rawValue]
      | some z => simp only [privateRow, rawValue]; split_ifs <;> simp_all
    · cases z with
      | none => simp [privateRow, rawValue]
      | some z => simp only [privateRow, rawValue]; split_ifs <;> simp_all

omit [DecidableEq Role] in
theorem privateRow_avoid {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (i : Option (Fin r)) (j : Option (Fin s)) (x z : Option (Variable r s))
    (hx : privateProfile i j x = true) (hz : privateProfile i j z = true) (b : Role) :
    privateRow hr hs three x z ≠ Native.atom b := by
  have hx' := of_decide_eq_true hx
  have hz' := of_decide_eq_true hz
  rcases hx' with ⟨k, hk, rfl⟩ | ⟨l, hl, rfl⟩ <;>
    rcases hz' with ⟨k', hk', rfl⟩ | ⟨l', hl', rfl⟩
  · have he : k = k' := Option.some.inj (hk.symm.trans hk')
    subst k'
    simp [privateRow, rawValue, row, fMarker]
  · simp [privateRow, rawValue, row, col, fMarker, fBlock, cell]
  · simp [privateRow, rawValue, row, col, gMarker, gBlock, cell]
  · have he : l = l' := Option.some.inj (hl.symm.trans hl')
    subst l'
    simp [privateRow, rawValue, col, gMarker]

/-- Positive third-role profiles on any of the source table's possible
third-atom position sets force an explicitly included upper coordinate. -/
theorem upper_of_private_profile {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (i : Option (Fin r)) (j : Option (Fin s))
    (ht : profile (three 2) (privateProfile i j) t = true) :
    ∃ c : Coordinate r s, t.realize (rawValue three c) = Native.upper := by
  obtain ⟨x, hx, hp⟩ := marker_of_positive_profile (three 2) (privateProfile i j)
    (privateRow hr hs three) (privateRow_marker hr hs three i j)
    (fun x _ z => privateRow_absent hr hs three x z)
    (fun x hx z hz b => privateRow_avoid hr hs three i j x z hx hz b) t ht
  have hx' := of_decide_eq_true hx
  rcases hx' with ⟨k, _, rfl⟩ | ⟨l, _, rfl⟩
  · exact ⟨.inl (⟨(k,other hr k), Ne.symm (other_ne hr k)⟩,none), hp⟩
  · exact ⟨.inr (.inl (⟨(l,other hs l), Ne.symm (other_ne hs l)⟩,none)), hp⟩

/-- Every row's third-atom inputs form one of the private profiles. -/
theorem exists_private_profile {r s : ℕ} (three : Fin 3 ↪ Role) (c : Coordinate r s) :
    ∃ i : Option (Fin r), ∃ j : Option (Fin s),
      (fun v => decide (rawValue three c v = Native.atom (three 2))) = privateProfile i j := by
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  rcases c with ⟨p,a⟩ | (⟨p,a⟩ | ⟨i,j⟩)
  · cases a with
    | none =>
      refine ⟨none, none, ?_⟩
      funext v
      cases v with
      | none => simp [rawValue, privateProfile]
      | some v => simp only [rawValue]; split_ifs <;> simp_all [privateProfile]
    | some j =>
      refine ⟨none, some j, ?_⟩
      funext v
      cases v with
      | none => simp [rawValue, privateProfile]
      | some v =>
        rcases v with ⟨i,k⟩ | (i | k)
        all_goals simp [rawValue, privateProfile, fMarker, fBlock, cell, row, col]
        all_goals split_ifs <;> simp_all
  · cases a with
    | none =>
      refine ⟨none, none, ?_⟩
      funext v
      cases v with
      | none => simp [rawValue, privateProfile]
      | some v => simp only [rawValue]; split_ifs <;> simp_all [privateProfile]
    | some i =>
      refine ⟨some i, none, ?_⟩
      funext v
      cases v with
      | none => simp [rawValue, privateProfile]
      | some v =>
        rcases v with ⟨k,j⟩ | (k | j)
        all_goals simp [rawValue, privateProfile, gMarker, gBlock, cell, row, col]
        all_goals split_ifs <;> simp_all
  · refine ⟨some i, some j, ?_⟩
    funext v
    cases v with
    | none => simp [rawValue, privateProfile]
    | some v =>
      rcases v with ⟨k,l⟩ | (k | l)
      all_goals simp [rawValue, privateProfile, cell, row, col]
      all_goals split_ifs <;> simp_all

/-- Below the lower tuple, the entire third atom is absent. This holds
for all core terms and all roles, with no bound on syntax or variable reuse. -/
theorem no_third_atom {r s : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s) (three : Fin 3 ↪ Role)
    (t : Equational.Term (Equational.CoreSymbol Role) (Option (Variable r s)))
    (noUpper : ∀ c : Coordinate r s, t.realize (rawValue three c) ≠ Native.upper)
    (c : Coordinate r s) : t.realize (rawValue three c) ≠ Native.atom (three 2) := by
  intro he
  have ht := (realize_eq_atom_iff_profile t (three 2) (rawValue three c)).mp he
  obtain ⟨i,j,hij⟩ := exists_private_profile three c
  rw [hij] at ht
  obtain ⟨d,hd⟩ := upper_of_private_profile hr hs three t i j ht
  exact noUpper d hd

end KFOL.Core.Grid
