module

public import KFOL.Definitions.CoreBasis
public import KFOL.Algebra.Views
public import KFOL.Equational.Locality

/-! # Native quotient tables uniformly over all role types -/

@[expose] public section

namespace KFOL.Core.Native

universe u

variable {Role : Type u} [DecidableEq Role]

omit [DecidableEq Role] in
theorem ext_atoms_upper {x y : Native Role}
    (ha : ∀ r, x = .atom r ↔ y = .atom r) (hp : x = .upper ↔ y = .upper) : x = y := by
  cases x with
  | atom r => exact (ha r).mp rfl |>.symm
  | lower =>
    cases y with
    | atom r => cases (ha r).mpr rfl
    | lower => rfl
    | upper => cases hp.mpr rfl
  | upper => exact (hp.mp rfl).symm

@[simp] theorem join_eq_atom (x y : Native Role) (r : Role) :
    join x y = .atom r ↔ x = .atom r ∧ y = .atom r := by
  by_cases h : x = y
  · subst y
    simp [join]
  · have hn : ¬(x = .atom r ∧ y = .atom r) := fun hh => h (hh.1.trans hh.2.symm)
    simp only [join, ite_eq_right h, hn, iff_false]
    split <;> simp

@[simp] theorem join_eq_upper (x y : Native Role) :
    join x y = .upper ↔ x = .upper ∨ y = .upper := by
  by_cases h : x = y
  · subst y
    simp [join]
  · by_cases hp : x = .upper ∨ y = .upper <;> simp [join, h, hp]

@[simp] theorem choice_eq_atom_owner (r : Role) (x y : Native Role) :
    choice r x y = .atom r ↔ x = .atom r ∨ y = .atom r := by
  by_cases h : x = .atom r ∨ y = .atom r
  · simp [choice, h]
  · simp only [choice, ite_eq_right h, join_eq_atom]
    exact ⟨fun hh => False.elim (h (Or.inl hh.1)), fun hh => False.elim (h hh)⟩

theorem choice_eq_atom_other (r i : Role) (hri : r ≠ i) (x y : Native Role) :
    choice r x y = .atom i ↔ x = .atom i ∧ y = .atom i := by
  by_cases h : x = .atom r ∨ y = .atom r
  · have hn : ¬(x = .atom i ∧ y = .atom i) := by
      rintro ⟨hx, hy⟩
      rcases h with h | h
      · exact hri (Native.atom.inj (h.symm.trans hx))
      · exact hri (Native.atom.inj (h.symm.trans hy))
    simp [choice, h, hri, hn]
  · simp only [choice, ite_eq_right h, join_eq_atom]

theorem choice_eq_atom (r i : Role) (x y : Native Role) :
    choice r x y = .atom i ↔
      if r = i then x = .atom i ∨ y = .atom i else x = .atom i ∧ y = .atom i := by
  by_cases h : r = i
  · subst r
    simp
  · simp only [ite_eq_right h, choice_eq_atom_other r i h]

@[simp] theorem choice_eq_upper (r : Role) (x y : Native Role) :
    choice r x y = .upper ↔ (x = .upper ∨ y = .upper) ∧ x ≠ .atom r ∧ y ≠ .atom r := by
  by_cases h : x = .atom r ∨ y = .atom r
  · simp only [choice, ite_eq_left h, reduceCtorEq, false_iff, not_and]
    intro _ hx hy
    exact h.elim hx hy
  · simp [choice, not_or.mp h]

omit [DecidableEq Role] in
@[simp] theorem atomicQuotient_eq_atom (A : WinnerSet Role) (r : Role) :
    atomicQuotient A = .atom r ↔ A = WinnerSet.singleton r := by
  classical
  unfold atomicQuotient
  split
  next h =>
    simp only [Native.atom.injEq]
    exact ⟨fun hr => hr ▸ h.choose_spec, fun hr => WinnerSet.singleton_inj.mp (h.choose_spec.symm.trans hr)⟩
  next h => simp_all

omit [DecidableEq Role] in
@[simp] theorem atomicQuotient_ne_upper (A : WinnerSet Role) : atomicQuotient A ≠ .upper := by
  classical
  unfold atomicQuotient
  split <;> simp

omit [DecidableEq Role] in
@[simp] theorem quotient_eq_atom (drop : Option Role) (A : WinnerSet Role) (r : Role) :
    quotient drop A = .atom r ↔ A = WinnerSet.singleton r ∧ drop ≠ some r := by
  classical
  cases drop with
  | none => simp [quotient]
  | some k =>
    by_cases hk : k ∈ A.val
    · have hn : ¬(A = WinnerSet.singleton r ∧ k ≠ r) := by
        rintro ⟨he, hkr⟩
        exact hkr (by simpa [he] using hk)
      simp [quotient, hk, hn]
    · have hr : A = WinnerSet.singleton r → k ≠ r := by
        intro he hkr
        exact hk (by simp [he, hkr])
      simp only [quotient, ite_eq_right hk, atomicQuotient_eq_atom, ne_eq, Option.some.injEq]
      exact ⟨fun he => ⟨he, hr he⟩, And.left⟩

omit [DecidableEq Role] in
@[simp] theorem quotient_eq_upper (drop : Option Role) (A : WinnerSet Role) :
    quotient drop A = .upper ↔ ∃ k, drop = some k ∧ k ∈ A.val := by
  classical
  cases drop <;> simp [quotient]

omit [DecidableEq Role] in
theorem quotient_ne_omitted (drop : Option Role) (A : WinnerSet Role) :
    quotient drop A ≠ omitted drop := by
  cases drop <;> simp [omitted]

/-- Every omission quotient preserves each owned choice, uniformly in K. -/
theorem quotient_choice (drop : Option Role) (r : Role) (A B : WinnerSet Role) :
    quotient drop (WinnerSet.choice r A B) = choice r (quotient drop A) (quotient drop B) := by
  apply ext_atoms_upper
  · intro i
    by_cases hri : r = i
    · subst i
      simp only [quotient_eq_atom, WinnerSet.choice_eq_owner_iff, choice_eq_atom_owner]
      tauto
    · simp only [quotient_eq_atom, WinnerSet.choice_eq_other_iff A B r hri,
        choice_eq_atom_other r i hri]
      tauto
  · rw [choice_eq_upper]
    cases drop with
    | none => simp
    | some k =>
      simp only [quotient_eq_upper, Option.some.injEq]
      by_cases hrk : r = k
      · subst r
        simpa using WinnerSet.mem_choice_owner k A B
      · simpa [hrk, Ne.symm hrk] using WinnerSet.mem_choice_other r k hrk A B

/-- The derived core union really is native join for every role type,
including the full native counteralgebra. -/
theorem three_choice_join (a b c : Role) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : Native Role) : choice c (choice a x y) (choice b x y) = join x y := by
  apply ext_atoms_upper
  · intro i
    rw [join_eq_atom, choice_eq_atom, choice_eq_atom, choice_eq_atom]
    by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hc : c = i
    all_goals simp_all only [ite_true, ite_false]
    all_goals tauto
  · rw [join_eq_upper]
    constructor
    · intro h
      obtain ⟨ha | hb, _, _⟩ := (choice_eq_upper c _ _).mp h
      · exact ((choice_eq_upper a x y).mp ha).1
      · exact ((choice_eq_upper b x y).mp hb).1
    · intro hp
      have hn (r : Role) : ¬(x = .atom r ∧ y = .atom r) := by
        rintro ⟨hx, hy⟩
        rcases hp with h | h
        · cases h.symm.trans hx
        · cases h.symm.trans hy
      have hcross : ¬((x = .atom a ∨ y = .atom a) ∧ (x = .atom b ∨ y = .atom b)) := by
        rintro ⟨ha, hb⟩
        rcases hp with hp | hp
        · subst x
          simp only [reduceCtorEq, false_or] at ha hb
          exact hab (Native.atom.inj (ha.symm.trans hb))
        · subst y
          simp only [reduceCtorEq, or_false] at ha hb
          exact hab (Native.atom.inj (ha.symm.trans hb))
      apply (choice_eq_upper c _ _).mpr
      refine ⟨?_, ?_, ?_⟩
      · by_cases ha : x = .atom a ∨ y = .atom a
        · exact Or.inr ((choice_eq_upper b x y).mpr
            ⟨hp, (not_or.mp (fun hb => hcross ⟨ha, hb⟩)).1,
              (not_or.mp (fun hb => hcross ⟨ha, hb⟩)).2⟩)
        · exact Or.inl ((choice_eq_upper a x y).mpr ⟨hp, (not_or.mp ha).1, (not_or.mp ha).2⟩)
      · exact fun h => hn c ((choice_eq_atom_other a c hac x y).mp h)
      · exact fun h => hn c ((choice_eq_atom_other b c hbc x y).mp h)

@[simp] theorem choice_self (r : Role) (x : Native Role) : choice r x x = x := by
  by_cases hx : x = .atom r <;> simp [choice, join, hx]

theorem choice_comm (r : Role) (x y : Native Role) : choice r x y = choice r y x := by
  apply ext_atoms_upper
  · intro i
    rw [choice_eq_atom, choice_eq_atom]
    split <;> tauto
  · simp only [choice_eq_upper]
    tauto

/-- Each native owned operation is independently a semilattice operation;
no global choice of one owner's order is installed. -/
theorem choice_assoc (r : Role) (x y z : Native Role) :
    choice r (choice r x y) z = choice r x (choice r y z) := by
  apply ext_atoms_upper
  · intro i
    by_cases hri : r = i
    · subst i
      simp only [choice_eq_atom_owner]
      tauto
    · simp only [choice_eq_atom_other r i hri]
      tauto
  · simp only [choice_eq_upper, ne_eq, choice_eq_atom_owner]
    tauto

end KFOL.Core.Native
