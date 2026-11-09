module

public import KFOL.Strategic.Basic
public import Mathlib.Data.Set.Finite.Basic

/-! # Possible equilibrium winners and owned-choice interpretation -/

@[expose] public section

namespace KFOL.Strategic

universe u

/-- The nonempty winner carrier, bundled after the independently proved
existence theorem. Its underlying set is defined by actual equilibrium profiles. -/
def value {Role : Type u} (g : Tree Role) : WinnerSet Role :=
  ⟨possibleWinners g, possibleWinners_ne g⟩

@[simp] theorem value_leaf {Role : Type u} (i : Role) :
    value (.leaf i) = WinnerSet.singleton i :=
  Subtype.ext (possibleWinners_leaf i)

/-- The recurrence is a theorem about independently specified full-profile
SPE, including off-path subgames and whole-player deviations. -/
@[simp] theorem value_node {Role : Type u} (r : Role) (g h : Tree Role) :
    value (.node r g h) = WinnerSet.choice r (value g) (value h) := by
  classical
  have hg : value g = WinnerSet.singleton r ↔ possibleWinners g = {r} := Subtype.ext_iff
  have hh : value h = WinnerSet.singleton r ↔ possibleWinners h = {r} := Subtype.ext_iff
  apply Subtype.ext
  change possibleWinners (.node r g h) = _
  rw [possibleWinners_node]
  simp only [WinnerSet.choice, hg, hh]
  split_ifs <;> rfl

/-- The four occurrences are independent copies with independently supplied
full profiles. There is no sharing constraint between equal input trees. -/
def neutralTree {Role : Type u} (r s t : Role) (g h : Tree Role) : Tree Role :=
  .node t (.node r g h) (.node s g h)

theorem value_neutralTree {Role : Type u} (r s t : Role)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (g h : Tree Role) :
    value (neutralTree r s t g h) = WinnerSet.union (value g) (value h) := by
  simp only [neutralTree, value_node]
  exact WinnerSet.three_owner_union (value g) (value h) r s t hrs hrt hst

/-- Every nonempty finite set of roles is realized by a finite public game. -/
theorem exists_value_of_finite {Role : Type u} (three : Fin 3 ↪ Role)
    (A : WinnerSet Role) (finite : A.val.Finite) : ∃ g : Tree Role, value g = A := by
  classical
  have hrs := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hrt := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hst := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  have realize (S : Finset Role) : S.Nonempty → ∃ g : Tree Role, (value g).val = (S : Set Role) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S _ ih =>
      intro _
      by_cases hs : S.Nonempty
      · obtain ⟨g, hg⟩ := ih hs
        refine ⟨neutralTree (three 0) (three 1) (three 2) (.leaf a) g, ?_⟩
        rw [value_neutralTree _ _ _ hrs hrt hst, value_leaf]
        ext i
        simp [hg]
      · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst S
        exact ⟨.leaf a, by simp⟩
  obtain ⟨g, hg⟩ := realize finite.toFinset (by simpa using A.property)
  exact ⟨g, Subtype.ext (hg.trans finite.coe_toFinset)⟩

end KFOL.Strategic
