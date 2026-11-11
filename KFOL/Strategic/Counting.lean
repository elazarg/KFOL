module

public import KFOL.Strategic.Adequacy
public import KFOL.Definitions.StrategicCounting
public import KFOL.Algebra.Counting

/-! # Optimal numbers of decisions for public winner sets -/

@[expose] public section

namespace KFOL.Strategic

universe u
variable {Role : Type u}

namespace Tree

@[simp] theorem eval_toTerm (g : Tree Role) : g.toTerm.eval Empty.elim = value g := by
  induction g <;> simp_all [toTerm, Term.eval]

@[simp] theorem choiceCount_toTerm (g : Tree Role) :
    g.toTerm.choiceCount = g.choiceCount := by
  induction g <;> simp_all [toTerm, choiceCount, Term.choiceCount]

@[simp] theorem leafMass_toTerm (g : Tree Role) :
    g.toTerm.leafMass Empty.elim = g.choiceCount + 1 := by
  induction g with
  | leaf r => rfl
  | node r g h ihg ihh =>
    simp only [toTerm, Term.leafMass, choiceCount, ihg, ihh]
    omega

@[simp] theorem absorbingCount_leaf (r : Role) : absorbingCount (.leaf r) = 0 := rfl

@[simp] theorem absorbingCount_node (r : Role) (g h : Tree Role) :
    absorbingCount (.node r g h) = g.absorbingCount + h.absorbingCount +
      if value g = WinnerSet.singleton r ∨ value h = WinnerSet.singleton r
      then 1 else 0 := by
  simp only [absorbingCount, toTerm, Term.absorbingCount, eval_toTerm]

theorem winner_budget [Finite Role] (g : Tree Role) :
    (value g).val.ncard ≤ min (Nat.card Role) (g.choiceCount + 1) := by
  simpa using Term.atomic_winner_budget g.toTerm Empty.elim (fun x => nomatch x)

theorem winner_budget_absorbing [Finite Role] (g : Tree Role) :
    (value g).val.ncard + g.absorbingCount ≤ g.choiceCount + 1 := by
  simpa [absorbingCount] using Term.winner_budget_absorbing g.toTerm Empty.elim

/-- Replacing one leaf by a redundant choice preserves all existing node values
and adds just the requested kind of choice. -/
theorem exists_pad (three : Fin 3 ↪ Role) (g : Tree Role) (absorbing : Bool) :
    ∃ g' : Tree Role, value g' = value g ∧ g'.choiceCount = g.choiceCount + 1 ∧
      g'.absorbingCount = g.absorbingCount + (if absorbing then 1 else 0) := by
  classical
  induction g with
  | leaf i =>
    cases absorbing with
    | true =>
      refine ⟨.node i (.leaf i) (.leaf i), ?_, rfl, ?_⟩
      · simp [WinnerSet.choice_self]
      · simp
    | false =>
      obtain ⟨r, hri, _⟩ := exists_role_outside_pair three i i
      refine ⟨.node r (.leaf i) (.leaf i), ?_, rfl, ?_⟩
      · simp [WinnerSet.choice_self]
      · simp [hri.symm]
  | node r g h ihg _ =>
    obtain ⟨g', hv, hc, ha⟩ := ihg
    refine ⟨.node r g' h, ?_, ?_, ?_⟩
    · simp only [value_node, hv]
    · simp only [choiceCount, hc]; omega
    · simp only [absorbingCount_node, hv, ha]; omega

theorem exists_pad_many (three : Fin 3 ↪ Role) (g : Tree Role)
    (absorbing : Bool) (n : ℕ) :
    ∃ g' : Tree Role, value g' = value g ∧ g'.choiceCount = g.choiceCount + n ∧
      g'.absorbingCount = g.absorbingCount + (if absorbing then n else 0) := by
  induction n with
  | zero => exact ⟨g, rfl, by omega, by cases absorbing <;> simp⟩
  | succ n ih =>
    obtain ⟨g', hv, hc, ha⟩ := ih
    obtain ⟨g'', hv', hc', ha'⟩ := exists_pad three g' absorbing
    refine ⟨g'', hv'.trans hv, by omega, ?_⟩
    cases absorbing <;> simp_all [Nat.add_assoc]

end Tree

/-- Every nonempty finite target is realized with the
minimum number of binary choices. Three roles suffice even for a two-winner target. -/
theorem exists_value_optimal_of_finite (three : Fin 3 ↪ Role)
    (A : WinnerSet Role) (finite : A.val.Finite) :
    ∃ g : Tree Role, value g = A ∧ g.choiceCount + 1 = A.val.ncard := by
  classical
  have realize (S : Finset Role) : S.Nonempty →
      ∃ g : Tree Role, (value g).val = (S : Set Role) ∧ g.choiceCount + 1 = S.card := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      intro _
      by_cases hs : S.Nonempty
      · obtain ⟨g, hg, hc⟩ := ih hs
        obtain ⟨b, hb⟩ := hs
        obtain ⟨r, hra, hrb⟩ := exists_role_outside_pair three a b
        have hleft : WinnerSet.singleton a ≠ WinnerSet.singleton r := by
          simpa using hra.symm
        have hright : value g ≠ WinnerSet.singleton r := by
          intro he
          have hbr : b ∈ (WinnerSet.singleton r).val := by rw [← he, hg]; exact hb
          exact hrb (Set.mem_singleton_iff.mp hbr).symm
        refine ⟨.node r (.leaf a) g, ?_, ?_⟩
        · rw [value_node, value_leaf, WinnerSet.choice,
            ite_eq_right (not_or.mpr ⟨hleft, hright⟩)]
          ext i
          simp [hg]
        · simp only [Tree.choiceCount, Nat.zero_add, Finset.card_insert_of_notMem ha]
          omega
      · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        subst S
        exact ⟨.leaf a, by simp, by simp [Tree.choiceCount]⟩
  obtain ⟨g, hg, hc⟩ := realize finite.toFinset (by simpa using A.property)
  exact ⟨g, Subtype.ext (hg.trans finite.coe_toFinset),
    hc.trans (by rw [← Set.ncard_coe_finset, finite.coe_toFinset])⟩

theorem optimal_realizability [Finite Role] (three : Fin 3 ↪ Role) (A : WinnerSet Role) :
    (∃ g : Tree Role, value g = A ∧ g.choiceCount = A.val.ncard - 1) ∧
      ∀ g : Tree Role, value g = A → A.val.ncard - 1 ≤ g.choiceCount := by
  obtain ⟨g, hg, hc⟩ := exists_value_optimal_of_finite three A (Set.toFinite A.val)
  refine ⟨⟨g, hg, by omega⟩, ?_⟩
  intro h hh
  have hb := (le_min_iff.mp (Tree.winner_budget h)).2
  rw [hh] at hb
  omega

/-- The winner bound with a prescribed number of absorbing decisions is sharp. -/
theorem sharp_absorbing_budget [Finite Role] (three : Fin 3 ↪ Role)
    (n h : ℕ) (hn : h ≤ n) :
    (∀ g : Tree Role, g.choiceCount = n → g.absorbingCount = h →
      (value g).val.ncard ≤ min (Nat.card Role) (n + 1 - h)) ∧
    ∃ g : Tree Role, g.choiceCount = n ∧ g.absorbingCount = h ∧
      (value g).val.ncard = min (Nat.card Role) (n + 1 - h) := by
  constructor
  · intro g hg hh
    have hb := g.winner_budget_absorbing
    exact le_min (Set.ncard_le_card _) (by omega)
  · have hk : 0 < Nat.card Role := by
      have hne : (Set.univ : Set Role).Nonempty := ⟨three 0, Set.mem_univ _⟩
      simpa only [Set.ncard_univ] using hne.ncard_pos
    let m := min (Nat.card Role) (n + 1 - h)
    have hm : 0 < m := by dsimp [m]; omega
    obtain ⟨S, _, hs⟩ := Set.exists_subset_card_eq
      (s := (Set.univ : Set Role)) (n := m)
      (by rw [Set.ncard_univ]; exact min_le_left _ _)
    have hs' : S.ncard = m := hs
    let A : WinnerSet Role := ⟨S, (Set.ncard_pos (s := S)).mp (by omega)⟩
    obtain ⟨g, hg, hc⟩ := exists_value_optimal_of_finite three A (Set.toFinite S)
    have hsize : (value g).val.ncard = m := by rw [hg]; exact hs'
    have hcount : g.choiceCount + 1 = m := hc.trans hs'
    have habs : g.absorbingCount = 0 := by
      have hb := g.winner_budget_absorbing
      omega
    obtain ⟨g', hv', hc', ha'⟩ := Tree.exists_pad_many three g true h
    obtain ⟨g'', hv'', hc'', ha''⟩ := Tree.exists_pad_many three g' false (n - (g.choiceCount + h))
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at ha' ha''
    refine ⟨g'', ?_, ?_, ?_⟩
    · have hmle : m ≤ n + 1 - h := min_le_right _ _
      omega
    · omega
    · rw [hv'', hv', hsize]

theorem sharp_budget [Finite Role] (three : Fin 3 ↪ Role) (n : ℕ) :
    (∀ g : Tree Role, g.choiceCount = n → (value g).val.ncard ≤ min (Nat.card Role) (n + 1)) ∧
    ∃ g : Tree Role, g.choiceCount = n ∧ (value g).val.ncard = min (Nat.card Role) (n + 1) := by
  obtain ⟨_, g, hc, _, hv⟩ := sharp_absorbing_budget three n 0 (Nat.zero_le _)
  exact ⟨fun g hg => by simpa [hg] using g.winner_budget, g, hc, by simpa using hv⟩

end KFOL.Strategic
