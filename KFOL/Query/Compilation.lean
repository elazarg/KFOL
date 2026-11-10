module

public import KFOL.Definitions.Queries
public import KFOL.Algebra.ChoiceSupport
public import KFOL.Algebra.Views
public import KFOL.Definitions.PaperAlgebra
public import Mathlib.Tactic.Linarith

/-! # Exact navigation queries for public terms -/

@[expose] public section
namespace KFOL.Query
universe u v
variable {Role : Type u} {Var : Type v}

@[simp] theorem input_holds (valuation : Var → WinnerSet Role) (j : Var) (node : Node valuation) :
    (input j).Holds (document valuation) .root node ↔
      ∃ r ∈ (valuation j).val, node = .role r := by
  cases node with
  | root => simp [input, Path.Holds, Test.Holds, document]
  | mark r k h => simp [input, Path.Holds, Test.Holds, document]
  | role r =>
    simp only [input, Path.Holds, Test.Holds, document, true_and]
    constructor
    · rintro ⟨node, he, hm⟩
      cases node with
      | root => cases he
      | role s => cases he
      | mark s k h =>
        simp only at he hm
        subst s; subst k
        exact ⟨r, h, rfl⟩
    · rintro ⟨s, hs, he⟩
      cases Node.role.inj he
      exact ⟨.mark r j hs, rfl, rfl⟩

theorem nonOwner_holds [DecidableEq Role] (r : Role) (t : Term Role Var) (ht : t.IsPublic)
    (valuation : Var → WinnerSet Role) :
    (nonOwner r t ht).Holds (document valuation) .root ↔ t.eval valuation ≠ WinnerSet.singleton r := by
  induction t with
  | winner a =>
    by_cases h : a = r <;> simp [nonOwner, h, Term.eval, Test.Holds, WinnerSet.singleton_inj]
  | var j =>
    simp only [nonOwner, Test.Holds, Path.Holds]
    constructor
    · rintro ⟨node, selected, outside⟩
      obtain ⟨s, hs, rfl⟩ := (input_holds valuation j node).mp selected
      intro equal
      change valuation j = WinnerSet.singleton r at equal
      have sr : s = r := by simpa only [equal, WinnerSet.val_singleton, Set.mem_singleton_iff] using hs
      exact outside (congrArg Node.role sr)
    · intro hn
      obtain ⟨s, hs, hsr⟩ := WinnerSet.exists_mem_ne_of_ne_singleton r (valuation j) hn
      exact ⟨.role s, (input_holds valuation j _).mpr ⟨s, hs, rfl⟩,
        fun h => hsr (Node.role.inj h)⟩
  | choice a s t hs ht' =>
    by_cases ha : a = r
    · subst a
      simp only [nonOwner, ite_true, Test.Holds, hs ht.1, ht' ht.2, Term.eval]
      simp only [ne_eq]
      rw [WinnerSet.choice_eq_owner_iff]
      exact not_or.symm
    · simp only [nonOwner, ite_eq_right ha, Test.Holds, hs ht.1, ht' ht.2, Term.eval]
      simp only [ne_eq]
      rw [WinnerSet.choice_eq_other_iff _ _ _ ha]
      exact not_and_or.symm
  | rename p t => exact False.elim ht

theorem compile_holds [DecidableEq Role] (t : Term Role Var) (ht : t.IsPublic)
    (valuation : Var → WinnerSet Role) (node : Node valuation) :
    (compile t ht).Holds (document valuation) .root node ↔
      ∃ r ∈ (t.eval valuation).val, node = .role r := by
  induction t with
  | winner r =>
    cases node <;> simp [compile, Path.Holds, Test.Holds, document, Term.eval, WinnerSet.singleton]
  | var j => exact input_holds valuation j node
  | choice r s t hs ht' =>
    simp only [compile, Path.Holds, Test.Holds, hs ht.1, ht' ht.2]
    constructor
    · rintro ⟨(⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩), eligible⟩
      all_goals
        refine ⟨a, ?_, rfl⟩
        by_cases ar : a = r
        · subst a
          apply (WinnerSet.mem_choice_owner r _ _).mpr
          first | exact Or.inl ha | exact Or.inr ha
        · obtain equal | ⟨parent, edge, left, right⟩ := eligible
          · exact (ar (Node.role.inj equal)).elim
          · cases parent with
            | root =>
              have hleft := (nonOwner_holds r s ht.1 valuation).mp left
              have hright := (nonOwner_holds r t ht.2 valuation).mp right
              apply (WinnerSet.mem_choice_other r a (Ne.symm ar) _ _).mpr
              first | exact ⟨Or.inl ha, hleft, hright⟩ | exact ⟨Or.inr ha, hleft, hright⟩
            | role b => cases edge
            | mark b j hj => cases edge
    · rintro ⟨a, ha, rfl⟩
      by_cases ar : a = r
      · subst a
        obtain h | h := (WinnerSet.mem_choice_owner r _ _).mp ha
        · exact ⟨Or.inl ⟨r, h, rfl⟩, Or.inl rfl⟩
        · exact ⟨Or.inr ⟨r, h, rfl⟩, Or.inl rfl⟩
      · obtain ⟨hm, hleft, hright⟩ := (WinnerSet.mem_choice_other r a (Ne.symm ar) _ _).mp ha
        refine ⟨hm.elim (fun h => Or.inl ⟨a,h,rfl⟩) (fun h => Or.inr ⟨a,h,rfl⟩),
          Or.inr ⟨.root, trivial, ?_, ?_⟩⟩
        · exact (nonOwner_holds r s ht.1 valuation).mpr hleft
        · exact (nonOwner_holds r t ht.2 valuation).mpr hright
  | rename p t => exact False.elim ht

theorem nonOwner_size [DecidableEq Role] (r : Role) (t : Term Role Var) (ht : t.IsPublic) :
    (nonOwner r t ht).size ≤ 9 * t.size := by
  induction t with
  | winner a => simp only [nonOwner]; split <;> simp [Test.size, Term.size]
  | var j => simp [nonOwner, input, Test.size, Path.size, Term.size]
  | choice a s t hs ht' =>
    have hleft := hs ht.1
    have hright := ht' ht.2
    simp only [nonOwner]; split <;> simp only [Test.size, Term.size] <;> omega
  | rename p t => exact False.elim ht

theorem compile_size [DecidableEq Role] (t : Term Role Var) (ht : t.IsPublic) :
    (compile t ht).size ≤ 12 * t.size ^ 2 := by
  induction t with
  | winner r => simp [compile, Path.size, Test.size, Term.size]
  | var j => simp [compile, input, Path.size, Test.size, Term.size]
  | choice r s t hs ht' =>
    have hleft := hs ht.1
    have hright := ht' ht.2
    have hns := nonOwner_size r s ht.1
    have hnt := nonOwner_size r t ht.2
    simp only [compile, Path.size, Test.size, Term.size]
    nlinarith
  | rename p t => exact False.elim ht

/-- Exact equivalence on the valuation-document schema, not on arbitrary XML
trees: every nonempty valuation has its own canonical document. -/
theorem compile_equivalence [DecidableEq Role] (s t : Term Role Var)
    (hs : s.IsPublic) (ht : t.IsPublic) :
    (∀ (valuation : Var → WinnerSet Role) (node : Node valuation),
      (compile s hs).Holds (document valuation) .root node ↔
        (compile t ht).Holds (document valuation) .root node) ↔ s.Equivalent t := by
  constructor
  · intro equal valuation
    apply Subtype.ext
    ext r
    have observed := equal valuation (.role r)
    simpa [compile_holds] using observed
  · intro equal valuation node
    rw [compile_holds, compile_holds, equal valuation]

theorem public_compilation [DecidableEq Role] (t : Term Role Var) (ht : t.IsPublic) :
    (∀ (valuation : Var → WinnerSet Role) (node : Node valuation),
      (compile t ht).Holds (document valuation) .root node ↔
        ∃ r ∈ (t.eval valuation).val, node = .role r) ∧
    (compile t ht).size ≤ 12 * t.size ^ 2 :=
  ⟨compile_holds t ht, compile_size t ht⟩

end KFOL.Query
