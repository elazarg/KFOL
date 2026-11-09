module

public import KFOL.Definitions.Policies
public import KFOL.Owner.Basic

/-! Exact policy operation semantics and independent syntactic root status. -/

@[expose] public section

namespace KFOL

universe u v w

namespace WinnerSet

variable {Role : Type u}

@[simp] theorem policyBlocks_pair (a b : Role) (Y : WinnerSet Role) :
    PolicyBlocks {a, b} Y ↔ Y = singleton a ∨ Y = singleton b := by
  constructor
  · rintro ⟨r, hr, hY⟩
    rcases hr with rfl | hr
    · exact Or.inl hY
    · exact Or.inr ((Set.mem_singleton_iff.mp hr) ▸ hY)
  · rintro (hY | hY)
    · exact ⟨a, Or.inl rfl, hY⟩
    · exact ⟨b, Or.inr rfl, hY⟩

@[simp] theorem policyPasses_singleton (D : Set Role) (k r : Role) :
    PolicyPasses D k (singleton r) ↔ r ∉ D ∨ r = k := by
  classical
  constructor
  · intro h
    by_cases hr : r ∈ D
    · right
      by_contra hn
      exact h r hr hn rfl
    · exact Or.inl hr
  · rintro (hr | rfl) s hs hsk he
    · exact hr ((singleton_inj.mp he) ▸ hs)
    · exact hsk (singleton_inj.mp he).symm

theorem policyPasses_of_ambiguous (D : Set Role) (k : Role) (Y : WinnerSet Role)
    (hY : Y.Ambiguous) : PolicyPasses D k Y := fun r _ _ => hY r

theorem policyPasses_of_mem (D : Set Role) (k : Role) (Y : WinnerSet Role)
    (hk : k ∈ Y.val) : PolicyPasses D k Y := by
  intro r _ hr he
  rw [he] at hk
  exact hr (Set.mem_singleton_iff.mp hk).symm

@[simp] theorem selective_self (D : Set Role) (Y : WinnerSet Role) : selective D Y Y = Y := by
  classical
  by_cases hb : PolicyBlocks D Y <;> simp [selective, hb, union_self]

theorem mem_selective (D : Set Role) (Z Y : WinnerSet Role) (k : Role) :
    k ∈ (selective D Z Y).val ↔ k ∈ Y.val ∨ (PolicyPasses D k Y ∧ k ∈ Z.val) := by
  classical
  by_cases hb : PolicyBlocks D Y
  · have hselect : selective D Z Y = Y := by simp only [selective, hb, ite_true]
    rw [hselect]
    constructor
    · exact Or.inl
    · rintro (hy | ⟨hp, _⟩)
      · exact hy
      · obtain ⟨r, hr, hY⟩ := hb
        by_cases he : r = k
        · simp only [hY, he, val_singleton, Set.mem_singleton_iff]
        · exact False.elim (hp r hr he hY)
  · have hp : PolicyPasses D k Y := by
      intro r hr _ hY
      exact hb ⟨r, hr, hY⟩
    simp only [selective, ite_eq_right hb, val_union, Set.mem_union, hp, true_and]

theorem mem_policyReset (D : Set Role) (X Y Z : WinnerSet Role) (k : Role) :
    k ∈ (policyReset D X Y Z).val ↔ k ∈ X.val ∨
      (X.Ambiguous ∧ (k ∈ Y.val ∨ (PolicyPasses D k Y ∧ k ∈ Z.val))) := by
  rw [policyReset, mem_reset, mem_selective]

@[simp] theorem ambiguous_policyReset (D : Set Role) (X Y Z : WinnerSet Role) :
    (policyReset D X Y Z).Ambiguous ↔ X.Ambiguous := ambiguous_reset _ _

@[simp] theorem policyReset_eq_singleton (D : Set Role) (X Y Z : WinnerSet Role) (r : Role) :
    policyReset D X Y Z = singleton r ↔ X = singleton r := reset_eq_singleton _ _ r

/-- Every policy symbol alone defines reset, including both endpoint policies. -/
theorem policyReset_minor (D : Set Role) (X Y : WinnerSet Role) : policyReset D Y X X = X.reset Y := by
  rw [policyReset, selective_self]

@[simp] theorem policyReset_self (D : Set Role) (X : WinnerSet Role) : policyReset D X X X = X := by
  rw [policyReset_minor, reset_self]

end WinnerSet

namespace Policies.Term

variable {Role : Type u} {Label : Type w} {Var : Type v}

@[simp] theorem root_var (j : Var) : root (.var j : Term Label Var) = j := rfl
@[simp] theorem root_step (s t : Term Label Var) : (step s t).root = t.root := rfl
@[simp] theorem root_selective (d : Label) (x y z : Term Label Var) : (selective d x y z).root = x.root := rfl

@[simp] theorem eval_var (D : Label → Set Role) (j : Var) (v : Var → WinnerSet Role) :
    eval D (.var j) v = v j := rfl
@[simp] theorem eval_step (D : Label → Set Role) (s t : Term Label Var) (v : Var → WinnerSet Role) :
    (step s t).eval D v = (s.eval D v).reset (t.eval D v) := rfl
@[simp] theorem eval_selective (D : Label → Set Role) (d : Label) (x y z : Term Label Var) (v : Var → WinnerSet Role) :
    (selective d x y z).eval D v = WinnerSet.policyReset (D d) (x.eval D v) (y.eval D v) (z.eval D v) := rfl

@[elab_as_elim] theorem induction_policy {P : Term Label Var → Prop}
    (var : ∀ j, P (.var j))
    (step : ∀ s t, P s → P t → P (Term.step s t))
    (selective : ∀ d x y z, P x → P y → P z → P (Term.selective d x y z))
    (t : Term Label Var) : P t := by
  induction t with
  | var j => exact var j
  | @func n f args ih =>
    cases f with
    | reset =>
      have he : FirstOrder.Language.Term.func Symbol.reset args = Term.step (args 0) (args 1) := by
        congr 1
        funext i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;> rfl
      rw [he]
      exact step _ _ (ih 0) (ih 1)
    | selective d =>
      have he : FirstOrder.Language.Term.func (Symbol.selective d) args =
          Term.selective d (args 0) (args 1) (args 2) := by
        congr 1
        funext i
        have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        rcases hi with rfl | rfl | rfl <;> rfl
      rw [he]
      exact selective _ _ _ _ (ih 0) (ih 1) (ih 2)

theorem ambiguous_iff (D : Label → Set Role) (t : Term Label Var) (v : Var → WinnerSet Role) :
    (t.eval D v).Ambiguous ↔ (v t.root).Ambiguous := by
  induction t using induction_policy with
  | var => rfl
  | step s t _ ht => exact (WinnerSet.ambiguous_reset _ _).trans ht
  | selective d x y z hx _ _ => exact (WinnerSet.ambiguous_policyReset _ _ _ _).trans hx

theorem eq_singleton_iff (D : Label → Set Role) (t : Term Label Var) (v : Var → WinnerSet Role) (r : Role) :
    t.eval D v = WinnerSet.singleton r ↔ v t.root = WinnerSet.singleton r := by
  induction t using induction_policy with
  | var => rfl
  | step s t _ ht => exact (WinnerSet.reset_eq_singleton _ _ r).trans ht
  | selective d x y z hx _ _ => exact (WinnerSet.policyReset_eq_singleton _ _ _ _ r).trans hx

theorem policyPasses_iff (D : Label → Set Role) (t : Term Label Var) (v : Var → WinnerSet Role)
    (E : Set Role) (k : Role) :
    WinnerSet.PolicyPasses E k (t.eval D v) ↔ WinnerSet.PolicyPasses E k (v t.root) := by
  constructor
  · intro ht r hr hrk he
    exact ht r hr hrk ((t.eq_singleton_iff D v r).mpr he)
  · intro ht r hr hrk he
    exact ht r hr hrk ((t.eq_singleton_iff D v r).mp he)

end Policies.Term
end KFOL
