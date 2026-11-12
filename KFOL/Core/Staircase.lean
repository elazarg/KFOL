module

public import KFOL.Definitions.CoreStaircase
public import KFOL.Algebra.Idempotent
public import Mathlib.Data.Fintype.Fin

/-! # Omission independence and unbounded negative-budget Helly obstructions

An omitted owner makes every input containing that owner irrelevant. Along
an atomic staircase this would identify the two distinct constant endpoints
if the owner were omitted on every row. Deleting any row admits its column
projection.
-/

@[expose] public section
namespace KFOL.Core
universe u v
variable {Role : Type u} {Var : Type v}

/-- If a core output omits an owner, arbitrary changes to input menus containing
that owner leave the entire output unchanged. -/
theorem omission_independence (a : Role) (t : Term Role Var) (ht : t.IsCore)
    (values changed : Var → WinnerSet Role)
    (agree : ∀ j, a ∉ (values j).val → changed j = values j)
    (habsent : a ∉ (t.eval values).val) : t.eval changed = t.eval values := by
  classical
  induction t with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var j => exact agree j habsent
  | choice r s t hs ht' =>
    change WinnerSet.choice r (s.eval changed) (t.eval changed) =
      WinnerSet.choice r (s.eval values) (t.eval values)
    by_cases hleft : s.eval values = WinnerSet.singleton r
    · have hparent : WinnerSet.choice r (s.eval values) (t.eval values) =
          WinnerSet.singleton r := by simp [WinnerSet.choice, hleft]
      have hleftomit : a ∉ (s.eval values).val := by
        rw [hleft, ← hparent]
        exact habsent
      have hsame := hs ht.1 hleftomit
      simp [WinnerSet.choice, hleft, hsame]
    · by_cases hright : t.eval values = WinnerSet.singleton r
      · have hparent : WinnerSet.choice r (s.eval values) (t.eval values) =
            WinnerSet.singleton r := by simp [WinnerSet.choice, hright]
        have hrightomit : a ∉ (t.eval values).val := by
          rw [hright, ← hparent]
          exact habsent
        have hsame := ht' ht.2 hrightomit
        simp [WinnerSet.choice, hright, hsame]
      · have hchildren : a ∉ (s.eval values).val ∧ a ∉ (t.eval values).val := by
          simpa only [Term.eval, WinnerSet.choice, hleft, hright, or_self, ite_false,
            WinnerSet.val_union, Set.mem_union, not_or] using habsent
        rw [hs ht.1 hchildren.1, ht' ht.2 hchildren.2]

namespace Staircase

private theorem prefix_agrees (a b c : Role) {n : Nat} (i j : Fin n)
    (h : a ∉ (row a b c i j).val) : vertex b c i.val j = row a b c i j := by
  by_cases hji : j.val < i.val
  · simp only [vertex, row, hji, ite_true]
  · have hne : j ≠ i := by
      intro he
      subst j
      simp [row] at h
    simp only [vertex, row, hji, hne, ite_false]

private theorem prefix_succ_agrees (a b c : Role) {n : Nat} (i j : Fin n)
    (h : a ∉ (row a b c i j).val) : vertex b c (i.val + 1) j = row a b c i j := by
  by_cases hji : j.val < i.val
  · have hj : j.val < i.val + 1 := by omega
    simp only [vertex, row, hji, hj, ite_true]
  · have hne : j ≠ i := by
      intro he
      subst j
      simp [row] at h
    have hj : ¬j.val < i.val + 1 := by
      have hvals : j.val ≠ i.val := fun he => hne (Fin.ext he)
      omega
    simp only [vertex, row, hji, hne, hj, ite_false]

/-- Every core term includes the tracked owner on some atomic staircase row. -/
theorem exists_membership (a b c : Role) (hbc : b ≠ c) {n : Nat}
    (t : Term Role (Fin n)) (ht : t.IsCore) :
    ∃ i : Fin n, a ∈ (t.eval (row a b c i)).val := by
  classical
  by_contra hn
  have hzero : ∀ i : Fin n, a ∉ (t.eval (row a b c i)).val := by
    simpa only [not_exists] using hn
  have hstep (k : Nat) (hk : k < n) :
      t.eval (vertex b c k) = t.eval (vertex b c (k + 1)) := by
    let i : Fin n := ⟨k, hk⟩
    have hleft := omission_independence a t ht (row a b c i) (vertex b c k)
      (fun j hj => prefix_agrees a b c i j hj) (hzero i)
    have hright := omission_independence a t ht (row a b c i) (vertex b c (k + 1))
      (fun j hj => prefix_succ_agrees a b c i j hj) (hzero i)
    exact hleft.trans hright.symm
  have hchain : ∀ k, k ≤ n → t.eval (vertex b c 0) = t.eval (vertex b c k) := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => exact (ih (by omega)).trans (hstep k (by omega))
  have hends := hchain n le_rfl
  have hstart : vertex b c (n := n) 0 = fun _ => WinnerSet.singleton b := by
    funext j
    simp [vertex]
  have hend : vertex b c (n := n) n = fun _ => WinnerSet.singleton c := by
    funext j
    simp [vertex, j.isLt]
  rw [hstart, hend, ht.eval_diagonal, ht.eval_diagonal] at hends
  exact hbc (WinnerSet.singleton_inj.mp hends)

/-- The column projection for a deleted row avoids the tracked owner at every
remaining row. -/
theorem projection_avoids (a b c : Role) (hab : a ≠ b) (hac : a ≠ c)
    {n : Nat} (deleted i : Fin n) (hi : i ≠ deleted) :
    a ∉ ((Term.var deleted : Term Role (Fin n)).eval (row a b c i)).val := by
  change a ∉ (row a b c i deleted).val
  simp only [row]
  split
  · simpa using hac
  · simp only [Ne.symm hi, ite_false, WinnerSet.val_singleton, Set.mem_singleton_iff]
    exact hab

/-- Atomic rows give arbitrarily large negative-budget obstructions, with an
explicit column projection satisfying every proper subfamily. -/
theorem exists_atomic_irredundant_negative_budgets (three : Fin 3 ↪ Role) (n : Nat) :
    ∃ values : Fin n → Fin n → WinnerSet Role,
      (∀ i j, ∃ r : Fin 3, values i j = WinnerSet.singleton (three r)) ∧
      (∀ S : Finset (Fin n), S ≠ Finset.univ →
        ∃ j : Fin n, ∀ i ∈ S, three 0 ∉ (values i j).val) ∧
      ¬∃ t : Term Role (Fin n), t.IsCore ∧
        ∀ i, three 0 ∉ (t.eval (values i)).val := by
  classical
  refine ⟨row (three 0) (three 1) (three 2), ?_, ?_, ?_⟩
  · intro i j
    unfold row
    split
    · exact ⟨2, rfl⟩
    · split
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  · intro S hS
    have hex : ∃ j : Fin n, j ∉ S := by
      by_contra hn
      apply hS
      exact Finset.eq_univ_of_forall (by simpa only [not_exists, not_not] using hn)
    obtain ⟨j, hj⟩ := hex
    refine ⟨j, fun i hi => ?_⟩
    exact projection_avoids _ _ _ (three.injective.ne (by decide))
      (three.injective.ne (by decide)) j i (fun he => hj (he ▸ hi))
  · rintro ⟨t, ht, h⟩
    obtain ⟨i, hi⟩ := exists_membership (three 0) (three 1) (three 2)
      (three.injective.ne (by decide)) t ht
    exact h i hi

/-- Arbitrarily large negative upper-budget obstructions exist: every proper
subfamily is feasible by a projection, while the whole family is infeasible. -/
theorem exists_irredundant_negative_budgets (three : Fin 3 ↪ Role) (n : Nat) :
    ∃ values : Fin n → Fin n → WinnerSet Role,
      (∀ S : Finset (Fin n), S ≠ Finset.univ →
        ∃ t : Term Role (Fin n), t.IsCore ∧
          ∀ i ∈ S, three 0 ∉ (t.eval (values i)).val) ∧
      ¬∃ t : Term Role (Fin n), t.IsCore ∧
        ∀ i, three 0 ∉ (t.eval (values i)).val := by
  obtain ⟨values, _, hprojections, hnot⟩ := exists_atomic_irredundant_negative_budgets three n
  refine ⟨values, ?_, hnot⟩
  intro S hS
  obtain ⟨j, hj⟩ := hprojections S hS
  exact ⟨.var j, trivial, hj⟩

end Staircase
end KFOL.Core
