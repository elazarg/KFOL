module

public import KFOL.Reset.Antimatroid.Basic

/-! # Accessible orders of finite feasible sets -/

@[expose] public section

namespace KFOL.Reset.RootedAntimatroid

universe v

variable {Var : Type v} [DecidableEq Var]

/-- The list gives the tail of an accessible order starting at the unique root.
Every prefix, including the empty tail, is independently required to be feasible. -/
structure FeasibleOrder (F : RootedAntimatroid Var) (xs : List Var) : Prop where
  nodup : xs.Nodup
  root_not_mem : F.root ∉ xs
  prefix_mem : ∀ n, insert F.root (xs.take n).toFinset ∈ F.feasible

namespace FeasibleOrder

variable {F : RootedAntimatroid Var} {xs : List Var}

theorem support_mem (h : F.FeasibleOrder xs) : insert F.root xs.toFinset ∈ F.feasible := by
  simpa only [List.take_length] using h.prefix_mem xs.length

theorem nil (F : RootedAntimatroid Var) : F.FeasibleOrder [] :=
  ⟨by simp, by simp, fun _ => by simpa using F.root_mem⟩

/-- A fresh enabled position extends an accessible order. -/
theorem append (h : F.FeasibleOrder xs) (a : Var)
    (ha : a ∉ insert F.root xs.toFinset)
    (hfeas : insert a (insert F.root xs.toFinset) ∈ F.feasible) :
    F.FeasibleOrder (xs ++ [a]) := by
  have har : a ≠ F.root := fun he => ha (he ▸ Finset.mem_insert_self _ _)
  have hax : a ∉ xs := fun hm => ha (Finset.mem_insert_of_mem (List.mem_toFinset.mpr hm))
  constructor
  · rw [List.nodup_append]
    refine ⟨h.nodup, by simp, ?_⟩
    intro x hx b hb
    have he : b = a := List.mem_singleton.mp hb
    subst b
    intro hxa
    exact hax (hxa ▸ hx)
  · simpa only [List.mem_append, List.mem_singleton, not_or] using
      ⟨h.root_not_mem, Ne.symm har⟩
  · intro n
    by_cases hn : n ≤ xs.length
    · rw [List.take_append_of_le_length hn]
      exact h.prefix_mem n
    · have hl : (xs ++ [a]).length ≤ n := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [List.take_of_length_le hl]
      have he : insert F.root (xs ++ [a]).toFinset = insert a (insert F.root xs.toFinset) := by
        ext x
        simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
          Finset.mem_insert, Finset.mem_union, Finset.notMem_empty, or_false]
        tauto
      rw [he]
      exact hfeas

/-- Every prefix ending at one selected position is a feasible set. -/
theorem prefix_insert {j : Var} {before after : List Var} (h : F.FeasibleOrder xs)
    (he : xs = before ++ j :: after) :
    insert j (insert F.root before.toFinset) ∈ F.feasible := by
  have hp := h.prefix_mem (before.length + 1)
  rw [he, List.take_append] at hp
  simpa [List.take_of_length_le (Nat.le_succ before.length), Finset.insert_comm] using hp

end FeasibleOrder

/-- Accessibility supplies an order for every nonempty feasible set, with its
actual finite support; unused declared positions are never enumerated. -/
theorem exists_order (F : RootedAntimatroid Var) {A : Finset Var}
    (hA : A ∈ F.feasible) (hne : A.Nonempty) :
    ∃ xs : List Var, F.FeasibleOrder xs ∧ insert F.root xs.toFinset = A := by
  induction hn : A.card using Nat.strong_induction_on generalizing A with
  | h n ih =>
    obtain ⟨a, ha, he⟩ := F.accessible A hA hne
    by_cases hempty : A.erase a = ∅
    · have har : a = F.root := by
        apply F.singleton_unique
        have hs : A = {a} := by
          apply Finset.Subset.antisymm
          · intro x hx
            by_cases hxa : x = a
            · exact Finset.mem_singleton.mpr hxa
            · have bad := Finset.mem_erase.mpr ⟨hxa, hx⟩
              rw [hempty] at bad
              simp at bad
          · exact Finset.singleton_subset_iff.mpr ha
        rwa [← hs]
      refine ⟨[], FeasibleOrder.nil F, ?_⟩
      have hs := Finset.insert_erase ha
      rw [hempty] at hs
      simpa only [List.toFinset_nil, har] using hs
    · have hc : (A.erase a).card < n := by
        rw [← hn]
        exact Finset.card_lt_card (Finset.erase_ssubset ha)
      obtain ⟨xs, hxs, hs⟩ := ih _ hc he (Finset.nonempty_iff_ne_empty.mpr hempty) rfl
      have hfresh : a ∉ insert F.root xs.toFinset := by rw [hs]; simp
      have hnew : insert a (insert F.root xs.toFinset) ∈ F.feasible := by
        rw [hs, Finset.insert_erase ha]
        exact hA
      refine ⟨xs ++ [a], hxs.append a hfresh hnew, ?_⟩
      have heq : insert F.root (xs ++ [a]).toFinset = insert a (insert F.root xs.toFinset) := by
        simp [Finset.insert_comm]
      rw [heq, hs, Finset.insert_erase ha]

end KFOL.Reset.RootedAntimatroid
