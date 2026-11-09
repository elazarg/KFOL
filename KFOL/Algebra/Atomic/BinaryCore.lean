module

public import KFOL.Algebra.Atomic.CoreSupport
public import KFOL.Reset.Basic

/-! # Binary atom-preserving core operations are projections or resets -/

@[expose] public section

namespace KFOL.Term

universe u

variable {Role : Type u}

private theorem binary_positions (i j : Fin 2) (hne : j ≠ i) (k : Fin 2) :
    k = i ∨ k = j := by omega

/-- A core atomic projection contains the projected variable. -/
theorem IsCore.projection_mem_vars {Var : Type*} [DecidableEq Var]
    {t : Term Role Var} (ht : t.IsCore) (three : Fin 3 ↪ Role) (i : Var)
    (hp : t.AtomicRealizes (fun v => v i)) : i ∈ t.vars := by
  classical
  by_contra hi
  let v : Var → Role := fun x => if x = i then three 0 else three 1
  have he : t.eval (fun x => WinnerSet.singleton (v x)) = WinnerSet.singleton (three 1) :=
    ht.eval_eq_of_support _ _ (fun x hx => by
      have hxi : x ≠ i := fun h => hi (h ▸ hx)
      simp [v,hxi])
  have hf : t.eval (fun x => WinnerSet.singleton (v x)) = WinnerSet.singleton (three 0) :=
    by simpa [v] using hp v
  exact three.injective.ne (by decide : (0 : Fin 3) ≠ 1)
    (WinnerSet.singleton_inj.mp (hf.symm.trans he))

/-- Freezing the projected argument at an atom forces the whole binary
context to that atom, even when the other argument is ambiguous. -/
theorem IsCore.binary_frozen_projection {t : Term Role (Fin 2)} (ht : t.IsCore)
    (three : Fin 3 ↪ Role) (i : Fin 2) (hp : t.AtomicRealizes (fun v => v i))
    (r : Role) (B : WinnerSet Role) :
    t.eval (fun k => if k = i then WinnerSet.singleton r else B) = WinnerSet.singleton r := by
  classical
  obtain ⟨q,hqr,_⟩ := exists_role_outside_pair three r r
  have htest : t.eval (fun k => if decide (k ≠ i) then WinnerSet.singleton q
      else WinnerSet.singleton r) = WinnerSet.singleton r := by
    simpa [apply_ite] using hp (fun k => if k = i then r else q)
  simpa using ht.one_constant_rigidity (fun k => decide (k ≠ i)) r q hqr htest B

/-- Freezing the other argument at an atom makes a core atomic projection
inflationary in the projected argument. -/
theorem IsCore.binary_inflationary_projection {t : Term Role (Fin 2)} (ht : t.IsCore)
    (three : Fin 3 ↪ Role) (i : Fin 2) (hp : t.AtomicRealizes (fun v => v i))
    (r : Role) (A : WinnerSet Role) :
    A.val ⊆ (t.eval (fun k => if k = i then A else WinnerSet.singleton r)).val := by
  classical
  obtain ⟨q,hqr,_⟩ := exists_role_outside_pair three r r
  have htest : t.eval (fun k => if decide (k = i) then WinnerSet.singleton q
      else WinnerSet.singleton r) = WinnerSet.singleton q := by
    simpa [apply_ite] using hp (fun k => if k = i then q else r)
  simpa using ht.one_constant_inflationary (fun k => decide (k = i)) r q hqr htest A

/-- An atomic binary projection either has no occurrence of its other input
and is the same projection globally, or has such an occurrence and is reset.
The assertion is about every winner-set valuation, including mixed cells. -/
theorem IsCore.binary_of_atomic_projection {t : Term Role (Fin 2)} (ht : t.IsCore)
    (three : Fin 3 ↪ Role) (i j : Fin 2) (hne : j ≠ i)
    (hp : t.AtomicRealizes (fun v => v i)) :
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = v i) ∨
    (∀ v : Fin 2 → WinnerSet Role, t.eval v = (v j).reset (v i)) := by
  classical
  by_cases hj : j ∈ t.vars
  · apply Or.inr
    intro v
    have hi : i ∈ t.vars := ht.projection_mem_vars three i hp
    have hv (k : Fin 2) : k = i ∨ k = j := binary_positions i j hne k
    by_cases hA : (v i).Ambiguous
    · rw [WinnerSet.reset_of_ambiguous _ _ hA]
      by_cases hB : (v j).Ambiguous
      · have hamb : ∀ k, (v k).Ambiguous := fun k => (hv k).elim
          (fun h => h ▸ hA) (fun h => h ▸ hB)
        apply Subtype.ext
        ext r
        rw [ht.eval_mem_iff v hamb r]
        change (∃ k ∈ t.vars, r ∈ (v k).val) ↔ r ∈ (v j).val ∨ r ∈ (v i).val
        constructor
        · rintro ⟨k,_,hr⟩
          exact (hv k).elim (fun h => Or.inr (h ▸ hr)) (fun h => Or.inl (h ▸ hr))
        · rintro (hr | hr)
          · exact ⟨j,hj,hr⟩
          · exact ⟨i,hi,hr⟩
      · obtain ⟨r,hr⟩ : ∃ r, v j = WinnerSet.singleton r := by
          simpa only [WinnerSet.Ambiguous,not_forall,not_not] using hB
        have he : (fun k => if k = i then v i else WinnerSet.singleton r) = v := by
          funext k
          rcases hv k with rfl | rfl
          · simp
          · simp [hne,hr]
        have hsub : (v i).val ⊆ (t.eval v).val := by
          simpa only [he] using ht.binary_inflationary_projection three i hp r (v i)
        have hatom : ∀ k, (v k).Ambiguous ∨ v k = WinnerSet.singleton r := by
          intro k
          exact (hv k).elim (fun h => Or.inl (h ▸ hA)) (fun h => Or.inr (h ▸ hr))
        have hmem : r ∈ (t.eval v).val := ht.atom_mem_of_occurs v r hatom j hj hr
        have hbound : (t.eval v).val ⊆ (v j).val ∪ (v i).val :=
          ht.eval_subset_of_support v _ (fun k _ => (hv k).elim
            (fun h => h ▸ Set.subset_union_right) (fun h => h ▸ Set.subset_union_left))
        apply Subtype.ext
        apply Set.Subset.antisymm hbound
        rintro s (hs | hs)
        · have hsr : s = r := by simpa [hr] using hs
          exact hsr ▸ hmem
        · exact hsub hs
    · obtain ⟨r,hr⟩ : ∃ r, v i = WinnerSet.singleton r := by
        simpa only [WinnerSet.Ambiguous,not_forall,not_not] using hA
      rw [hr,WinnerSet.reset_singleton]
      have he : (fun k => if k = i then WinnerSet.singleton r else v j) = v := by
        funext k
        rcases hv k with rfl | rfl
        · simp [hr]
        · simp [hne]
      simpa only [he] using ht.binary_frozen_projection three i hp r (v j)
  · apply Or.inl
    intro v
    exact ht.eval_eq_of_support v (v i) (fun k hk => by
      rcases binary_positions i j hne k with rfl | rfl
      · rfl
      · exact False.elim (hj hk))

end KFOL.Term
