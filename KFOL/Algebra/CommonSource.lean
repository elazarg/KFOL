module

public import KFOL.Algebra.Basic
public import KFOL.Definitions.Core

/-!
# A common syntactic source for disjoint output constraints

At each owned node, one child satisfies every constraint simultaneously.
Switches pull back target regions, preserving disjointness. Descent reaches
an actual source occurrence with its accumulated permutation. Two distinct
regions exclude winner leaves, since their permuted singleton is fixed.
-/

@[expose] public section

namespace KFOL

universe u v w

namespace WinnerSet

variable {Role : Type u} {Index : Type w}

/-- A single child of owned choice satisfies all disjoint constraints at once.
No finiteness or nonemptiness assumptions on the index type are needed. -/
theorem choice_common_side (r : Role) (A B : Index → WinnerSet Role)
    (W : Index → Set Role) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (h : ∀ i, (choice r (A i) (B i)).val ⊆ W i) :
    (∀ i, (A i).val ⊆ W i) ∨ (∀ i, (B i).val ⊆ W i) := by
  classical
  by_cases hA : ∀ i, (A i).val ⊆ W i
  · exact Or.inl hA
  · right
    obtain ⟨i, hi⟩ := Classical.not_forall.mp hA
    have collapse : A i = singleton r ∨ B i = singleton r := by
      apply Classical.byContradiction
      intro hn
      apply hi
      intro x hx
      apply h i
      simp only [choice, ite_eq_right hn, val_union]
      exact Or.inl hx
    have hr : r ∈ W i := h i (by simp [choice, collapse])
    have hB : B i = singleton r := by
      rcases collapse with hc | hc
      · exact False.elim (hi (by
          intro x hx
          have hxr : x = r := by simpa [hc] using hx
          exact hxr ▸ hr))
      · exact hc
    intro j x hx
    by_cases he : j = i
    · subst j
      have hxr : x = r := by simpa [hB] using hx
      exact hxr ▸ hr
    · have hnr : r ∉ W j := fun hj => Set.disjoint_left.mp (hW (Ne.symm he)) hr hj
      have hn : ¬(A j = singleton r ∨ B j = singleton r) := by
        intro hc
        exact hnr (h j (by simp [choice, hc]))
      apply h j
      simp only [choice, ite_eq_right hn, val_union]
      exact Or.inr hx

end WinnerSet

namespace Term

variable {Role : Type u} {Var : Type v} {Index : Type w}

/-- The variable part of the complete source enumeration agrees with the
already-used input occurrence list. This connects both views of the syntax. -/
theorem mem_inputOccurrences_iff (t : Term Role Var) (x : Var) (p : Equiv.Perm Role) :
    (x, p) ∈ t.inputOccurrences ↔ (.inr x, p) ∈ t.sourceOccurrences := by
  induction t generalizing x p with
  | winner => simp [inputOccurrences, sourceOccurrences]
  | var y => simp [inputOccurrences, sourceOccurrences]
  | choice r s t hs ht =>
    simp only [inputOccurrences, sourceOccurrences, List.mem_append, hs, ht]
  | rename q t ih =>
    simp only [inputOccurrences, sourceOccurrences, List.mem_map]
    constructor
    · rintro ⟨⟨y, a⟩, ha, he⟩
      cases he
      exact ⟨(.inr y, a), (ih y a).mp ha, rfl⟩
    · rintro ⟨⟨leaf, a⟩, ha, he⟩
      cases leaf with
      | inl r => cases he
      | inr y =>
        cases he
        exact ⟨(x, a), (ih x a).mpr ha, rfl⟩

/-- One source occurrence meets every disjoint target constraint simultaneously.
Regions may be empty, and the index type may be empty or infinite. -/
theorem exists_common_source (t : Term Role Var) (v : Index → Var → WinnerSet Role)
    (W : Index → Set Role) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (h : ∀ i, (t.eval (v i)).val ⊆ W i) :
    ∃ (leaf : Role ⊕ Var) (p : Equiv.Perm Role), (leaf, p) ∈ t.sourceOccurrences ∧
      ∀ i, (WinnerSet.rename p (leaf.elim WinnerSet.singleton (v i))).val ⊆ W i := by
  induction t generalizing W with
  | winner r =>
    refine ⟨.inl r, 1, by simp [sourceOccurrences], ?_⟩
    intro i
    simpa only [Sum.elim_inl, eval, WinnerSet.rename_one] using h i
  | var x =>
    refine ⟨.inr x, 1, by simp [sourceOccurrences], ?_⟩
    intro i
    simpa only [Sum.elim_inr, eval, WinnerSet.rename_one] using h i
  | choice r s t hs ht =>
    rcases WinnerSet.choice_common_side r (fun i => s.eval (v i))
        (fun i => t.eval (v i)) W hW h with hh | hh
    · obtain ⟨leaf, p, hp, he⟩ := hs W hW hh
      exact ⟨leaf, p, List.mem_append_left _ hp, he⟩
    · obtain ⟨leaf, p, hp, he⟩ := ht W hW hh
      exact ⟨leaf, p, List.mem_append_right _ hp, he⟩
  | rename q t ih =>
    let W' : Index → Set Role := fun i => q ⁻¹' W i
    have hW' : Pairwise fun i j => Disjoint (W' i) (W' j) := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp (hW hij) hx hy
    have hh : ∀ i, (t.eval (v i)).val ⊆ W' i :=
      fun i x hx => h i ⟨x, hx, rfl⟩
    obtain ⟨leaf, p, hp, he⟩ := ih W' hW' hh
    refine ⟨leaf, q * p, List.mem_map.mpr ⟨(leaf, p), hp, rfl⟩, ?_⟩
    intro i
    rw [WinnerSet.rename_mul]
    rintro y ⟨x, hx, rfl⟩
    exact he i hx

/-- With at least two disjoint regions, the common source is an input leaf. -/
theorem exists_common_input (t : Term Role Var) (v : Index → Var → WinnerSet Role)
    (W : Index → Set Role) (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (i j : Index) (hij : i ≠ j) (h : ∀ k, (t.eval (v k)).val ⊆ W k) :
    ∃ (x : Var) (p : Equiv.Perm Role), (x, p) ∈ t.inputOccurrences ∧
      ∀ k, (WinnerSet.rename p (v k x)).val ⊆ W k := by
  obtain ⟨leaf, p, hp, he⟩ := t.exists_common_source v W hW h
  cases leaf with
  | inl r =>
    have hi : p r ∈ W i := he i ⟨r, rfl, rfl⟩
    have hj : p r ∈ W j := he j ⟨r, rfl, rfl⟩
    exact False.elim (Set.disjoint_left.mp (hW hij) hi hj)
  | inr x => exact ⟨x, p, (t.mem_inputOccurrences_iff x p).mpr hp, he⟩

/-- The same selected occurrence is forced to be a variable whenever the
constraint family has at least two members. -/
theorem exists_common_source_with_input_clause (t : Term Role Var)
    (v : Index → Var → WinnerSet Role) (W : Index → Set Role)
    (hW : Pairwise fun i j => Disjoint (W i) (W j))
    (h : ∀ i, (t.eval (v i)).val ⊆ W i) :
    ∃ (leaf : Role ⊕ Var) (p : Equiv.Perm Role), (leaf, p) ∈ t.sourceOccurrences ∧
      (∀ i, (WinnerSet.rename p (leaf.elim WinnerSet.singleton (v i))).val ⊆ W i) ∧
      ((∃ i j : Index, i ≠ j) →
        ∃ x : Var, leaf = .inr x ∧ (x, p) ∈ t.inputOccurrences) := by
  obtain ⟨leaf, p, hp, he⟩ := t.exists_common_source v W hW h
  refine ⟨leaf, p, hp, he, ?_⟩
  rintro ⟨i, j, hij⟩
  cases leaf with
  | inr x => exact ⟨x, rfl, (t.mem_inputOccurrences_iff x p).mpr hp⟩
  | inl r =>
    exact False.elim (Set.disjoint_left.mp (hW hij)
      (he i ⟨r, rfl, rfl⟩) (he j ⟨r, rfl, rfl⟩))

/-- Distinct singleton outputs are explained by one common input occurrence
and its accumulated role permutation. -/
theorem exists_common_atomic_input (t : Term Role Var) (v : Index → Var → Role)
    (out : Index → Role) (ho : Function.Injective out) (i j : Index) (hij : i ≠ j)
    (h : ∀ k, t.eval (fun x => WinnerSet.singleton (v k x)) = WinnerSet.singleton (out k)) :
    ∃ (x : Var) (p : Equiv.Perm Role), (x, p) ∈ t.inputOccurrences ∧
      ∀ k, p (v k x) = out k := by
  have hW : Pairwise fun k l => Disjoint ({out k} : Set Role) {out l} := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro a ha hb
    exact hkl (ho (ha.symm.trans hb))
  have hh : ∀ k, (t.eval (fun x => WinnerSet.singleton (v k x))).val ⊆ {out k} := by
    intro k
    rw [h k]
    exact Set.Subset.rfl
  obtain ⟨x, p, hp, he⟩ := t.exists_common_input (fun k x => WinnerSet.singleton (v k x))
    (fun k => {out k}) hW i j hij hh
  exact ⟨x, p, hp, fun k => he k ⟨v k x, rfl, rfl⟩⟩

private theorem injective_of_three_ne (out : Fin 3 → Role)
    (h01 : out 0 ≠ out 1) (h02 : out 0 ≠ out 2) (h12 : out 1 ≠ out 2) :
    Function.Injective out := by
  intro i j he
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp_all

/-- If every input column has a repeated entry, three atomic outputs must
also repeat. No global atom-preservation hypothesis on the term is needed. -/
theorem atomic_preserves_repeat_triple (t : Term Role Var) (v : Fin 3 → Var → Role)
    (hv : ∀ x, v 0 x = v 1 x ∨ v 0 x = v 2 x ∨ v 1 x = v 2 x)
    (out : Fin 3 → Role)
    (h : ∀ i, t.eval (fun x => WinnerSet.singleton (v i x)) = WinnerSet.singleton (out i)) :
    out 0 = out 1 ∨ out 0 = out 2 ∨ out 1 = out 2 := by
  apply Classical.byContradiction
  intro hn
  have h01 : out 0 ≠ out 1 := fun h => hn (Or.inl h)
  have h02 : out 0 ≠ out 2 := fun h => hn (Or.inr (Or.inl h))
  have h12 : out 1 ≠ out 2 := fun h => hn (Or.inr (Or.inr h))
  obtain ⟨x, p, _, hp⟩ := t.exists_common_atomic_input v out
    (injective_of_three_ne out h01 h02 h12) 0 1 (by decide) h
  rcases hv x with hx | hx | hx
  · exact h01 ((hp 0).symm.trans ((congrArg p hx).trans (hp 1)))
  · exact h02 ((hp 0).symm.trans ((congrArg p hx).trans (hp 2)))
  · exact h12 ((hp 1).symm.trans ((congrArg p hx).trans (hp 2)))

/-- The full language cannot implement an atomic if-then-else between any
two distinct control labels, even if other control inputs are unrestricted. -/
theorem not_atom_ifThenElse (three : Fin 3 ↪ Role) (a b : Role) (hab : a ≠ b)
    (t : Term Role (Fin 3)) :
    ¬((∀ y z : Role, t.eval (fun i => WinnerSet.singleton
        (if i = 0 then a else if i = 1 then y else z)) = WinnerSet.singleton y) ∧
      (∀ y z : Role, t.eval (fun i => WinnerSet.singleton
        (if i = 0 then b else if i = 1 then y else z)) = WinnerSet.singleton z)) := by
  rintro ⟨ha, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_role_outside_pair three a b
  let v : Fin 3 → Fin 3 → Role := fun e i =>
    if i = 0 then (if e = 2 then b else a)
    else if i = 1 then (if e = 1 then b else a)
    else if e = 2 then c else a
  let out : Fin 3 → Role := fun i => if i = 0 then a else if i = 1 then b else c
  have hv : ∀ x, v 0 x = v 1 x ∨ v 0 x = v 2 x ∨ v 1 x = v 2 x := by
    intro x
    by_cases hx : x = 1
    · exact Or.inr (Or.inl (by simp [v, hx]))
    · exact Or.inl (by simp [v, hx])
  have he : ∀ e, t.eval (fun x => WinnerSet.singleton (v e x)) = WinnerSet.singleton (out e) := by
    intro e
    have hc : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases hc with rfl | rfl | rfl
    · simpa [v, out] using ha a a
    · simpa [v, out] using ha b a
    · simpa [v, out] using hb a c
  rcases t.atomic_preserves_repeat_triple v hv out he with h | h | h
  · exact hab (by simpa [out] using h)
  · exact hca (by simpa [out] using h.symm)
  · exact hcb (by simpa [out] using h.symm)

end Term
end KFOL
