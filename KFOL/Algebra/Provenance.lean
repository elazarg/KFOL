module

public import KFOL.Algebra.PairTests
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Image

/-! # Finite permutation provenance on each fixed status cell -/

@[expose] public section

namespace KFOL.Term

universe u v

/-- Fix every singleton/ambiguity status. Evaluation on the whole cell is
then a fixed finite constant set plus finitely many permuted ambiguous inputs.
No finiteness assumption on the role or variable type is needed. -/
theorem exists_cell_provenance {Role : Type u} {Var : Type v} (t : Term Role Var)
    (base : Var → WinnerSet Role) :
    ∃ (C : Set Role) (P : Var → Finset (Equiv.Perm Role)), C.Finite ∧
      (∀ j, ∀ p ∈ P j, (base j).Ambiguous) ∧
      ∀ valuation : Var → WinnerSet Role,
        (∀ j r, base j = WinnerSet.singleton r ↔ valuation j = WinnerSet.singleton r) →
        (t.eval valuation).val = C ∪ ⋃ j, ⋃ p ∈ P j, p '' (valuation j).val := by
  classical
  induction t with
  | winner r =>
    refine ⟨{r}, fun _ => ∅, Set.finite_singleton r, ?_, ?_⟩
    · simp
    · intro valuation _
      simp [eval, WinnerSet.singleton]
  | var x =>
    by_cases hx : (base x).Ambiguous
    · let P : Var → Finset (Equiv.Perm Role) := fun j => if j = x then {1} else ∅
      refine ⟨∅, P, Set.finite_empty, ?_, ?_⟩
      · intro j p hp
        have hj : j = x := by
          by_contra hj
          simp [P, hj] at hp
        subst j
        exact hx
      · intro valuation _
        ext r
        simp only [eval, Set.mem_union, Set.mem_empty_iff_false, false_or,
          Set.mem_iUnion, Set.mem_image]
        constructor
        · intro h
          exact ⟨x, 1, by simp [P], r, h, rfl⟩
        · rintro ⟨j, p, hp, a, ha, he⟩
          have hj : j = x := by
            by_contra hj
            simp [P, hj] at hp
          subst j
          have hp' : p = 1 := by simpa only [P, ite_eq_left rfl, Finset.mem_singleton] using hp
          subst p
          have he' : a = r := he
          exact he' ▸ ha
    · simp only [WinnerSet.Ambiguous, not_forall, not_not] at hx
      obtain ⟨r, hr⟩ := hx
      refine ⟨{r}, fun _ => ∅, Set.finite_singleton r, ?_, ?_⟩
      · simp
      · intro valuation hstatus
        have hv := (hstatus x r).mp hr
        simp [eval, hv, WinnerSet.singleton]
  | choice r s t hs ht =>
    by_cases hc : s.eval base = WinnerSet.singleton r ∨ t.eval base = WinnerSet.singleton r
    · refine ⟨{r}, fun _ => ∅, Set.finite_singleton r, ?_, ?_⟩
      · simp
      · intro valuation hstatus
        have htransfer := or_congr ((s.eval_sameStatus base valuation hstatus) r)
          ((t.eval_sameStatus base valuation hstatus) r)
        change (WinnerSet.choice r (s.eval valuation) (t.eval valuation)).val = _
        rw [WinnerSet.choice, ite_eq_left (htransfer.mp hc)]
        simp [WinnerSet.singleton]
    · obtain ⟨Cs, Ps, hCs, hPs, es⟩ := hs
      obtain ⟨Ct, Pt, hCt, hPt, et⟩ := ht
      refine ⟨Cs ∪ Ct, fun j => Ps j ∪ Pt j, hCs.union hCt, ?_, ?_⟩
      · intro j p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · exact hPs j p hp
        · exact hPt j p hp
      · intro valuation hstatus
        have htransfer := or_congr ((s.eval_sameStatus base valuation hstatus) r)
          ((t.eval_sameStatus base valuation hstatus) r)
        have hc' : ¬(s.eval valuation = WinnerSet.singleton r ∨ t.eval valuation = WinnerSet.singleton r) :=
          fun h => hc (htransfer.mpr h)
        simp only [eval, WinnerSet.choice, ite_eq_right hc', WinnerSet.val_union, es valuation hstatus,
          et valuation hstatus]
        ext i
        simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_union]
        constructor
        · rintro ((h | ⟨j, p, hp, hm⟩) | (h | ⟨j, p, hp, hm⟩))
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨j, p, Or.inl hp, hm⟩
          · exact Or.inl (Or.inr h)
          · exact Or.inr ⟨j, p, Or.inr hp, hm⟩
        · rintro ((h | h) | ⟨j, p, hp | hp, hm⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Or.inr ⟨j, p, hp, hm⟩)
          · exact Or.inr (Or.inr ⟨j, p, hp, hm⟩)
  | rename p t ht =>
    obtain ⟨C, P, hC, hP, he⟩ := ht
    refine ⟨p '' C, fun j => (P j).image (fun q => p * q), hC.image p, ?_, ?_⟩
    · intro j q hq
      obtain ⟨q', hq', _⟩ := Finset.mem_image.mp hq
      exact hP j q' hq'
    · intro valuation hstatus
      change p '' (t.eval valuation).val = _
      rw [he valuation hstatus]
      ext i
      simp only [Set.mem_image, Set.mem_union, Set.mem_iUnion, Finset.mem_image]
      constructor
      · rintro ⟨a, h | ⟨j, q, hq, b, hb, rfl⟩, rfl⟩
        · exact Or.inl ⟨a, h, rfl⟩
        · exact Or.inr ⟨j, p * q, ⟨q, hq, rfl⟩, b, hb, rfl⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨j, q, ⟨q', hq', rfl⟩, b, hb, rfl⟩)
        · exact ⟨a, Or.inl ha, rfl⟩
        · exact ⟨q' b, Or.inr ⟨j, q', hq', b, hb, rfl⟩, rfl⟩

end KFOL.Term
