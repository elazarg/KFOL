module

public import KFOL.Core.CompulsoryPruning

/-! # Excluding auxiliary labels by two owners' support implications -/

@[expose] public section
namespace KFOL.Core.PruningExclusion

open ProfileBudgets CompulsoryPruning
variable {Role V : Type*} [DecidableEq Role] [DecidableEq V] {D : Set V}

/-- Each auxiliary label present in the support brings its specified partner. -/
def Closed (partner : D → D) (H : Finset V) : Prop :=
  ∀ d : D, d.val ∈ H → (partner d).val ∈ H

omit [DecidableEq V] in
private theorem no_singleton (partner : D → D) (moves : ∀ d, partner d ≠ d) (d : D) :
    ¬ Closed partner {d.val} := fun h =>
  moves d (Subtype.ext (Finset.mem_singleton.mp (h d (Finset.mem_singleton_self _))))

/-- If all s-prunings of this child are closed under a partner that moves d,
the other owner can prune the child while avoiding d. -/
private theorem avoids {r s : Role} (ne : r ≠ s) (t : CoreTerm Role V)
    (partner : D → D) (moves : ∀ d, partner d ≠ d)
    (safe : ∀ H ∈ Supports s t, Closed partner H) (d : D) :
    ∃ H ∈ Supports r t, d.val ∉ H := by
  classical
  by_contra! forced
  exact no_singleton partner moves d
    (safe _ (foreign_singleton r s ne.symm t d.val forced))

private theorem children {r s : Role} (ne : r ≠ s) (q : Role) (x y : CoreTerm Role V)
    (partner guard : D → D) (moves : ∀ d, guard d ≠ d)
    (own : ∀ H ∈ Supports r (choiceTerm q x y), Closed partner H)
    (other : ∀ H ∈ Supports s (choiceTerm q x y), Closed guard H) :
    (∀ H ∈ Supports r x, Closed partner H) ∧ (∀ H ∈ Supports r y, Closed partner H) := by
  by_cases qr : q = r
  · subst q
    have leftSafe H (h : H ∈ Supports s x) := other H ((foreign ne).mpr (Or.inl h))
    have rightSafe H (h : H ∈ Supports s y) := other H ((foreign ne).mpr (Or.inr h))
    constructor
    · intro H hH d hd
      obtain ⟨T, ht, miss⟩ := avoids ne y guard moves rightSafe (partner d)
      have hit := own _ (owned.mpr ⟨H, hH, T, ht, rfl⟩) d (Finset.mem_union_left _ hd)
      exact (Finset.mem_union.mp hit).resolve_right miss
    · intro H hH d hd
      obtain ⟨T, ht, miss⟩ := avoids ne x guard moves leftSafe (partner d)
      have hit := own _ (owned.mpr ⟨T, ht, H, hH, rfl⟩) d (Finset.mem_union_right _ hd)
      exact (Finset.mem_union.mp hit).resolve_left miss
  · exact ⟨fun _ h => own _ ((foreign qr).mpr (Or.inl h)),
      fun _ h => own _ ((foreign qr).mpr (Or.inr h))⟩

/-- Two different owners imposing fixed-point-free partner maps exclude
every auxiliary label from the actual syntax of the word. -/
theorem disjoint_vars {r s : Role} (ne : r ≠ s) (partner guard : D → D)
    (moves : ∀ d, partner d ≠ d) (moves' : ∀ d, guard d ≠ d) (t : CoreTerm Role V)
    (first : ∀ H ∈ Supports r t, Closed partner H) (second : ∀ H ∈ Supports s t, Closed guard H) :
    Disjoint (t.varFinset : Set V) D := by
  induction t using induction_choice with
  | var v =>
    apply Set.disjoint_left.mpr
    intro z hz hd
    have eq : z = v := Finset.mem_singleton.mp hz
    subst z
    exact no_singleton partner moves ⟨v, hd⟩ (first {v} rfl)
  | choice q x y hx hy =>
    obtain ⟨ax, ay⟩ := children ne q x y partner guard moves' first second
    obtain ⟨bx, by'⟩ := children ne.symm q x y guard partner moves second first
    have vars : (choiceTerm q x y).varFinset = x.varFinset ∪ y.varFinset := by
      simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2]
    rw [vars, Finset.coe_union, Set.disjoint_union_left]
    exact ⟨hx ax bx, hy ay by'⟩

/-- Auxiliary labels satisfying the two owners' requirements can be removed
from the available alphabet without affecting feasibility. -/
theorem feasibleOn_diff_iff {r s : Role} (ne : r ≠ s) (partner guard : D → D)
    (moves : ∀ d, partner d ≠ d) (moves' : ∀ d, guard d ≠ d)
    (F : Role → Finset V → Prop) (W : Set V)
    (first : ∀ H, F r H → Closed partner H) (second : ∀ H, F s H → Closed guard H) :
    FeasibleOn (W \ D) F ↔ FeasibleOn W F := by
  constructor
  · rintro ⟨t, sub, good⟩
    exact ⟨t, sub.trans Set.sdiff_subset, good⟩
  · rintro ⟨t, sub, good⟩
    have disj := disjoint_vars ne partner guard moves moves' t
      (fun H h => first H (good r H h)) (fun H h => second H (good s H h))
    exact ⟨t, fun _ h => ⟨sub h, Set.disjoint_left.mp disj h⟩, good⟩

end KFOL.Core.PruningExclusion
