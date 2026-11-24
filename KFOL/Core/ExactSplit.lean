module

public import KFOL.Core.ProfileBudgets.Pruning
public import Mathlib.Data.Finset.Card

/-! # Exact row interpolation by a game of bounded depth

A nonempty row goal prescribes the complete winner set. An empty row is
unconstrained. Guess an owner and two child goals whose choices meet the
parent, then let the opponent choose a child. The number of required
row–winner pairs bounds the number of rounds. -/

@[expose] public section
namespace KFOL.Core.ExactSplit

open WinnerSet ProfileBudgets
attribute [local instance] Equational.coreStructure

variable {Role Row Var : Type*}

abbrev Goal (Row Role : Type*) := Finset (Row × Role)

def fiber (G : Goal Row Role) (q : Row) : Set Role := {k | (q,k) ∈ G}

def Match (G : Goal Row Role) (q : Row) (X : WinnerSet Role) : Prop :=
  (fiber G q).Nonempty → X.val = fiber G q

def Projection (v : Row → Var → WinnerSet Role) (G : Goal Row Role) : Prop :=
  ∃ j, ∀ q, Match G q (v q j)

def Compatible (r : Role) (G L R : Goal Row Role) : Prop :=
  ∀ q X Y, Match L q X → Match R q Y → Match G q (choice r X Y)

def Plays (v : Row → Var → WinnerSet Role) : ℕ → Goal Row Role → Prop
  | 0, G => Projection v G
  | d+1, G => Projection v G ∨ ∃ r L R,
      Compatible r G L R ∧ Plays v d L ∧ Plays v d R

private theorem plays_step (v : Row → Var → WinnerSet Role) (d : ℕ) (G : Goal Row Role) :
    Plays v d G → Plays v (d+1) G := by
  induction d generalizing G with
  | zero => exact Or.inl
  | succ d ih =>
    rintro (leaf|⟨r,L,R,h,left,right⟩)
    · exact Or.inl leaf
    · exact Or.inr ⟨r,L,R,h,ih L left,ih R right⟩

theorem plays_mono (v : Row → Var → WinnerSet Role) {m d : ℕ} (le : m ≤ d) (G : Goal Row Role) :
    Plays v m G → Plays v d G := by
  induction le with
  | refl => exact id
  | step le ih => exact fun h => plays_step v _ G (ih h)

theorem plays_succ_iff [Nonempty Role] (v : Row → Var → WinnerSet Role) (d : ℕ) (G : Goal Row Role) :
    Plays v (d+1) G ↔ ∃ r L R, Compatible r G L R ∧ Plays v d L ∧ Plays v d R := by
  classical
  constructor
  · rintro (proj|gate)
    · have core : Plays v d G := plays_mono v (Nat.zero_le d) G proj
      refine ⟨Classical.arbitrary Role,G,G,?_,core,core⟩
      intro q X Y hx hy active
      have eq : X = Y := Subtype.ext ((hx active).trans (hy active).symm)
      rw [eq,WinnerSet.choice_idempotent]
      exact hy active
    · exact gate
  · exact Or.inr

/-- Height counts binary gates on a root-to-leaf path. -/
inductive HeightLE : ℕ → CoreTerm Role Var → Prop where
  | leaf (d : ℕ) (j : Var) : HeightLE d (.var j)
  | gate {d : ℕ} (r : Role) {l u : CoreTerm Role Var} :
      HeightLE d l → HeightLE d u → HeightLE (d+1) (choiceTerm r l u)

theorem short_word_of_plays (v : Row → Var → WinnerSet Role) (d : ℕ) (G : Goal Row Role) :
    Plays v d G → ∃ t : CoreTerm Role Var, HeightLE d t ∧ ∀ q, Match G q (t.realize (v q)) := by
  induction d generalizing G with
  | zero => rintro ⟨j,h⟩; exact ⟨.var j,.leaf _ j,h⟩
  | succ d ih =>
    rintro (⟨j,h⟩|⟨r,L,R,h,left,right⟩)
    · exact ⟨.var j,.leaf _ j,h⟩
    · obtain ⟨l,dl,hl⟩ := ih L left
      obtain ⟨u,du,hu⟩ := ih R right
      exact ⟨choiceTerm r l u,.gate r dl du,fun q => h q _ _ (hl q) (hu q)⟩

theorem word_of_plays (v : Row → Var → WinnerSet Role) (d : ℕ) (G : Goal Row Role) :
    Plays v d G → ∃ t : CoreTerm Role Var, ∀ q, Match G q (t.realize (v q)) :=
  fun h => let ⟨t,_,ht⟩ := short_word_of_plays v d G h; ⟨t,ht⟩

private noncomputable def child (G : Goal Row Role) (keep : Row → Prop)
    (v : Row → WinnerSet Role) : Goal Row Role := by
  classical
  exact G.filter fun i => keep i.1 ∧ i.2 ∈ (v i.1).val

private theorem child_subset (G : Goal Row Role) (keep : Row → Prop) (v : Row → WinnerSet Role) :
    child G keep v ⊆ G := by classical exact Finset.filter_subset _ _

private theorem fiber_child (G : Goal Row Role) (keep : Row → Prop) (v : Row → WinnerSet Role)
    (q : Row) (yes : keep q)
    (small : (v q).val ⊆ fiber G q) :
    fiber (child G keep v) q = (v q).val := by
  classical
  ext k
  change (q,k) ∈ G.filter _ ↔ k ∈ (v q).val
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2.2,fun h => ⟨small h,yes,h⟩⟩

private theorem child_match (G : Goal Row Role) (keep : Row → Prop) (v : Row → WinnerSet Role)
    (small : ∀ q, (fiber G q).Nonempty → keep q → (v q).val ⊆ fiber G q) (q : Row) :
    Match (child G keep v) q (v q) := by
  classical
  rintro ⟨k,hk⟩
  obtain ⟨old,yes,win⟩ := Finset.mem_filter.mp hk
  have active : (fiber G q).Nonempty := ⟨k,old⟩
  exact (fiber_child G keep v q yes (small q active yes)).symm

private theorem retained (G : Goal Row Role) (keep : Row → Prop) (v : Row → WinnerSet Role)
    (small : ∀ q, (fiber G q).Nonempty → keep q → (v q).val ⊆ fiber G q)
    (q : Row) (active : (fiber G q).Nonempty) (need : keep q) (X : WinnerSet Role)
    (fits : Match (child G keep v) q X) : X = v q := by
  have eq := fiber_child G keep v q need (small q active need)
  have nonempty : (fiber (child G keep v) q).Nonempty := eq ▸ (v q).property
  exact Subtype.ext ((fits nonempty).trans eq)

/-- A witness can be compressed until every retained binary gate decreases
the number of constrained pairs on both branches. -/
theorem plays_of_word (v : Row → Var → WinnerSet Role) (t : CoreTerm Role Var) :
    ∀ G : Goal Row Role, (∀ q, Match G q (t.realize (v q))) → Plays v G.card G := by
  classical
  induction t using Core.induction_choice with
  | var j =>
    intro G fit
    exact plays_mono v (Nat.zero_le G.card) G (show Projection v G from ⟨j,fit⟩)
  | choice r l u ihl ihu =>
    intro G fit
    let X := fun q => l.realize (v q)
    let Y := fun q => u.realize (v q)
    let needX := fun q => X q = WinnerSet.singleton r ∨ Y q ≠ WinnerSet.singleton r
    let needY := fun q => X q ≠ WinnerSet.singleton r
    have target (q) (active : (fiber G q).Nonempty) : (choice r (X q) (Y q)).val = fiber G q := fit q active
    have sx (q) (active : (fiber G q).Nonempty) (keep : needX q) : (X q).val ⊆ fiber G q := by
      rw [← target q active]
      by_cases left : X q = WinnerSet.singleton r
      · simp [choice,left]
      · have right := keep.resolve_left left
        simp [choice,left,right]
    have sy (q) (active : (fiber G q).Nonempty) (left : needY q) : (Y q).val ⊆ fiber G q := by
      rw [← target q active]
      by_cases right : Y q = WinnerSet.singleton r
      · simp [choice,right]
      · have diff : X q ≠ WinnerSet.singleton r := left
        simp [choice,diff,right]
    let L := child G needX X
    let R := child G needY Y
    have hl : Plays v L.card L := ihl L (child_match _ _ _ sx)
    have hr : Plays v R.card R := ihu R (child_match _ _ _ sy)
    by_cases leq : L = G
    · simpa only [leq] using hl
    by_cases req : R = G
    · simpa only [req] using hr
    have lsub : L ⊆ G := child_subset G needX X
    have rsub : R ⊆ G := child_subset G needY Y
    have ltL := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨lsub,leq⟩)
    have ltR := Finset.card_lt_card ((Finset.ssubset_iff_subset_ne).mpr ⟨rsub,req⟩)
    have comp : Compatible r G L R := by
      intro q X' Y' left right active
      rw [← target q active]
      by_cases x : X q = WinnerSet.singleton r
      · have eq := retained G needX X sx q active (Or.inl x) X' left
        simp [choice,eq,x]
      · have eqY := retained G needY Y sy q active x Y' right
        by_cases y : Y q = WinnerSet.singleton r
        · simp [choice,eqY,y]
        · have eqX := retained G needX X sx q active (Or.inr y) X' left
          rw [eqX,eqY]
    obtain ⟨d,hd⟩ := Nat.exists_eq_succ_of_ne_zero (show G.card ≠ 0 by omega)
    rw [hd]
    exact Or.inr ⟨r,L,R,comp,plays_mono v (by omega) L hl,plays_mono v (by omega) R hr⟩

/-- For an exact table G.card is the sum of the target output cardinalities. -/
theorem short_word (v : Row → Var → WinnerSet Role) (G : Goal Row Role) (t : CoreTerm Role Var)
    (yes : ∀ q, Match G q (t.realize (v q))) :
    ∃ u : CoreTerm Role Var, HeightLE G.card u ∧ ∀ q, Match G q (u.realize (v q)) :=
  short_word_of_plays v G.card G (plays_of_word v t G yes)

theorem plays_iff_word (v : Row → Var → WinnerSet Role) (d : ℕ) (G : Goal Row Role) (bound : G.card ≤ d) :
    Plays v d G ↔ ∃ t : CoreTerm Role Var, ∀ q, Match G q (t.realize (v q)) :=
  ⟨word_of_plays v d G,fun ⟨t,fit⟩ => plays_mono v bound G (plays_of_word v t G fit)⟩

end KFOL.Core.ExactSplit
