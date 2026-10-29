/-
Conservative models of reset and the congruence obstruction in comb models.
Only Std is used. Membership of all forest models in the reset variety is
proved mathematically in reset.tex; it is not assumed as a Lean axiom here.
-/
import Reset

set_option autoImplicit false
namespace MinimalChoice.ResetCalculus.Models

theorem reset_absorb {α : Type} (A B : S α) :
    reset (reset A B) A = reset B A := by
  classical
  funext w
  apply propext
  by_cases ha : Multiple A <;> by_cases hb : Multiple B <;>
    simp [reset, ha, hb, join, or_comm]

theorem reset_leftComm {α : Type} (A B C : S α) :
    reset A (reset B C) = reset B (reset A C) := by
  classical
  by_cases hc : Multiple C
  · have h1 : Multiple (reset B C) := (reset_multiple B C).mpr hc
    have h2 : Multiple (reset A C) := (reset_multiple A C).mpr hc
    have e1 : reset A (reset B C) = join A (reset B C) := by
      rw [reset, ite_eq_left h1]
    have e2 : reset B (reset A C) = join B (reset A C) := by
      rw [reset, ite_eq_left h2]
    rw [e1, e2]
    funext w
    apply propext
    simp only [reset, ite_eq_left hc, join]
    exact or_left_comm
  · have h1 : reset B C = C := by simp [reset, hc]
    have h2 : reset A C = C := by simp [reset, hc]
    simp only [h1, h2]

structure ConservativeLaws (α : Type) where
  op : α → α → α
  conservative : ∀ x y, op x y = x ∨ op x y = y
  absorb : ∀ x y, op (op x y) x = op y x
  leftComm : ∀ x y z, op x (op y z) = op y (op x z)

namespace ConservativeLaws
variable {α : Type} (A : ConservativeLaws α)

def below (x y : α) : Prop := A.op x y = y ∧ A.op y x = y

theorem idem (x : α) : A.op x x = x := (A.conservative x x).elim id id

theorem left_selected (x y : α) (h : A.op x y = x) : A.op y x = x := by
  rw [← A.absorb x y, h, A.idem]

theorem below_refl (x : α) : A.below x x := ⟨A.idem x, A.idem x⟩

theorem below_antisymm (x y : α) (h : A.below x y) (k : A.below y x) : x = y :=
  k.1.symm.trans h.2

theorem below_trans (x y z : α) (h : A.below x y) (k : A.below y z) :
    A.below x z := by
  have hc := A.leftComm z y x
  rw [h.2, k.2] at hc
  rcases A.conservative z x with hz | hx
  · exact ⟨A.left_selected z x hz, hz⟩
  · rw [hx, h.2] at hc
    have hyz : y = z := hc.symm
    subst z
    exact h

theorem upper_chain (x y z : α) (h : A.below x y) (k : A.below x z) :
    A.below y z ∨ A.below z y := by
  have hc := A.leftComm y z x
  rw [k.2, h.2] at hc
  rcases A.conservative y z with hy | hz
  · exact Or.inr ⟨hc.symm.trans hy, hy⟩
  · exact Or.inl ⟨hz, hc.symm.trans hz⟩

theorem op_formula (x y : α) :
    A.op x y = @ite α (A.below y x) (Classical.propDecidable _) x y := by
  classical
  split
  · rename_i h
    exact h.2
  · rename_i h
    rcases A.conservative x y with hx | hy
    · exact False.elim (h ⟨A.left_selected x y hx, hx⟩)
    · exact hy
end ConservativeLaws

/-- The ancestor order of a rooted forest; no finiteness assumption. -/
structure ForestOrder (α : Type) where
  below : α → α → Prop
  refl : ∀ x, below x x
  trans : ∀ x y z, below x y → below y z → below x z
  antisymm : ∀ x y, below x y → below y x → x = y
  upper_chain : ∀ x y z, below x y → below x z → below y z ∨ below z y

def ConservativeLaws.forest {α : Type} (A : ConservativeLaws α) : ForestOrder α :=
  ⟨A.below, A.below_refl, A.below_trans, A.below_antisymm, A.upper_chain⟩

noncomputable def ForestOrder.op {α : Type} (P : ForestOrder α) (x y : α) : α := by
  classical
  exact if P.below y x then x else y

namespace ForestOrder
variable {α : Type} (P : ForestOrder α)

theorem conservative (x y : α) : P.op x y = x ∨ P.op x y = y := by
  classical
  by_cases h : P.below y x <;> simp [op, h]

theorem absorb (x y : α) : P.op (P.op x y) x = P.op y x := by
  classical
  by_cases h : P.below y x
  · have hh : P.op x y = x := by simp [op, h]
    rw [hh]
    by_cases k : P.below x y
    · have he := P.antisymm x y k h
      subst y
      simp [op, P.refl]
    · simp [op, k, P.refl]
  · have hh : P.op x y = y := by simp [op, h]
    rw [hh]

theorem leftComm (x y z : α) : P.op x (P.op y z) = P.op y (P.op x z) := by
  classical
  by_cases hx : P.below z x <;> by_cases hy : P.below z y
  · have h1 : P.op y z = y := by simp [op, hy]
    have h2 : P.op x z = x := by simp [op, hx]
    rw [h1, h2]
    rcases P.upper_chain z x y hx hy with h | h
    · by_cases k : P.below y x
      · have he := P.antisymm x y h k
        subst y
        rfl
      · simp [op, h, k]
    · by_cases k : P.below x y
      · have he := P.antisymm x y k h
        subst y
        rfl
      · simp [op, h, k]
  · have hxy : ¬ P.below x y := fun h => hy (P.trans z x y hx h)
    simp [op, hx, hy, hxy]
  · have hyx : ¬ P.below y x := fun h => hx (P.trans z y x hy h)
    simp [op, hx, hy, hyx]
  · simp [op, hx, hy]

noncomputable def laws : ConservativeLaws α :=
  ⟨P.op, P.conservative, P.absorb, P.leftComm⟩

theorem recover (x y : α) : P.laws.below x y ↔ P.below x y := by
  classical
  constructor
  · rintro ⟨h, k⟩
    change P.op x y = y at h
    by_cases he : P.below y x
    · rw [op, ite_eq_left he] at h
      subst y
      exact P.refl x
    · by_cases hx : P.below x y
      · exact hx
      · have h' : P.op y x = y := k
        simp [op, hx] at h'
        subst y
        exact P.refl x
  · intro h
    constructor
    · change P.op x y = y
      by_cases k : P.below y x
      · have he := P.antisymm x y h k
        subst y
        simp [op, P.refl]
      · simp [op, k]
    · change P.op y x = y
      simp [op, h]
end ForestOrder

structure Chain (α : Type) where
  below : α → α → Prop
  refl : ∀ x, below x x
  trans : ∀ x y z, below x y → below y z → below x z
  antisymm : ∀ x y, below x y → below y x → x = y
  total : ∀ x y, below x y ∨ below y x
  bottom : α
  bottom_le : ∀ x, below bottom x

inductive Comb (α : Type) where
  | base : Comb α
  | side : α → Comb α
  | spine : α → Comb α
deriving DecidableEq

noncomputable def combOp {α : Type} (L : Chain α) : Comb α → Comb α → Comb α := by
  classical
  exact fun x y => match x, y with
    | .base, y => y
    | .side _, y => y
    | .spine i, .base => .spine i
    | .spine i, .side j => if L.below j i then .spine i else .side j
    | .spine i, .spine j => if L.below j i then .spine i else .spine j

structure Congruence {α : Type} (op : α → α → α) where
  rel : α → α → Prop
  refl : ∀ x, rel x x
  symm : ∀ {x y}, rel x y → rel y x
  trans : ∀ {x y z}, rel x y → rel y z → rel x z
  compatible : ∀ {x y z w}, rel x y → rel z w → rel (op x z) (op y w)

namespace Congruence
variable {α : Type} {op : α → α → α} (R : Congruence op)
theorem left {x y : α} (h : R.rel x y) (z : α) : R.rel (op z x) (op z y) :=
  R.compatible (R.refl z) h
theorem right {x y : α} (h : R.rel x y) (z : α) : R.rel (op x z) (op y z) :=
  R.compatible h (R.refl z)
end Congruence

def collapse {α : Type} (L : Chain α) : Comb α → Comb α
  | .base => .side L.bottom
  | .side i => .side i
  | .spine i => .spine i

theorem collapse_hom {α : Type} (L : Chain α) (x y : Comb α) :
    collapse L (combOp L x y) = combOp L (collapse L x) (collapse L y) := by
  classical
  cases x <;> cases y <;> simp [collapse, combOp, L.bottom_le]
  all_goals rename_i i j
  all_goals by_cases h : L.below j i <;> simp [h]

noncomputable def monolith {α : Type} (L : Chain α) : Congruence (combOp L) where
  rel x y := collapse L x = collapse L y
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans
  compatible := by
    intro x y z w h k
    rw [collapse_hom, collapse_hom, h, k]

theorem comb_spine_leaf {α : Type} (L : Chain α) (R : Congruence (combOp L))
    (i : α) (v : Comb α) (hv : ∀ j, v ≠ .spine j)
    (h : R.rel (.spine i) v) : R.rel .base (.side L.bottom) := by
  have ha := R.right h .base
  have hb := R.right h (.side L.bottom)
  cases v with
  | base =>
    simp only [combOp, ite_eq_left (L.bottom_le i)] at ha hb
    exact R.trans (R.symm ha) hb
  | side j =>
    simp only [combOp, ite_eq_left (L.bottom_le i)] at ha hb
    exact R.trans (R.symm ha) hb
  | spine j => exact False.elim (hv j rfl)

/-- Every nontrivial congruence contains the same pair, at every cardinality. -/
theorem comb_common_pair {α : Type} (L : Chain α) (R : Congruence (combOp L))
    (x y : Comb α) (hne : x ≠ y) (h : R.rel x y) :
    R.rel .base (.side L.bottom) := by
  classical
  have leaf : ∀ i v, (∀ j, v ≠ Comb.spine j) → R.rel (.spine i) v →
      R.rel .base (.side L.bottom) := comb_spine_leaf L R
  have side_base : ∀ j, R.rel Comb.base (.side j) → R.rel .base (.side L.bottom) := by
    intro j hj
    by_cases he : j = L.bottom
    · simpa only [he] using hj
    · have hn : ¬ L.below j L.bottom := by
        intro hh
        exact he (L.antisymm j L.bottom hh (L.bottom_le j))
      have hh := R.left hj (.spine L.bottom)
      simp only [combOp, ite_eq_right hn] at hh
      exact leaf L.bottom (.side j) (by intro k he; cases he) hh
  cases x with
  | base =>
    cases y with
    | base => exact False.elim (hne rfl)
    | side j => exact side_base j h
    | spine j => exact leaf j .base (by intro k he; cases he) (R.symm h)
  | side i =>
    cases y with
    | base => exact side_base i (R.symm h)
    | spine j => exact leaf j (.side i) (by intro k he; cases he) (R.symm h)
    | side j =>
      have hij : i ≠ j := fun he => hne (congrArg Comb.side he)
      rcases L.total i j with hc | hc
      · have hj : ¬ L.below j i := fun hh => hij (L.antisymm i j hc hh)
        have hh := R.left h (.spine i)
        simp only [combOp, ite_eq_left (L.refl i), ite_eq_right hj] at hh
        exact leaf i (.side j) (by intro k he; cases he) hh
      · have hi : ¬ L.below i j := fun hh => hij (L.antisymm i j hh hc)
        have hh := R.left (R.symm h) (.spine j)
        simp only [combOp, ite_eq_left (L.refl j), ite_eq_right hi] at hh
        exact leaf j (.side i) (by intro k he; cases he) hh
  | spine i =>
    cases y with
    | base => exact leaf i .base (by intro k he; cases he) h
    | side j => exact leaf i (.side j) (by intro k he; cases he) h
    | spine j =>
      have hij : i ≠ j := fun he => hne (congrArg Comb.spine he)
      rcases L.total i j with hc | hc
      · have hj : ¬ L.below j i := fun hh => hij (L.antisymm i j hc hh)
        have hh := R.right h (.side j)
        simp only [combOp, ite_eq_right hj, ite_eq_left (L.refl j)] at hh
        exact leaf j (.side j) (by intro k he; cases he) (R.symm hh)
      · have hi : ¬ L.below i j := fun hh => hij (L.antisymm i j hh hc)
        have hh := R.right (R.symm h) (.side i)
        simp only [combOp, ite_eq_right hi, ite_eq_left (L.refl i)] at hh
        exact leaf i (.side i) (by intro k he; cases he) (R.symm hh)

theorem monolith_minimal {α : Type} (L : Chain α) (R : Congruence (combOp L))
    (x y : Comb α) (hne : x ≠ y) (h : R.rel x y) :
    ∀ u v, (monolith L).rel u v → R.rel u v := by
  have hc := comb_common_pair L R x y hne h
  intro u v hv
  change collapse L u = collapse L v at hv
  cases u with
  | base =>
    cases v with
    | base => exact R.refl _
    | side j =>
      have he : L.bottom = j := Comb.side.inj hv
      simpa only [← he] using hc
    | spine j => cases hv
  | side i =>
    cases v with
    | base =>
      have he : i = L.bottom := Comb.side.inj hv
      simpa only [he] using R.symm hc
    | side j =>
      have he : i = j := Comb.side.inj hv
      subst j
      exact R.refl _
    | spine j => cases hv
  | spine i =>
    cases v with
    | base => cases hv
    | side j => cases hv
    | spine j =>
      have he : i = j := Comb.spine.inj hv
      subst j
      exact R.refl _

theorem monolith_nontrivial {α : Type} (L : Chain α) :
    (monolith L).rel .base (.side L.bottom) := rfl

theorem monolith_proper {α : Type} (L : Chain α) :
    ¬ (monolith L).rel .base (.spine L.bottom) := by
  intro h
  change Comb.side L.bottom = Comb.spine L.bottom at h
  cases h

def combBelow {α : Type} (L : Chain α) : Comb α → Comb α → Prop
  | .base, .base => True
  | .base, .spine _ => True
  | .side i, .side j => i = j
  | .side i, .spine j => L.below i j
  | .spine i, .spine j => L.below i j
  | _, _ => False

def combForest {α : Type} (L : Chain α) : ForestOrder (Comb α) where
  below := combBelow L
  refl := by intro x; cases x <;> simp [combBelow, L.refl]
  trans := by
    intro x y z h k
    cases x <;> cases y <;> cases z <;> simp_all [combBelow]
    all_goals exact L.trans _ _ _ h k
  antisymm := by
    intro x y h k
    cases x <;> cases y <;> simp_all [combBelow]
    exact L.antisymm _ _ h k
  upper_chain := by
    intro x y z h k
    cases x <;> cases y <;> cases z <;> simp_all [combBelow]
    all_goals exact L.total _ _

theorem combForest_op {α : Type} (L : Chain α) (x y : Comb α) :
    (combForest L).op x y = combOp L x y := by
  classical
  cases x <;> cases y <;> simp [ForestOrder.op, combForest, combBelow, combOp] <;> try rfl
  rename_i i j
  by_cases h : j = i <;> simp_all

end MinimalChoice.ResetCalculus.Models

#print axioms MinimalChoice.ResetCalculus.Models.ConservativeLaws.below_trans
#print axioms MinimalChoice.ResetCalculus.Models.reset_absorb
#print axioms MinimalChoice.ResetCalculus.Models.reset_leftComm
#print axioms MinimalChoice.ResetCalculus.Models.ConservativeLaws.upper_chain
#print axioms MinimalChoice.ResetCalculus.Models.ForestOrder.leftComm
#print axioms MinimalChoice.ResetCalculus.Models.comb_common_pair
#print axioms MinimalChoice.ResetCalculus.Models.monolith_minimal
#print axioms MinimalChoice.ResetCalculus.Models.combForest_op
