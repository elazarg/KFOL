module

public import KFOL.Congruences.SymmetricClassification
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat

/-! # Exhaustive representatives and exact symmetric quotient cardinalities -/

@[expose] public section

namespace KFOL.WinnerSet

universe u

variable {Role : Type u} [Nonempty Role]

/-- Small nonempty winner values; the full value is excluded whenever m<K. -/
abbrev Small (m : ℕ) := {A : WinnerSet Role // A.val.ncard ≤ m}

noncomputable def thresholdTag (m : ℕ) (A : WinnerSet Role) : Option (Small (Role := Role) m) := by
  classical
  exact if h : A.val.ncard ≤ m then some ⟨A,h⟩ else none

def thresholdDecode (m : ℕ) : Option (Small (Role := Role) m) → WinnerSet Role
  | none => full
  | some A => A.val

@[simp] theorem thresholdDecode_tag (m : ℕ) (A : WinnerSet Role) :
    thresholdDecode m (thresholdTag m A) = threshold m A := by
  classical
  unfold thresholdTag threshold
  split <;> rfl

theorem thresholdDecode_injective {m : ℕ} (hm : m < Nat.card Role) :
    Function.Injective (thresholdDecode (Role := Role) m) := by
  intro a b he
  cases a with
  | none => cases b with
    | none => rfl
    | some B =>
      have hb := B.property
      change full = B.val at he
      rw [← he] at hb
      simp only [full_val,Set.ncard_univ] at hb
      omega
  | some A => cases b with
    | none =>
      have ha := A.property
      change A.val = full at he
      rw [he] at ha
      simp only [full_val,Set.ncard_univ] at ha
      omega
    | some B => exact congrArg some (Subtype.ext he)

theorem thresholdTag_surjective {m : ℕ} (hm : m < Nat.card Role) :
    Function.Surjective (thresholdTag (Role := Role) m) := by
  classical
  intro tag
  cases tag with
  | none =>
    refine ⟨full,?_⟩
    simp [thresholdTag,full_val,Set.ncard_univ,Nat.not_le_of_gt hm]
  | some A =>
    refine ⟨A.val,?_⟩
    simp only [thresholdTag,dite_eq_left A.property]

theorem thresholdTag_eq_iff {m : ℕ} (hm : m < Nat.card Role) (A B : WinnerSet Role) :
    thresholdTag m A = thresholdTag m B ↔ threshold m A = threshold m B := by
  constructor
  · intro he
    have hh := congrArg (thresholdDecode m) he
    simpa only [thresholdDecode_tag] using hh
  · intro he
    apply thresholdDecode_injective hm
    simpa only [thresholdDecode_tag] using he

/-- Exhaustive concrete representatives of every threshold quotient. -/
noncomputable def thresholdQuotientEquiv {m : ℕ} (hm : m < Nat.card Role) :
    Quotient (Setoid.ker (threshold (Role := Role) m)) ≃ Option (Small (Role := Role) m) :=
  (Quotient.congrRight (fun A B => (thresholdTag_eq_iff hm A B).symm)).trans
    (Setoid.quotientKerEquivOfSurjective (thresholdTag m) (thresholdTag_surjective hm))

section Count

variable [Fintype Role]

/-- The complete finite family of possible small representatives, partitioned
by cardinality; every size from one through m is included. -/
noncomputable def smallFinsets (m : ℕ) : Finset (Finset Role) := by
  classical
  exact (Finset.Icc 1 m).biUnion (fun j => (Finset.univ : Finset Role).powersetCard j)

omit [Nonempty Role] in
@[simp] theorem mem_smallFinsets (m : ℕ) (S : Finset Role) :
    S ∈ smallFinsets m ↔ S.Nonempty ∧ S.card ≤ m := by
  classical
  simp only [smallFinsets,Finset.mem_biUnion,Finset.mem_Icc,Finset.mem_powersetCard]
  constructor
  · rintro ⟨j,⟨hj1,hjm⟩,_,hcard⟩
    exact ⟨Finset.card_pos.mp (by omega),by omega⟩
  · rintro ⟨hne,hm⟩
    exact ⟨S.card,⟨Finset.card_pos.mpr hne,hm⟩,Finset.subset_univ S,rfl⟩

noncomputable def smallEquivFinsets (m : ℕ) : Small (Role := Role) m ≃ smallFinsets (Role := Role) m where
  toFun A := by
    classical
    exact ⟨A.val.val.toFinset,by
    rw [mem_smallFinsets]
    constructor
    · obtain ⟨owner,hm⟩ := A.val.property
      exact ⟨owner,by simpa using hm⟩
    · simpa only [Set.ncard_eq_toFinset_card'] using A.property⟩
  invFun S := by
    classical
    exact ⟨⟨(S.val : Set Role),by
    obtain ⟨owner,hm⟩ := ((mem_smallFinsets m S.val).mp S.property).1
    exact ⟨owner,hm⟩⟩,by
      have hcard := ((mem_smallFinsets m S.val).mp S.property).2
      simpa using hcard⟩
  left_inv A := by
    classical
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv S := by
    classical
    apply Subtype.ext
    simp

omit [Nonempty Role] in
theorem card_smallFinsets (m : ℕ) :
    (smallFinsets (Role := Role) m).card = ∑ j ∈ Finset.Icc 1 m, (Fintype.card Role).choose j := by
  classical
  have hd : (↑(Finset.Icc 1 m) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.univ : Finset Role).powersetCard j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    have hi := (Finset.mem_powersetCard.mp hSi).2
    have hj := (Finset.mem_powersetCard.mp hSj).2
    exact hij (hi.symm.trans hj)
  rw [smallFinsets,Finset.card_biUnion hd]
  simp only [Finset.card_powersetCard,Finset.card_univ]

/-- The quotient count is proved from exhaustive representatives and the
standard binomial powerset-cardinality theorem. -/
theorem card_thresholdQuotient_fintype {m : ℕ} (hm : m < Nat.card Role) :
    Nat.card (Quotient (Setoid.ker (threshold (Role := Role) m))) =
      1 + ∑ j ∈ Finset.Icc 1 m, (Nat.card Role).choose j := by
  classical
  rw [Nat.card_congr (thresholdQuotientEquiv hm),Nat.card_eq_fintype_card,Fintype.card_option,
    Fintype.card_congr (smallEquivFinsets (Role := Role) m),Fintype.card_coe,card_smallFinsets]
  rw [Nat.card_eq_fintype_card]
  omega

end Count

/-- Finite-role formulation, independent of a chosen Fintype enumeration. -/
theorem card_thresholdQuotient [Finite Role] {m : ℕ} (hm : m < Nat.card Role) :
    Nat.card (Quotient (Setoid.ker (threshold (Role := Role) m))) =
      1 + ∑ j ∈ Finset.Icc 1 m, (Nat.card Role).choose j := by
  let _ : Fintype Role := Fintype.ofFinite Role
  exact card_thresholdQuotient_fintype hm

end KFOL.WinnerSet
