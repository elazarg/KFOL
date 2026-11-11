module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Fin

/-! # Boolean separators after cutting a crown

A monotone Boolean function is allowed when it is constant on each
nonwrapping edge {i} ⊆ {i,i+1}. Prefixes, pairs and thresholds separate
every other strict interval in the Boolean lattice.
-/

@[expose] public section
namespace KFOL.Core.CrownBoolean

variable {n : ℕ}

abbrev lower (i : Fin (n+2)) : Finset (Fin (n+3)) := {i.castSucc}
abbrev upper (i : Fin (n+2)) : Finset (Fin (n+3)) := {i.castSucc,i.succ}

structure Good (f : Finset (Fin (n+3)) → Bool) : Prop where
  mono : ∀ S T, S ⊆ T → f S = true → f T = true
  bot : f ∅ = false
  top : f Finset.univ = true
  edge : ∀ i : Fin (n+2), f (lower i) = f (upper i)

private theorem next_ne (i : Fin (n+2)) : i.castSucc ≠ i.succ := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at he
  omega

private def prefixTest (r : Fin (n+3)) (S : Finset (Fin (n+3))) : Bool :=
  decide (∃ i ∈ S, i ≤ r)

private theorem prefixTest_good (r : Fin (n+3)) : Good (prefixTest r) where
  mono S T hST h := by
    obtain ⟨i,hi,hir⟩ : ∃ i ∈ S, i ≤ r := of_decide_eq_true h
    exact decide_eq_true ⟨i,hST hi,hir⟩
  bot := by simp [prefixTest]
  top := decide_eq_true ⟨r,Finset.mem_univ _,le_rfl⟩
  edge i := by
    apply Bool.eq_iff_iff.mpr
    simp only [prefixTest, decide_eq_true_eq]
    constructor
    · rintro ⟨j,hj,hr⟩
      exact ⟨j,Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hj)),hr⟩
    · rintro ⟨j,hj,hr⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact ⟨i.castSucc,Finset.mem_singleton_self _,hr⟩
      · have he : j = i.succ := Finset.mem_singleton.mp hj
        subst j
        exact ⟨i.castSucc,Finset.mem_singleton_self _,by
          apply Fin.le_iff_val_le_val.mpr
          have hh := Fin.le_iff_val_le_val.mp hr
          simp only [Fin.val_castSucc,Fin.val_succ] at hh ⊢
          omega⟩

def anyBit (S : Finset (Fin (n+3))) : Bool := decide S.Nonempty

theorem anyBit_good : Good (anyBit (n:=n)) where
  mono S T hST h := decide_eq_true ((of_decide_eq_true h).mono hST)
  bot := by simp [anyBit]
  top := decide_eq_true ⟨0,Finset.mem_univ _⟩
  edge i := by simp [anyBit,lower,upper]

private def pair (P S : Finset (Fin (n+3))) : Bool := decide (P ⊆ S)

private theorem pair_good (P : Finset (Fin (n+3))) (hP : P.card=2)
    (hbad : ∀ i : Fin (n+2), P ≠ upper i) : Good (pair P) where
  mono S T hST h := decide_eq_true ((of_decide_eq_true h).trans hST)
  bot := by
    simp only [pair, decide_eq_false_iff_not]
    intro hh
    have hcard := Finset.card_le_card hh
    simp only [Finset.card_empty,hP] at hcard
    omega
  top := decide_eq_true (Finset.subset_univ _)
  edge i := by
    have hlo : ¬P ⊆ lower i := by
      intro hh
      have hcard := Finset.card_le_card hh
      simp only [lower,Finset.card_singleton,hP] at hcard
      omega
    have hup : ¬P ⊆ upper i := by
      intro hh
      apply hbad i
      apply Finset.eq_of_subset_of_card_le hh
      simp [upper,next_ne i,hP]
    simp only [pair,decide_eq_false hlo,decide_eq_false hup]

private def threshold (d : ℕ) (S : Finset (Fin (n+3))) : Bool := decide (d ≤ S.card)

private theorem threshold_good (d : ℕ) (hd : 3≤d) (hdn : d≤n+3) :
    Good (threshold (n:=n) d) where
  mono S T hST h := decide_eq_true ((of_decide_eq_true h).trans (Finset.card_le_card hST))
  bot := by simp [threshold]; omega
  top := by simpa [threshold] using hdn
  edge i := by simp [threshold,lower,upper,next_ne i]; omega

def allBits (S : Finset (Fin (n+3))) : Bool := decide (S=Finset.univ)

theorem allBits_good : Good (allBits (n:=n)) := by
  have he : allBits (n:=n) = threshold (n+3) := by
    funext S
    simp only [allBits,threshold]
    congr 1
    apply propext
    constructor
    · rintro rfl
      simp
    · intro h
      apply Finset.eq_univ_of_card
      have hh : S.card≤n+3 := by simpa using Finset.card_le_univ S
      simpa using Nat.le_antisymm hh h
  rw [he]
  exact threshold_good _ (by omega) le_rfl

@[simp] theorem anyBit_singleton (i : Fin (n+3)) : anyBit {i}=true := by
  simp [anyBit]

@[simp] theorem allBits_upper (i : Fin (n+2)) : allBits (upper i)=false := by
  simp only [allBits,decide_eq_false_iff_not]
  intro he
  have hh := congrArg Finset.card he
  simp [upper,next_ne i] at hh

/-- Exactly the remaining matching pairs fail to admit an allowed Boolean
separator among strict Boolean intervals. -/
theorem separates_iff (L U : Finset (Fin (n+3))) (hLU : L ⊆ U) :
    (∃ f, Good f ∧ f L=false ∧ f U=true) ↔
      L ≠ U ∧ ¬∃ i : Fin (n+2), L=lower i ∧ U=upper i := by
  constructor
  · rintro ⟨f,hf,hL,hU⟩
    refine ⟨?_,?_⟩
    · intro he
      rw [he,hU] at hL
      cases hL
    · rintro ⟨i,rfl,rfl⟩
      have he := hf.edge i
      rw [hL,hU] at he
      cases he
  · rintro ⟨hne,hbad⟩
    have hlt : L.card < U.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hLU,hne⟩)
    by_cases hL : L=∅
    · refine ⟨anyBit,anyBit_good,?_,?_⟩
      · simp [anyBit,hL]
      · apply decide_eq_true
        exact Finset.card_pos.mp (by simp only [hL,Finset.card_empty] at hlt; exact hlt)
    have hLpos : 0 < L.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hL)
    by_cases hU3 : 3≤U.card
    · let d := max 3 (L.card+1)
      have hdU : d≤U.card := max_le hU3 (by omega)
      refine ⟨threshold d,threshold_good d (le_max_left _ _) (hdU.trans (by simpa using Finset.card_le_univ U)),?_,?_⟩
      · simp only [threshold,decide_eq_false_iff_not]
        have hh : L.card+1≤d := le_max_right _ _
        omega
      · exact decide_eq_true hdU
    have hU2 : U.card=2 := by omega
    by_cases hmatch : ∃ i : Fin (n+2), U=upper i
    · obtain ⟨i,rfl⟩ := hmatch
      have hL1 : L.card=1 := by omega
      obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp hL1
      have hj : j∈upper i := hLU (Finset.mem_singleton_self _)
      rcases Finset.mem_insert.mp hj with he | he
      · have hj : j=i.castSucc := he
        subst j
        exact (hbad ⟨i,rfl,rfl⟩).elim
      · have hj : j=i.succ := Finset.mem_singleton.mp he
        subst j
        refine ⟨prefixTest i.castSucc,prefixTest_good _,?_,?_⟩
        · simp only [prefixTest,decide_eq_false_iff_not]
          rintro ⟨j,hj,hji⟩
          have he : j=i.succ := Finset.mem_singleton.mp hj
          subst j
          have hh := Fin.le_iff_val_le_val.mp hji
          simp only [Fin.val_succ,Fin.val_castSucc] at hh
          omega
        · exact decide_eq_true ⟨i.castSucc,Finset.mem_insert_self _ _,le_rfl⟩
    · refine ⟨pair U,pair_good U hU2 (fun i he => hmatch ⟨i,he⟩),?_,decide_eq_true (Finset.Subset.refl _)⟩
      simp only [pair,decide_eq_false_iff_not]
      intro hUL
      exact hne (Finset.Subset.antisymm hLU hUL)

end KFOL.Core.CrownBoolean
