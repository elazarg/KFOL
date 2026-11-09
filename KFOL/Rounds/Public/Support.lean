module

public import KFOL.Rounds.Public.Values
public import KFOL.Strategic.Adequacy

/-! # Mixing preserves the pure possible-winner observation on public trees -/
@[expose] public section
noncomputable section
namespace KFOL.Rounds.Game
open GameTheory.Math.Probability
open GameTheory.Languages.Bridges.FOSGToEFG
universe u
variable {Role : Type u} [DecidableEq Role] [Fintype Role]

omit [DecidableEq Role] [Fintype Role] in
private theorem pure_of_mass_one (law : PMF Role) (owner : Role)
    (mass : (law owner).toReal = 1) : law = PMF.pure owner := by
  apply pmf_eq_pure_of_support_subset_singleton
  have he : law owner = 1 := (ENNReal.toReal_eq_toReal_iff'
    (law.apply_ne_top owner) (by simp)).mp (by simpa using mass)
  exact ((law.apply_eq_one_iff owner).mp he).subset

omit [DecidableEq Role] [Fintype Role] in
private theorem pure_of_support (law : PMF Role) (owner : Role)
    (support : law.support ⊆ {owner}) : law = PMF.pure owner :=
  pmf_eq_pure_of_support_subset_singleton law owner support

private theorem owner_le_mixture_left (α x y : ℝ) (h1 : α ≤ 1)
    (prefer : α < 1 → x ≤ y) : x ≤ α*x+(1-α)*y := by
  by_cases he : α = 1
  · simp [he]
  · have hlt := lt_of_le_of_ne h1 he
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (prefer hlt))]

private theorem owner_le_mixture_right (α x y : ℝ) (h0 : 0 ≤ α)
    (prefer : 0 < α → y ≤ x) : y ≤ α*x+(1-α)*y := by
  by_cases he : α = 0
  · simp [he]
  · have hlt := lt_of_le_of_ne h0 (Ne.symm he)
    nlinarith [mul_nonneg h0 (sub_nonneg.mpr (prefer hlt))]

/-- A child whose only possible mixed winner is the owner forces that owner
with probability one at the parent, independently of the other child. -/
theorem publicChoice_forced (owner : Role) (left right : Game Role) (order : ExplicitOrder Role)
    (forced : (∀ p ∈ left.sequentialValues order, p = PMF.pure owner) ∨
      (∀ q ∈ right.sequentialValues order, q = PMF.pure owner))
    (value : PMF Role) (hv : value ∈ (publicChoice owner left right).sequentialValues order) :
    value = PMF.pure owner := by
  obtain ⟨p,hp,q,hq,α,h0,h1,prefer0,prefer1,hvalue⟩ :=
    (sequentialValues_publicChoice_iff owner left right order value).mp hv
  apply pure_of_mass_one value owner
  have hv1 := pmf_toReal_apply_le_one value owner
  have hmix : (value owner).toReal = α*(p owner).toReal+(1-α)*(q owner).toReal := by
    rw [hvalue,mix_apply_toReal]
  rcases forced with hf | hf
  · have hleft : (p owner).toReal = 1 := by simp [hf p hp]
    have hle := owner_le_mixture_left α (p owner).toReal (q owner).toReal h1 prefer1
    linarith
  · have hright : (q owner).toReal = 1 := by simp [hf q hq]
    have hle := owner_le_mixture_right α (p owner).toReal (q owner).toReal h0 prefer0
    linarith

omit [Fintype Role] in
private theorem exists_outsider (A : WinnerSet Role) (owner : Role)
    (hne : A ≠ WinnerSet.singleton owner) : ∃ i ∈ A.val, i ≠ owner := by
  by_contra h
  apply hne
  apply WinnerSet.eq_singleton_of_subset
  intro i hi
  by_contra he
  exact h ⟨i,hi,by simpa using he⟩

/-- A semantic induction invariant: mixed distributions use only the pure
winner set, and every pure possible winner still has its Dirac equilibrium. -/
theorem publicTree_support_and_dirac (tree : Strategic.Tree Role) (order : ExplicitOrder Role) :
    (∀ p ∈ (publicTree tree).sequentialValues order, p.support ⊆ (Strategic.value tree).val) ∧
    (∀ i ∈ (Strategic.value tree).val, PMF.pure i ∈ (publicTree tree).sequentialValues order) := by
  induction tree with
  | leaf r =>
    simp only [publicTree,sequentialValues_leaf,Strategic.value_leaf]
    constructor
    · intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      simp
    · intro i hi
      have he : i = r := by simpa only [WinnerSet.singleton,Set.mem_singleton_iff] using hi
      simp [he]
  | node owner left right ihl ihr =>
    simp only [publicTree,Strategic.value_node]
    let A := Strategic.value left
    let B := Strategic.value right
    change (∀ p ∈ (publicTree left).sequentialValues order, p.support ⊆ A.val) ∧
      (∀ i ∈ A.val, PMF.pure i ∈ (publicTree left).sequentialValues order) at ihl
    change (∀ p ∈ (publicTree right).sequentialValues order, p.support ⊆ B.val) ∧
      (∀ i ∈ B.val, PMF.pure i ∈ (publicTree right).sequentialValues order) at ihr
    change (∀ p ∈ (publicChoice owner (publicTree left) (publicTree right)).sequentialValues order,
      p.support ⊆ (WinnerSet.choice owner A B).val) ∧
      (∀ i ∈ (WinnerSet.choice owner A B).val, PMF.pure i ∈
        (publicChoice owner (publicTree left) (publicTree right)).sequentialValues order)
    by_cases forced : A = WinnerSet.singleton owner ∨ B = WinnerSet.singleton owner
    · have hchoice : WinnerSet.choice owner A B = WinnerSet.singleton owner := by
        simp only [WinnerSet.choice,forced,ite_true]
      constructor
      · intro p hp
        have hf : (∀ q ∈ (publicTree left).sequentialValues order, q = PMF.pure owner) ∨
            (∀ q ∈ (publicTree right).sequentialValues order, q = PMF.pure owner) := by
          rcases forced with he | he
          · exact Or.inl (fun q hq => pure_of_support q owner (by simpa only [he,WinnerSet.singleton] using ihl.1 q hq))
          · exact Or.inr (fun q hq => pure_of_support q owner (by simpa only [he,WinnerSet.singleton] using ihr.1 q hq))
        rw [publicChoice_forced owner _ _ order hf p hp]
        simpa only [hchoice] using (show (PMF.pure owner).support ⊆ (WinnerSet.singleton owner).val by simp)
      · intro i hi
        have hio : i = owner := by simpa only [hchoice,WinnerSet.singleton,Set.mem_singleton_iff] using hi
        obtain ⟨p,hp⟩ := (publicChoice owner (publicTree left) (publicTree right)).sequentialValues_nonempty order
        have hf : p = PMF.pure owner := by
          apply publicChoice_forced owner _ _ order _ p hp
          rcases forced with he | he
          · exact Or.inl (fun q hq => pure_of_support q owner (by simpa only [he,WinnerSet.singleton] using ihl.1 q hq))
          · exact Or.inr (fun q hq => pure_of_support q owner (by simpa only [he,WinnerSet.singleton] using ihr.1 q hq))
        simpa only [hf,hio] using hp
    · have ha : A ≠ WinnerSet.singleton owner := fun he => forced (Or.inl he)
      have hb : B ≠ WinnerSet.singleton owner := fun he => forced (Or.inr he)
      have hchoice : (WinnerSet.choice owner A B).val = A.val ∪ B.val := by
        simp only [WinnerSet.choice,forced,ite_false,WinnerSet.union]
      constructor
      · intro value hv i hi
        rw [hchoice]
        obtain ⟨p,hp,q,hq,α,h0,h1,_prefer0,_prefer1,hvalue⟩ :=
          (sequentialValues_publicChoice_iff owner _ _ order value).mp hv
        by_cases hia : i ∈ A.val
        · exact Or.inl hia
        by_cases hib : i ∈ B.val
        · exact Or.inr hib
        have hp0 : p i = 0 := by
          by_contra hn
          exact hia (ihl.1 p hp hn)
        have hq0 : q i = 0 := by
          by_contra hn
          exact hib (ihr.1 q hq hn)
        change value i ≠ 0 at hi
        exact False.elim (hi (by simp [hvalue,mix_apply,hp0,hq0]))
      · intro i hi
        rw [hchoice] at hi
        rcases hi with hi | hi
        · obtain ⟨j,hj,hjo⟩ := exists_outsider B owner hb
          apply (sequentialValues_publicChoice_iff owner _ _ order _).mpr
          refine ⟨PMF.pure i,ihl.2 i hi,PMF.pure j,ihr.2 j hj,1,by norm_num,le_rfl,?_,?_,?_⟩
          · intro _
            simp only [PMF.pure_apply,Ne.symm hjo,ite_false,ENNReal.toReal_zero]
            exact ENNReal.toReal_nonneg
          · norm_num
          · simp
        · obtain ⟨j,hj,hjo⟩ := exists_outsider A owner ha
          apply (sequentialValues_publicChoice_iff owner _ _ order _).mpr
          refine ⟨PMF.pure j,ihl.2 j hj,PMF.pure i,ihr.2 i hi,0,le_rfl,by norm_num,?_,?_,?_⟩
          · norm_num
          · intro _
            simp only [PMF.pure_apply,Ne.symm hjo,ite_false,ENNReal.toReal_zero]
            exact ENNReal.toReal_nonneg
          · simp

/-- Mixed serial sequential equilibria add no possible winner to the
independently defined pure full-profile SPE observation of a public tree. -/
theorem possibleWinners_publicTree (tree : Strategic.Tree Role) (order : ExplicitOrder Role) :
    possibleWinners ((publicTree tree).sequentialValues order) = (Strategic.value tree).val := by
  obtain ⟨upper,dirac⟩ := publicTree_support_and_dirac tree order
  ext i
  constructor
  · rintro ⟨p,hp,hi⟩
    exact upper p hp hi
  · intro hi
    exact ⟨PMF.pure i,dirac i hi,by simp⟩

end KFOL.Rounds.Game
