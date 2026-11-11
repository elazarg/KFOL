module

public import KFOL.Core.CrownPatch
public import KFOL.Core.CrownRegions
public import KFOL.Core.CrownBoolean

/-! # Realizing a crown with one matching edge removed

Take the union of greatest completions of all Boolean separators allowed by
the cut crown. The only collapsed intervals are its remaining matching edges.
-/

@[expose] public section
namespace KFOL.Core.Crown
open WinnerSet
universe u
variable {Role : Type u} {n : ℕ}

private noncomputable def lowerInputs (c : Role)
    (v : Fin (n+3) → WinnerSet Role) : Finset (Fin (n+3)) := by
  classical
  exact Finset.univ.filter (fun j => v j = WinnerSet.singleton c)

private noncomputable def upperInputs (b : Role)
    (v : Fin (n+3) → WinnerSet Role) : Finset (Fin (n+3)) := by
  classical
  exact Finset.univ.filter (fun j => v j ≠ WinnerSet.singleton b)

private theorem lower_subset_upper (b c : Role) (hbc : b ≠ c)
    (v : Fin (n+3) → WinnerSet Role) : lowerInputs c v ⊆ upperInputs b v := by
  classical
  intro j hj
  simp only [lowerInputs, upperInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  intro hb
  exact hbc (WinnerSet.singleton_inj.mp (hb.symm.trans hj))

private theorem rotate_castSucc (i : Fin (n+2)) :
    finRotate (n+3) i.castSucc = i.succ := by
  exact finRotate_of_lt i.isLt

private theorem nonwrap_cylinder_iff (b c : Role) (hbc : b ≠ c)
    (i : Fin (n+2)) (v : Fin (n+3) → WinnerSet Role) :
    Cylinder b c (finRotate (n+3)) i.castSucc v ↔
      lowerInputs c v = CrownBoolean.lower i ∧ upperInputs b v = CrownBoolean.upper i := by
  classical
  have hne : i.castSucc ≠ i.succ := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  constructor
  · intro h
    have hn := rotate_castSucc i
    refine ⟨?_, ?_⟩
    · ext j
      simp only [lowerInputs, Finset.mem_filter, Finset.mem_univ, true_and,
        CrownBoolean.lower, Finset.mem_singleton]
      exact ⟨fun hj => cylinder_unique_c hbc h hj, fun hj => hj ▸ h.1⟩
    · ext j
      simp only [upperInputs, Finset.mem_filter, Finset.mem_univ, true_and,
        CrownBoolean.upper, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hj
        by_cases hji : j = i.castSucc
        · exact Or.inl hji
        · right
          by_contra hjn
          exact hj (h.2.2.2 j hji (by simpa only [hn] using hjn))
      · rintro (rfl | rfl)
        · intro hb
          exact hbc (WinnerSet.singleton_inj.mp (hb.symm.trans h.1))
        · simpa only [hn] using h.2.1
  · rintro ⟨hL, hU⟩
    have hc : v i.castSucc = WinnerSet.singleton c := by
      have hm : i.castSucc ∈ lowerInputs c v := by rw [hL]; simp [CrownBoolean.lower]
      simpa [lowerInputs] using hm
    have hb : v i.succ ≠ WinnerSet.singleton b := by
      have hm : i.succ ∈ upperInputs b v := by rw [hU]; simp [CrownBoolean.upper]
      simpa [upperInputs] using hm
    refine ⟨hc, ?_, ?_, ?_⟩
    · simpa only [rotate_castSucc] using hb
    · rw [rotate_castSucc]
      intro hcs
      have hm : i.succ ∈ lowerInputs c v := by simp [lowerInputs, hcs]
      rw [hL] at hm
      exact hne (Finset.mem_singleton.mp hm).symm
    · intro j hji hjn
      by_contra hjb
      have hm : j ∈ upperInputs b v := by simp [upperInputs, hjb]
      rw [hU] at hm
      rcases Finset.mem_insert.mp hm with he | he
      · exact hji he
      · exact hjn (by simpa only [rotate_castSucc] using Finset.mem_singleton.mp he)

private theorem selected_cylinder_iff (b c : Role) (hbc : b ≠ c)
    (v : Fin (n+3) → WinnerSet Role) :
    (∃ i ∈ {i : Fin (n+3) | i ≠ Fin.last (n+2)},
      Cylinder b c (finRotate (n+3)) i v) ↔
      ∃ i : Fin (n+2), lowerInputs c v = CrownBoolean.lower i ∧
        upperInputs b v = CrownBoolean.upper i := by
  constructor
  · rintro ⟨j, hj, h⟩
    let i : Fin (n+2) := ⟨j.val, Fin.val_lt_last hj⟩
    have he : i.castSucc = j := Fin.ext rfl
    exact ⟨i, (nonwrap_cylinder_iff b c hbc i v).mp (he ▸ h)⟩
  · rintro ⟨i, hi⟩
    refine ⟨i.castSucc, ?_, (nonwrap_cylinder_iff b c hbc i v).mpr hi⟩
    exact Fin.castSucc_ne_last i

private def unionTerms (three : Fin 3 ↪ Role) (xs : List (Term Role (Fin (n+3))))
    (base : Term Role (Fin (n+3))) : Term Role (Fin (n+3)) :=
  xs.foldr (Term.unionTerm three) base

private theorem unionTerms_core (three : Fin 3 ↪ Role)
    (xs : List (Term Role (Fin (n+3)))) (base : Term Role (Fin (n+3)))
    (hbase : base.IsCore) (hxs : ∀ t ∈ xs, t.IsCore) :
    (unionTerms three xs base).IsCore := by
  induction xs with
  | nil => exact hbase
  | cons t ts ih =>
    have ht := hxs t (by simp)
    have hi := ih (fun s hs => hxs s (by simp [hs]))
    exact ⟨⟨ht, hi⟩, ⟨ht, hi⟩⟩

private theorem mem_unionTerms (three : Fin 3 ↪ Role)
    (xs : List (Term Role (Fin (n+3)))) (base : Term Role (Fin (n+3)))
    (v : Fin (n+3) → WinnerSet Role) (r : Role) :
    r ∈ ((unionTerms three xs base).eval v).val ↔
      r ∈ (base.eval v).val ∨ ∃ t ∈ xs, r ∈ (t.eval v).val := by
  induction xs with
  | nil => simp [unionTerms]
  | cons t ts ih =>
    change r ∈ ((Term.unionTerm three t (unionTerms three ts base)).eval v).val ↔ _
    rw [Term.eval_unionTerm]
    simp only [WinnerSet.val_union, Set.mem_union, ih, List.mem_cons,
      exists_eq_or_imp]
    tauto

/-- Deleting the wrapping cylinder leaves an actual core operation. -/
theorem exists_base_patch [Fintype Role] (three : Fin 3 ↪ Role) (n : ℕ) :
    ∃ t : Term Role (Fin (n+3)), t.IsCore ∧ ∀ v,
      t.eval v = operation (three 1) (three 2) (finRotate (n+3))
        {i | i ≠ Fin.last (n+2)} v := by
  classical
  let b := three 1
  let c := three 2
  have hbc : b ≠ c := three.injective.ne (by decide)
  let A := {φ : Finset (Fin (n+3)) → Bool // CrownBoolean.Good φ}
  let : Fintype A := Fintype.ofFinite A
  let aOr : A := ⟨CrownBoolean.anyBit, CrownBoolean.anyBit_good⟩
  let aAnd : A := ⟨CrownBoolean.allBits, CrownBoolean.allBits_good⟩
  have hm (f : A) : Monotone f.val := by
    intro S T hST
    apply Bool.le_iff_imp.mpr
    exact f.property.mono S T hST
  have hex (f : A) := exists_set_completion three b c hbc f.val (hm f)
    f.property.bot f.property.top
  choose e he hec heb heother hegap using hex
  let t := unionTerms three (Finset.univ.toList.map e) (e aOr)
  have ht : t.IsCore := by
    apply unionTerms_core three _ _ (he aOr)
    intro s hs
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hs
    exact he f
  have hmem (v : Fin (n+3) → WinnerSet Role) (r : Role) :
      r ∈ (t.eval v).val ↔ ∃ f : A, r ∈ ((e f).eval v).val := by
    change r ∈ ((unionTerms three (Finset.univ.toList.map e) (e aOr)).eval v).val ↔ _
    rw [mem_unionTerms]
    constructor
    · rintro (h | ⟨s, hs, hr⟩)
      · exact ⟨aOr, h⟩
      · obtain ⟨f, _, rfl⟩ := List.mem_map.mp hs
        exact ⟨f, hr⟩
    · rintro ⟨f, hf⟩
      exact Or.inr ⟨e f, List.mem_map.mpr ⟨f, by simp, rfl⟩, hf⟩
  have hbound (v : Fin (n+3) → WinnerSet Role) :
      (t.eval v).val ⊆ ⋃ j, (v j).val := by
    intro r hr
    obtain ⟨f, hf⟩ := (hmem v r).mp hr
    exact (he f).eval_subset_of_support v _ (fun j _ k hk => Set.mem_iUnion.mpr ⟨j,hk⟩) hf
  have hfull (v : Fin (n+3) → WinnerSet Role)
      (hsep : ∃ φ, CrownBoolean.Good φ ∧
        φ (lowerInputs c v) = false ∧ φ (upperInputs b v) = true) :
      (t.eval v).val = ⋃ j, (v j).val := by
    obtain ⟨φ, hφ, hL, hU⟩ := hsep
    let f : A := ⟨φ,hφ⟩
    have hh : ((e f).eval v).val = ⋃ j, (v j).val := hegap f v hL hU
    apply Set.Subset.antisymm (hbound v)
    intro r hr
    exact (hmem v r).mpr ⟨f, by rw [hh]; exact hr⟩
  have hcollapsed (v : Fin (n+3) → WinnerSet Role) (i : Fin (n+2))
      (hL : lowerInputs c v = CrownBoolean.lower i)
      (hU : upperInputs b v = CrownBoolean.upper i) :
      t.eval v = (WinnerSet.singleton b).union (WinnerSet.singleton c) := by
    have hc : (e aOr).eval v = WinnerSet.singleton c := by
      apply (hec aOr v).mpr
      change CrownBoolean.anyBit (lowerInputs c v) = true
      rw [hL]
      exact CrownBoolean.anyBit_singleton _
    have hb : (e aAnd).eval v = WinnerSet.singleton b := by
      apply (heb aAnd v).mpr
      change CrownBoolean.allBits (upperInputs b v) = false
      rw [hU]
      exact CrownBoolean.allBits_upper i
    apply Subtype.ext
    change (t.eval v).val = (WinnerSet.singleton b).val ∪ (WinnerSet.singleton c).val
    apply Set.Subset.antisymm
    · intro r hr
      obtain ⟨f, hf⟩ := (hmem v r).mp hr
      have hequal : f.val (lowerInputs c v) = f.val (upperInputs b v) := by
        rw [hL,hU]
        exact f.property.edge i
      cases hval : f.val (lowerInputs c v) with
      | false =>
        have hvU : f.val (upperInputs b v) = false := hequal.symm.trans hval
        have hat : (e f).eval v = WinnerSet.singleton b := (heb f v).mpr hvU
        exact Or.inl (by simpa only [hat] using hf)
      | true =>
        have hat : (e f).eval v = WinnerSet.singleton c := (hec f v).mpr hval
        exact Or.inr (by simpa only [hat] using hf)
    · intro r hr
      rcases hr with hr | hr
      · exact (hmem v r).mpr ⟨aAnd, by simpa only [hb] using hr⟩
      · exact (hmem v r).mpr ⟨aOr, by simpa only [hc] using hr⟩
  have hequal (v : Fin (n+3) → WinnerSet Role)
      (hLU : lowerInputs c v = upperInputs b v) :
      (t.eval v).val = ⋃ j, (v j).val := by
    have hvalues (j) : v j = WinnerSet.singleton b ∨ v j = WinnerSet.singleton c := by
      by_cases hjb : v j = WinnerSet.singleton b
      · exact Or.inl hjb
      · right
        have hm : j ∈ upperInputs b v := by simp [upperInputs,hjb]
        rw [← hLU] at hm
        simpa only [lowerInputs,Finset.mem_filter,Finset.mem_univ,true_and] using hm
    apply Set.Subset.antisymm (hbound v)
    intro r hr
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hr
    rcases hvalues j with hjb | hjc
    · have hU : upperInputs b v ≠ Finset.univ := by
        intro hh
        have hm : j ∈ upperInputs b v := by rw [hh]; simp
        simp [upperInputs,hjb] at hm
      have hb : (e aAnd).eval v = WinnerSet.singleton b := by
        apply (heb aAnd v).mpr
        change CrownBoolean.allBits (upperInputs b v) = false
        simpa only [CrownBoolean.allBits,decide_eq_false_iff_not] using hU
      exact (hmem v r).mpr ⟨aAnd, by simpa only [hb,hjb] using hj⟩
    · have hL : (lowerInputs c v).Nonempty := ⟨j,by simp [lowerInputs,hjc]⟩
      have hc : (e aOr).eval v = WinnerSet.singleton c := by
        apply (hec aOr v).mpr
        change CrownBoolean.anyBit (lowerInputs c v) = true
        exact decide_eq_true hL
      exact (hmem v r).mpr ⟨aOr, by simpa only [hc,hjc] using hj⟩
  refine ⟨t,ht,fun v => ?_⟩
  unfold operation
  split_ifs with hcy
  · obtain ⟨i,hL,hU⟩ := (selected_cylinder_iff b c hbc v).mp hcy
    exact hcollapsed v i hL hU
  · apply Subtype.ext
    change (t.eval v).val = ⋃ j, (v j).val
    by_cases hLU : lowerInputs c v = upperInputs b v
    · exact hequal v hLU
    · apply hfull v
      apply (CrownBoolean.separates_iff _ _ (lower_subset_upper b c hbc v)).mpr
      exact ⟨hLU,fun hm => hcy ((selected_cylinder_iff b c hbc v).mpr hm)⟩

end KFOL.Core.Crown
