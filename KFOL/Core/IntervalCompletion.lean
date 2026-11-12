module

public import KFOL.Definitions.CoreIntervals
public import KFOL.Core.CrownPatch

/-! # Full winner-valued realization from Boolean interval separators

Greatest completions of all permitted Boolean cuts realize the interval
operation on every winner-valued input, including ambiguous values and
additional owners. Atomic observer interpolation alone is not assumed.
-/

@[expose] public section
namespace KFOL.Core.Intervals
open WinnerSet
universe u v
variable {Role : Type u} {Var : Type v} [Fintype Var]

/-- The two named input cuts always form a Boolean interval. -/
theorem lower_subset_upper (b c : Role) (hbc : b ≠ c)
    (values : Var → WinnerSet Role) : lowerInputs c values ⊆ upperInputs b values := by
  classical
  intro j hj
  simp only [lowerInputs,upperInputs,Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
  intro hb
  exact hbc (WinnerSet.singleton_inj.mp (hb.symm.trans hj))

private noncomputable def anyBit (S : Finset Var) : Bool := by
  classical
  exact decide S.Nonempty

private noncomputable def allBits (S : Finset Var) : Bool := by
  classical
  exact decide (S = Finset.univ)

private theorem anyBit_good [Nonempty Var]
    {selected : Set (Finset Var × Finset Var)} (hp : Proper selected) :
    Good selected (anyBit (Var := Var)) := by
  classical
  refine ⟨?_,by simp [anyBit],by simp [anyBit],?_⟩
  · intro S T hST
    apply Bool.le_iff_imp.mpr
    intro hS
    exact decide_eq_true ((of_decide_eq_true hS).mono hST)
  · intro L U h
    have hL := (hp L U h).1
    have hU := hL.mono (Finset.ssubset_iff_subset_ne.mp (hp L U h).2.1).1
    simp [anyBit,hL,hU]

private theorem allBits_good [Nonempty Var]
    {selected : Set (Finset Var × Finset Var)} (hp : Proper selected) :
    Good selected (allBits (Var := Var)) := by
  classical
  refine ⟨?_,?_,by simp [allBits],?_⟩
  · intro S T hST
    apply Bool.le_iff_imp.mpr
    intro hS
    have hSe : S = Finset.univ := of_decide_eq_true hS
    rw [hSe] at hST
    exact decide_eq_true (Finset.Subset.antisymm (Finset.subset_univ _) hST)
  · simp only [allBits,decide_eq_false_iff_not]
    exact Finset.univ_nonempty.ne_empty.symm
  · intro L U h
    have hU := (hp L U h).2.2
    have hL : L ≠ Finset.univ := by
      intro he
      have hh := (Finset.ssubset_iff_subset_ne.mp (hp L U h).2.1).1
      rw [he] at hh
      exact hU (Finset.Subset.antisymm (Finset.subset_univ _) hh)
    simp [allBits,hL,hU]

private def unionTerms (three : Fin 3 ↪ Role) (xs : List (Term Role Var))
    (base : Term Role Var) : Term Role Var := xs.foldr (Term.unionTerm three) base

omit [Fintype Var] in
private theorem unionTerms_core (three : Fin 3 ↪ Role)
    (xs : List (Term Role Var)) (base : Term Role Var)
    (hb : base.IsCore) (hs : ∀ t ∈ xs, t.IsCore) :
    (unionTerms three xs base).IsCore := by
  induction xs with
  | nil => exact hb
  | cons t ts ih =>
    have ht := hs t (by simp)
    have hi := ih (fun s hs' => hs s (by simp [hs']))
    exact ⟨⟨ht,hi⟩,⟨ht,hi⟩⟩

omit [Fintype Var] in
private theorem mem_unionTerms (three : Fin 3 ↪ Role)
    (xs : List (Term Role Var)) (base : Term Role Var)
    (values : Var → WinnerSet Role) (r : Role) :
    r ∈ ((unionTerms three xs base).eval values).val ↔
      r ∈ (base.eval values).val ∨ ∃ t ∈ xs, r ∈ (t.eval values).val := by
  induction xs with
  | nil => simp [unionTerms]
  | cons t ts ih =>
    change r ∈ ((Term.unionTerm three t (unionTerms three ts base)).eval values).val ↔ _
    rw [Term.eval_unionTerm]
    simp only [WinnerSet.val_union,Set.mem_union,ih,List.mem_cons,exists_eq_or_imp]
    tauto

/-- Two greatest profile completions give one common core cover of every
proper selected interval, without a separation hypothesis. -/
theorem exists_collapsed_cover [Fintype Role] [Nonempty Var] (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (hp : Proper selected) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ values,
      (lowerInputs (three 2) values,upperInputs (three 1) values) ∈ selected →
        t.eval values = (WinnerSet.singleton (three 1)).union (WinnerSet.singleton (three 2)) := by
  classical
  have hbc : three 1 ≠ three 2 := three.injective.ne (by decide)
  have hOr := anyBit_good hp
  have hAnd := allBits_good hp
  obtain ⟨s,hs,hsc,_,_,_⟩ := Crown.exists_set_completion three (three 1) (three 2)
    hbc anyBit hOr.mono hOr.bot hOr.top
  obtain ⟨t,ht,_,htb,_,_⟩ := Crown.exists_set_completion three (three 1) (three 2)
    hbc allBits hAnd.mono hAnd.bot hAnd.top
  refine ⟨Term.unionTerm three s t,⟨⟨hs,ht⟩,⟨hs,ht⟩⟩,?_⟩
  intro values hv
  have hc : s.eval values = WinnerSet.singleton (three 2) := by
    apply (hsc values).mpr
    exact decide_eq_true (hp _ _ hv).1
  have hb : t.eval values = WinnerSet.singleton (three 1) := by
    apply (htb values).mpr
    simpa only [allBits,upperInputs,decide_eq_false_iff_not] using (hp _ _ hv).2.2
  rw [Term.eval_unionTerm,hc,hb]
  apply Subtype.ext
  exact Set.union_comm _ _

/-- Boolean separation of every unselected strict interval realizes the full
winner-valued operation, uniformly over every ambiguous input and extra owner. -/
theorem exists_completion [Fintype Role] [Nonempty Var] (three : Fin 3 ↪ Role)
    (selected : Set (Finset Var × Finset Var)) (hp : Proper selected)
    (hsep : ∀ L U, L ⊂ U → (L,U) ∉ selected → Separates selected L U) :
    ∃ t : Term Role Var, t.IsCore ∧ ∀ values,
      t.eval values = operation (three 1) (three 2) selected values := by
  classical
  let b := three 1
  let c := three 2
  have hbc : b ≠ c := three.injective.ne (by decide)
  let A := {φ : Finset Var → Bool // Good selected φ}
  let : Fintype A := Fintype.ofFinite A
  let aOr : A := ⟨anyBit,anyBit_good hp⟩
  let aAnd : A := ⟨allBits,allBits_good hp⟩
  have hex (f : A) := Crown.exists_set_completion three b c hbc f.val f.property.mono
    f.property.bot f.property.top
  choose e he hec heb heother hegap using hex
  let t := unionTerms three (Finset.univ.toList.map e) (e aOr)
  have ht : t.IsCore := by
    apply unionTerms_core three _ _ (he aOr)
    intro s hs
    obtain ⟨f,_,rfl⟩ := List.mem_map.mp hs
    exact he f
  have hmem (values : Var → WinnerSet Role) (r : Role) :
      r ∈ (t.eval values).val ↔ ∃ f : A, r ∈ ((e f).eval values).val := by
    change r ∈ ((unionTerms three (Finset.univ.toList.map e) (e aOr)).eval values).val ↔ _
    rw [mem_unionTerms]
    constructor
    · rintro (h | ⟨s,hs,hr⟩)
      · exact ⟨aOr,h⟩
      · obtain ⟨f,_,rfl⟩ := List.mem_map.mp hs
        exact ⟨f,hr⟩
    · rintro ⟨f,hf⟩
      exact Or.inr ⟨e f,List.mem_map.mpr ⟨f,by simp,rfl⟩,hf⟩
  have hbound (values : Var → WinnerSet Role) :
      (t.eval values).val ⊆ ⋃ j, (values j).val := by
    intro r hr
    obtain ⟨f,hf⟩ := (hmem values r).mp hr
    exact (he f).eval_subset_of_support values _
      (fun j _ k hk => Set.mem_iUnion.mpr ⟨j,hk⟩) hf
  have hfull (values : Var → WinnerSet Role)
      (hs : Separates selected (lowerInputs c values) (upperInputs b values)) :
      (t.eval values).val = ⋃ j, (values j).val := by
    obtain ⟨φ,hφ,hL,hU⟩ := hs
    let f : A := ⟨φ,hφ⟩
    have hh : ((e f).eval values).val = ⋃ j, (values j).val := hegap f values hL hU
    apply Set.Subset.antisymm (hbound values)
    intro r hr
    exact (hmem values r).mpr ⟨f,by rw [hh]; exact hr⟩
  have hcollapsed (values : Var → WinnerSet Role)
      (hF : (lowerInputs c values,upperInputs b values) ∈ selected) :
      t.eval values = (WinnerSet.singleton b).union (WinnerSet.singleton c) := by
    have hL := (hp _ _ hF).1
    have hU := (hp _ _ hF).2.2
    have hc : (e aOr).eval values = WinnerSet.singleton c := by
      apply (hec aOr values).mpr
      change anyBit (lowerInputs c values) = true
      exact decide_eq_true hL
    have hb : (e aAnd).eval values = WinnerSet.singleton b := by
      apply (heb aAnd values).mpr
      change allBits (upperInputs b values) = false
      simpa only [allBits,decide_eq_false_iff_not] using hU
    apply Subtype.ext
    change (t.eval values).val = (WinnerSet.singleton b).val ∪ (WinnerSet.singleton c).val
    apply Set.Subset.antisymm
    · intro r hr
      obtain ⟨f,hf⟩ := (hmem values r).mp hr
      have hequal := f.property.edge _ _ hF
      cases hval : f.val (lowerInputs c values) with
      | false =>
        have hvU : f.val (upperInputs b values) = false := hequal.symm.trans hval
        have hat : (e f).eval values = WinnerSet.singleton b := (heb f values).mpr hvU
        exact Or.inl (by simpa only [hat] using hf)
      | true =>
        have hat : (e f).eval values = WinnerSet.singleton c := (hec f values).mpr hval
        exact Or.inr (by simpa only [hat] using hf)
    · intro r hr
      rcases hr with hr | hr
      · exact (hmem values r).mpr ⟨aAnd,by simpa only [hb] using hr⟩
      · exact (hmem values r).mpr ⟨aOr,by simpa only [hc] using hr⟩
  have hequal (values : Var → WinnerSet Role)
      (hLU : lowerInputs c values = upperInputs b values) :
      (t.eval values).val = ⋃ j, (values j).val := by
    have hvalues (j) : values j = WinnerSet.singleton b ∨ values j = WinnerSet.singleton c := by
      by_cases hjb : values j = WinnerSet.singleton b
      · exact Or.inl hjb
      · right
        have hm : j ∈ upperInputs b values := by simp [upperInputs,hjb]
        rw [← hLU] at hm
        simpa only [lowerInputs,Finset.mem_filter,Finset.mem_univ,true_and] using hm
    apply Set.Subset.antisymm (hbound values)
    intro r hr
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hr
    rcases hvalues j with hjb | hjc
    · have hU : upperInputs b values ≠ Finset.univ := by
        intro hh
        have hm : j ∈ upperInputs b values := by rw [hh]; simp
        simp [upperInputs,hjb] at hm
      have hb : (e aAnd).eval values = WinnerSet.singleton b := by
        apply (heb aAnd values).mpr
        change allBits (upperInputs b values) = false
        simpa only [allBits,decide_eq_false_iff_not] using hU
      exact (hmem values r).mpr ⟨aAnd,by simpa only [hb,hjb] using hj⟩
    · have hL : (lowerInputs c values).Nonempty := ⟨j,by simp [lowerInputs,hjc]⟩
      have hc : (e aOr).eval values = WinnerSet.singleton c := by
        apply (hec aOr values).mpr
        change anyBit (lowerInputs c values) = true
        exact decide_eq_true hL
      exact (hmem values r).mpr ⟨aOr,by simpa only [hc,hjc] using hj⟩
  refine ⟨t,ht,fun values => ?_⟩
  unfold operation
  split_ifs with hF
  · exact hcollapsed values hF
  · apply Subtype.ext
    change (t.eval values).val = ⋃ j, (values j).val
    by_cases hLU : lowerInputs c values = upperInputs b values
    · exact hequal values hLU
    · exact hfull values (hsep _ _
        (Finset.ssubset_iff_subset_ne.mpr ⟨lower_subset_upper b c hbc values,hLU⟩) hF)

end KFOL.Core.Intervals
