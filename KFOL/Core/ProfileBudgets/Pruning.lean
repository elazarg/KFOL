module

public import KFOL.Definitions.ProfileBudgets
public import KFOL.Core.ProfileSynthesis
public import KFOL.Core.Exhaustion

/-! # Uniform pruning to the single permitted absorbing owner -/

@[expose] public section
namespace KFOL.Core.ProfileBudgets
universe u v w
variable {Role : Type u} [DecidableEq Role] {Var : Type v} {Row : Type w}
attribute [local instance] Equational.coreStructure
abbrev CoreTerm (Role : Type u) (Var : Type v) :=
  Equational.Term (Equational.CoreSymbol Role) Var

/-- Retain distinguished-owner gates and choose one child at all other gates. -/
inductive Prunes (r : Role) : CoreTerm Role Var → CoreTerm Role Var → Prop
  | var (j : Var) : Prunes r (.var j) (.var j)
  | owned {x y x' y'} : Prunes r x x' → Prunes r y y' →
      Prunes r (choiceTerm r x y) (choiceTerm r x' y')
  | left {s x y x'} : s ≠ r → Prunes r x x' → Prunes r (choiceTerm s x y) x'
  | right {s x y y'} : s ≠ r → Prunes r y y' → Prunes r (choiceTerm s x y) y'

theorem Prunes.owner_profile {r : Role} {t s : CoreTerm Role Var} (h : Prunes r t s)
    (A : Var → Bool) : profile r A t = true → profile r A s = true := by
  induction h with
  | var => exact id
  | owned hx hy ihx ihy => simpa only [profile_choice,ite_true,Bool.or_eq_true] using
      (Or.imp ihx ihy)
  | left hsr hx ih =>
    simp only [profile_choice,ite_eq_right hsr,Bool.and_eq_true]
    exact fun hh => ih hh.1
  | right hsr hy ih =>
    simp only [profile_choice,ite_eq_right hsr,Bool.and_eq_true]
    exact fun hh => ih hh.2

private theorem no_foreign_atom (b : Row → Budget Role Var) (r : Role)
    (h : SingleAbsorber b r) (i : Row) (s : Role) (hs : s ∈ (b i).allowed)
    (hsr : s ≠ r) (t : CoreTerm Role Var) :
    t.realize (b i).values ≠ WinnerSet.singleton s := by
  intro he
  have hp := (winnerSet_eq_singleton_iff_profile t s (b i).values).mp he
  have hb : (fun j => decide ((b i).values j = WinnerSet.singleton s)) = fun _ => false := by
    funext j
    exact decide_eq_false (h i s hs hsr j)
  rw [hb,profile_false] at hp
  cases hp

/-- The same pruning preserves every budget at once. Existing distinguished
absorptions survive, including where the other child violates the budget. -/
theorem Prunes.satisfies {b : Row → Budget Role Var} {r : Role}
    (habs : SingleAbsorber b r) {t s : CoreTerm Role Var} (h : Prunes r t s)
    (ht : Satisfies b t) : Satisfies b s := by
  have pointwise : ∀ i, (t.realize (b i).values).val ⊆ (b i).allowed →
      (s.realize (b i).values).val ⊆ (b i).allowed := by
    clear ht
    induction h with
    | var => exact fun _ hh => hh
    | @owned x y x' y' hx hy ihx ihy =>
      intro i hb
      by_cases ha : x.realize (b i).values = WinnerSet.singleton r ∨
          y.realize (b i).values = WinnerSet.singleton r
      · have hparent : (choiceTerm r x y).realize (b i).values = WinnerSet.singleton r := by
          change WinnerSet.choice r _ _ = _
          simp [WinnerSet.choice,ha]
        have hrU : r ∈ (b i).allowed := hb (by rw [hparent]; rfl)
        have ha' : x'.realize (b i).values = WinnerSet.singleton r ∨
            y'.realize (b i).values = WinnerSet.singleton r := by
          rcases ha with ha | ha
          · exact Or.inl ((winnerSet_eq_singleton_iff_profile x' r _).mpr
              (hx.owner_profile _ ((winnerSet_eq_singleton_iff_profile x r _).mp ha)))
          · exact Or.inr ((winnerSet_eq_singleton_iff_profile y' r _).mpr
              (hy.owner_profile _ ((winnerSet_eq_singleton_iff_profile y r _).mp ha)))
        change (WinnerSet.choice r (x'.realize (b i).values) (y'.realize (b i).values)).val ⊆ _
        rw [WinnerSet.choice,ite_eq_left ha']
        exact Set.singleton_subset_iff.mpr hrU
      · have hb' : (x.realize (b i).values).val ∪ (y.realize (b i).values).val ⊆
            (b i).allowed := by
          change (WinnerSet.choice r (x.realize (b i).values) (y.realize (b i).values)).val ⊆ _ at hb
          simpa only [WinnerSet.choice,ite_eq_right ha,WinnerSet.union] using hb
        exact (WinnerSet.choice_subset_union r _ _).trans
          (Set.union_subset (ihx i (Set.Subset.trans Set.subset_union_left hb'))
            (ihy i (Set.Subset.trans Set.subset_union_right hb')))
    | @left o x y x' hor hx ih =>
      intro i hb
      have ha : ¬(x.realize (b i).values = WinnerSet.singleton o ∨
          y.realize (b i).values = WinnerSet.singleton o) := by
        intro ha
        have hp : (choiceTerm o x y).realize (b i).values = WinnerSet.singleton o := by
          change WinnerSet.choice o _ _ = _
          simp [WinnerSet.choice,ha]
        have hoU := hb (by rw [hp]; rfl)
        exact ha.elim (no_foreign_atom b r habs i o hoU hor x)
          (no_foreign_atom b r habs i o hoU hor y)
      have hb' : (x.realize (b i).values).val ∪ (y.realize (b i).values).val ⊆
          (b i).allowed := by
        change (WinnerSet.choice o (x.realize (b i).values) (y.realize (b i).values)).val ⊆ _ at hb
        simpa only [WinnerSet.choice,ite_eq_right ha,WinnerSet.union] using hb
      exact ih i (Set.Subset.trans Set.subset_union_left hb')
    | @right o x y y' hor hy ih =>
      intro i hb
      have ha : ¬(x.realize (b i).values = WinnerSet.singleton o ∨
          y.realize (b i).values = WinnerSet.singleton o) := by
        intro ha
        have hp : (choiceTerm o x y).realize (b i).values = WinnerSet.singleton o := by
          change WinnerSet.choice o _ _ = _
          simp [WinnerSet.choice,ha]
        have hoU := hb (by rw [hp]; rfl)
        exact ha.elim (no_foreign_atom b r habs i o hoU hor x)
          (no_foreign_atom b r habs i o hoU hor y)
      have hb' : (x.realize (b i).values).val ∪ (y.realize (b i).values).val ⊆
          (b i).allowed := by
        change (WinnerSet.choice o (x.realize (b i).values) (y.realize (b i).values)).val ⊆ _ at hb
        simpa only [WinnerSet.choice,ite_eq_right ha,WinnerSet.union] using hb
      exact ih i (Set.Subset.trans Set.subset_union_right hb')
  exact fun i => pointwise i (ht i)

/-- Every same-owner positive/negative query survives some uniform pruning. -/
theorem exists_pruning_pair (r q : Role) (A B : Var → Bool) (t : CoreTerm Role Var) :
    ∃ s, Prunes r t s ∧
      (profile q A t = true → profile q A s = true) ∧
      (profile q B t = false → profile q B s = false) := by
  induction t using induction_choice with
  | var j => exact ⟨.var j,.var j,id,id⟩
  | choice o x y hx hy =>
    obtain ⟨x',hxx,hxp,hxn⟩ := hx
    obtain ⟨y',hyy,hyp,hyn⟩ := hy
    by_cases hor : o = r
    · subst o
      refine ⟨choiceTerm r x' y',.owned hxx hyy,?_,?_⟩
      · by_cases hrq : r = q
        · simpa only [profile_choice,ite_eq_left hrq,Bool.or_eq_true] using Or.imp hxp hyp
        · simpa only [profile_choice,ite_eq_right hrq,Bool.and_eq_true] using And.imp hxp hyp
      · by_cases hrq : r = q
        · simpa only [profile_choice,ite_eq_left hrq,Bool.or_eq_false_iff] using And.imp hxn hyn
        · simpa only [profile_choice,ite_eq_right hrq,Bool.and_eq_false_iff] using Or.imp hxn hyn
    · by_cases hoq : o = q
      · by_cases hxa : profile q A x = true
        · refine ⟨x',.left hor hxx,fun _ => hxp hxa,?_⟩
          intro hb
          have hh : profile q B x = false ∧ profile q B y = false := by
            simpa only [profile_choice,ite_eq_left hoq,Bool.or_eq_false_iff] using hb
          exact hxn hh.1
        · refine ⟨y',.right hor hyy,?_,?_⟩
          · intro ha
            have hh : profile q A x = true ∨ profile q A y = true := by
              simpa only [profile_choice,ite_eq_left hoq,Bool.or_eq_true] using ha
            exact hyp (hh.resolve_left hxa)
          · intro hb
            have hh : profile q B x = false ∧ profile q B y = false := by
              simpa only [profile_choice,ite_eq_left hoq,Bool.or_eq_false_iff] using hb
            exact hyn hh.2
      · by_cases hxb : profile q B x = false
        · refine ⟨x',.left hor hxx,?_,fun _ => hxn hxb⟩
          intro ha
          have hh : profile q A x = true ∧ profile q A y = true := by
            simpa only [profile_choice,ite_eq_right hoq,Bool.and_eq_true] using ha
          exact hxp hh.1
        · refine ⟨y',.right hor hyy,?_,?_⟩
          · intro ha
            have hh : profile q A x = true ∧ profile q A y = true := by
              simpa only [profile_choice,ite_eq_right hoq,Bool.and_eq_true] using ha
            exact hyp hh.2
          · intro hb
            have hh : profile q B x = false ∨ profile q B y = false := by
              simpa only [profile_choice,ite_eq_right hoq,Bool.and_eq_false_iff] using hb
            exact hyn (hh.resolve_left hxb)

/-- A rainbow of positive requests survives some pruning simultaneously. -/
theorem exists_pruning_rainbow (r : Role) (J : Finset Role) (A : Role → Var → Bool)
    (t : CoreTerm Role Var) (ht : ∀ q ∈ J, profile q (A q) t = true) :
    ∃ s, Prunes r t s ∧ ∀ q ∈ J, profile q (A q) s = true := by
  have stronger : ∃ s, Prunes r t s ∧
      ∀ q ∈ J, q ≠ r → profile q (A q) s = true := by
    have aux : ∀ t : CoreTerm Role Var,
        (∀ q ∈ J, q ≠ r → profile q (A q) t = true) →
        ∃ s, Prunes r t s ∧ ∀ q ∈ J, q ≠ r → profile q (A q) s = true := by
      intro t
      induction t using induction_choice with
      | var j => exact fun h => ⟨.var j,.var j,h⟩
      | choice o x y hx hy =>
        intro h
        by_cases hor : o = r
        · subst o
          have hxy (q : Role) (hq : q ∈ J) (hqr : q ≠ r) :
              profile q (A q) x = true ∧ profile q (A q) y = true := by
            simpa only [profile_choice,ite_eq_right (Ne.symm hqr),Bool.and_eq_true] using h q hq hqr
          obtain ⟨x',hxx,hxp⟩ := hx (fun q hq hqr => (hxy q hq hqr).1)
          obtain ⟨y',hyy,hyp⟩ := hy (fun q hq hqr => (hxy q hq hqr).2)
          refine ⟨choiceTerm r x' y',.owned hxx hyy,?_⟩
          intro q hq hqr
          simp only [profile_choice,ite_eq_right (Ne.symm hqr),Bool.and_eq_true]
          exact ⟨hxp q hq hqr,hyp q hq hqr⟩
        · have other (q : Role) (hq : q ∈ J) (hqr : q ≠ r) (hoq : o ≠ q) :
              profile q (A q) x = true ∧ profile q (A q) y = true := by
            simpa only [profile_choice,ite_eq_right hoq,Bool.and_eq_true] using h q hq hqr
          by_cases hoJ : o ∈ J
          · have hh : profile o (A o) x = true ∨ profile o (A o) y = true := by
              simpa only [profile_choice,ite_true,Bool.or_eq_true] using h o hoJ hor
            rcases hh with hh | hh
            · have hp (q : Role) (hq : q ∈ J) (hqr : q ≠ r) : profile q (A q) x = true := by
                by_cases hoq : o = q
                · simpa only [← hoq] using hh
                · exact (other q hq hqr hoq).1
              obtain ⟨x',hxx,hxp⟩ := hx hp
              exact ⟨x',.left hor hxx,hxp⟩
            · have hp (q : Role) (hq : q ∈ J) (hqr : q ≠ r) : profile q (A q) y = true := by
                by_cases hoq : o = q
                · simpa only [← hoq] using hh
                · exact (other q hq hqr hoq).2
              obtain ⟨y',hyy,hyp⟩ := hy hp
              exact ⟨y',.right hor hyy,hyp⟩
          · have hp (q : Role) (hq : q ∈ J) (hqr : q ≠ r) : profile q (A q) x = true :=
              (other q hq hqr (fun he => hoJ (he.symm ▸ hq))).1
            obtain ⟨x',hxx,hxp⟩ := hx hp
            exact ⟨x',.left hor hxx,hxp⟩
    exact aux t (fun q hq _ => ht q hq)
  obtain ⟨s,hp,hs⟩ := stronger
  refine ⟨s,hp,?_⟩
  intro q hq
  by_cases hqr : q = r
  · subst q
    exact hp.owner_profile _ (ht r hq)
  · exact hs q hq hqr

end KFOL.Core.ProfileBudgets
