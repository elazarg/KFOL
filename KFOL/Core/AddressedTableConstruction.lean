module

public import KFOL.Core.AddressedLogicalGroups
public import KFOL.Core.AddressedTableExtraction
public import KFOL.Core.BichainRecognition

/-! # Realizing the complete addressed table from a pure separator -/

@[expose] public section
namespace KFOL.Core.AddressedTableConstruction

open AddressedRails AddressedRectangle AddressedLogicalGroups AddressedTableExtraction
open ProfileBudgets WinnerSet Bichain
open scoped Classical
attribute [local instance] Equational.coreStructure

variable {Role Label Track Bit Row : Type*} [DecidableEq Role] {B : Book Label Track Bit}

private def rotate (three : Fin 3 ↪ Role) : Fin 3 ↪ Role :=
  (Equiv.swap 0 2).toEmbedding.trans three

omit [DecidableEq Role] in
private theorem rotated (three : Fin 3 ↪ Role) : rotate three 0 = three 2 ∧
    rotate three 1 = three 1 ∧ rotate three 2 = three 0 := by
  simp [rotate, Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)]

omit [DecidableEq Role] in
private theorem see_raw (three : Fin 3 ↪ Role) (R : Rows B Row) (z : Row) (f : Label) :
    Recognition.see (rotate three) (three 2) (rawValues three R z f) = R.cube z f := by
  obtain ⟨_,one,two⟩ := rotated three
  have n21 : three 2 ≠ three 1 := three.injective.ne (by decide)
  have n20 : three 2 ≠ three 0 := three.injective.ne (by decide)
  by_cases marked : f = R.mark z
  · subst f
    rw [Rows.cube, ite_eq_left rfl]
    exact (Recognition.see_possible_iff _ _ _).mpr (by simp [rawValues, MonochromaticCutObstruction.pureProbe])
  · unfold rawValues MonochromaticCutObstruction.pureProbe
    rw [Sources.probe_other _ _ _ _ f marked, Rows.cube, ite_eq_right marked]
    by_cases posted : f ∈ R.posted z
    · simp only [posted, decide_true, ite_true, Sources.representative]
      cases side : R.left z
      · simpa [posted, side, Sources.representative, one] using
          (Recognition.see_b (rotate three) (three 2) (by rwa [one]))
      · simpa [posted, side, Sources.representative, two] using
          (Recognition.see_c (rotate three) (three 2) (by rwa [two]))
    · simp only [posted, decide_false, Bool.false_eq_true, ite_false]
      have miss (k : Role) (h : k ≠ three 2) :
          Sources.representative three (three 2) .neutral ≠ WinnerSet.singleton k := by
        intro atom
        cases (Sources.representative_atom_iff three (three 2) .neutral ⟨k,h⟩).mp atom
      simp [Recognition.see, one, two, miss _ n21.symm, miss _ n20.symm]

/-- A pure separator in the rectangle provides one logical core word good
for both orientations. The canonical logical losses are evaluated with
the auxiliary observer even if there are additional roles. -/
theorem good_of_pure (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (x y : Label → Bool) (q : Bichain.Term Label) (pure : q.IsPure)
    (quiet : ∀ z ∈ S, q.eval (R.cube z) ≠ .possible)
    (fits : (CubeQuery.separate x y).Holds q) :
    ∃ w, Good three R S true x w ∧ Good three R S false (fun f => !(y f)) w := by
  let p := rotate three
  let c := three 2
  have one : p 1 = three 1 := (rotated three).2.1
  have two : p 2 = three 0 := (rotated three).2.2
  have cb : c ≠ p 1 := by rw [one]; exact three.injective.ne (by decide)
  have ca : c ≠ p 2 := by rw [two]; exact three.injective.ne (by decide)
  let t := Recognition.fromPure p id q
  let w := Equational.Core.encode t (Recognition.fromPure_isCore p id q)
  have same (v : Label → WinnerSet Role) : w.realize v = t.eval v := by
    rw [← Equational.Core.eval_decode, Equational.Core.decode_encode]
  let v (A : Label → Bool) (f : Label) := if A f then WinnerSet.singleton (p 2) else WinnerSet.singleton (p 1)
  have seeEnd (A : Label → Bool) : (fun f => Recognition.see p c (v A (id f))) =
      fun f => Value.ofBool (A f) := by
    funext f
    cases h : A f <;> simp [v, h, Value.ofBool, Recognition.see_b p c cb, Recognition.see_c p c ca]
  have oneTwo : p 1 ≠ p 2 := p.injective.ne (by decide)
  have leftFlags : (fun f => decide (v x f = WinnerSet.singleton (p 2))) = x := by
    funext f; cases h : x f <;> simp [v,h,oneTwo]
  have rightFlags : (fun f => decide (v y f = WinnerSet.singleton (p 1))) = fun f => !(y f) := by
    funext f; cases h : y f <;> simp [v,h,oneTwo.symm]
  have quietW (z : Row) (hz : z ∈ S) : c ∉ (w.realize (rawValues three R z)).val := by
    rw [same]
    apply (Recognition.fromPure_spec p id cb ca _ q pure).2.2
    simpa only [id_eq, p, c, see_raw] using quiet z hz
  refine ⟨w,⟨?_,fun z hz _ => quietW z hz⟩,⟨?_,fun z hz _ => quietW z hz⟩⟩
  · simp only [orient_zero, ite_true]
    rw [← two, ← leftFlags, ← winnerSet_eq_singleton_iff_profile, same]
    apply (Recognition.fromPure_spec p id cb ca _ q pure).2.1
    simpa only [seeEnd] using fits.1
  · simp only [orient_zero, Bool.false_eq_true, ite_false]
    rw [← one, ← rightFlags, ← winnerSet_eq_singleton_iff_profile, same]
    apply (Recognition.fromPure_spec p id cb ca _ q pure).1
    simpa only [seeEnd] using fits.2

variable [Fintype Bit] [Nonempty Bit]

/-- Substituting one address fold at every logical leaf realizes the 
baseline on every valuation, even for a rectangle admitting a cut. -/
theorem realizes_baseline (three : Fin 3 ↪ Role) (B : Book Label Track Bit)
    (left right : CoreTerm Role Label) : ∃ base : CoreTerm Role (Option (Rail Track Bit)), ∀ z v,
      base.realize (fun j => j.elim z v) = AddressedTableExtraction.baseline three B left right z v := by
  obtain ⟨l,hl⟩ := B.substitute (three 2) left
  obtain ⟨r,hr⟩ := B.substitute (three 2) right
  let base := OneOwnerSelector.selectWord three (three 0) (three 1) (.var none)
    (l.relabel some) (r.relabel some)
  have baseEval (z : WinnerSet Role) (v : Rail Track Bit → WinnerSet Role) :
      base.realize (fun j => j.elim z v) = AddressedTableExtraction.baseline three B left right z v := by
    rw [OneOwnerSelector.realize_selectWord, FirstOrder.Language.Term.realize_relabel,
      FirstOrder.Language.Term.realize_relabel]
    change OneOwnerSelector.select _ _ z (l.realize v) (r.realize v) = _
    rw [hl, hr]
    rfl
  exact ⟨base,baseEval⟩

/-- The greatest words of the two groups and a common witness with the
unanimous auxiliary profile realize the exact operation on all menus. -/
theorem realize_target (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (x y : Label → Bool) (left right g : CoreTerm Role Label)
    (envL : Envelope three R S true x left)
    (envR : Envelope three R S false (fun f => !(y f)) right)
    (goodL : Good three R S true x g) (goodR : Good three R S false (fun f => !(y f)) g)
    (unanimous : ∀ A : Label → Bool, profile (three 2) A g = true ↔ ∀ f, A f = true) :
    ∃ t : CoreTerm Role (Option (Rail Track Bit)), ∀ z v,
      t.realize (fun j => j.elim z v) = AddressedTableExtraction.operation three B left right z v := by
  obtain ⟨base,baseEval⟩ := realizes_baseline three B left right
  obtain ⟨h,hh⟩ := B.substitute (three 2) g
  have ab : three 0 ≠ three 1 := three.injective.ne (by decide)
  have bounded (z : WinnerSet Role) (v : Rail Track Bit → WinnerSet Role) :
      (h.realize v).val ⊆ (AddressedTableExtraction.baseline three B left right z v).val := by
    intro k hk
    rw [hh] at hk
    change k ∈ (OneOwnerSelector.select _ _ z _ _).val
    rw [OneOwnerSelector.select_eq _ _ ab]
    split_ifs
    · exact Or.inr (envL.2 g goodL _ hk)
    · exact Or.inr (envR.2 g goodR _ hk)
    · exact Or.inr (Or.inl (envL.2 g goodL _ hk))
  have profileCap (A : Rail Track Bit → Bool) : profile (three 2) A h = cap B A := by
    let val (i : Rail Track Bit) := if A i then WinnerSet.singleton (three 2) else WinnerSet.singleton (three 0)
    have diff : three 0 ≠ three 2 := three.injective.ne (by decide)
    have flags : (fun i => decide (val i = WinnerSet.singleton (three 2))) = A := by
      funext i; cases ai : A i <;> simp [val,ai,diff]
    have iff := (winnerSet_eq_singleton_iff_profile h (three 2) val).symm.trans
      ((hh val).symm ▸ B.unanimous_cap (three 2) g unanimous val)
    rw [flags] at iff
    apply Bool.eq_iff_iff.mpr
    rw [iff]
    simp only [cap, decide_eq_true_eq]
    have bit (i : Rail Track Bit) : val i = WinnerSet.singleton (three 2) ↔ A i = true := by
      cases ai : A i <;> simp [val, ai, diff]
    simp only [bit]
  exact ⟨choiceTerm (three 2) base (h.relabel some),
    AddressedSelectorCap.attach _ _ _ base h baseEval bounded profileCap⟩

end KFOL.Core.AddressedTableConstruction
