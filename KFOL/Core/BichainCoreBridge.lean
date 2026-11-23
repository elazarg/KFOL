module

public import KFOL.Core.BichainFiber
public import KFOL.Core.BichainFiniteLabels
public import KFOL.Core.ProfilePruning
public import KFOL.Equational.Native
public import KFOL.Algebra.ViewOrders.Table

/-! # Pure bichain witnesses from core terms -/

@[expose] public section
namespace KFOL.Bichain

variable {Var : Type*}
attribute [local instance] Equational.coreStructure

namespace Term

/-- Keep one branch of each observer union. -/
def selectPure : Term Var → Term Var
  | .var j => .var j
  | .inf x y => .inf x.selectPure y.selectPure
  | .sup x y => .sup x.selectPure y.selectPure
  | .union x _ => x.selectPure

theorem selectPure_isPure (t : Term Var) : t.selectPure.IsPure := by
  induction t <;> simp_all [selectPure, IsPure]

theorem eval_selectPure_resolves (t : Term Var) (v : Var → Value) :
    Value.Resolves (t.selectPure.eval v) (t.eval v) := by
  have hrefl : ∀ x : Value, x.Resolves x := by
    unfold Value.Resolves
    decide +kernel
  have hleft : ∀ x y z : Value, x.Resolves y → x.Resolves (y.union z) := by
    unfold Value.Resolves
    decide +kernel
  induction t with
  | var j => exact hrefl _
  | inf x y hx hy => exact Value.resolves_inf _ _ _ _ hx hy
  | sup x y hx hy => exact Value.resolves_sup _ _ _ _ hx hy
  | union x y hx _ => exact hleft _ _ _ hx

end Term

/-- Translate a three-role core term into its observer-zero term. -/
def toObserver : (t : KFOL.Term (Fin 3) Var) → t.IsCore → Term Var
  | .var j, _ => .var j
  | .choice r x y, h =>
    let left := toObserver x h.1
    let right := toObserver y h.2
    if r = 1 then .inf left right else if r = 2 then .sup left right else .union left right

theorem view_eval_toObserver (t : KFOL.Term (Fin 3) Var) (ht : t.IsCore)
    (v : Var → WinnerSet (Fin 3)) :
    Value.toView ((toObserver t ht).eval (fun j => Value.ofView (WinnerSet.view 0 (v j)))) =
      WinnerSet.view 0 (t.eval v) := by
  induction t with
  | winner r => cases ht
  | rename p t ih => cases ht
  | var j => exact Value.toView_ofView _
  | choice r x y hx hy =>
    have hr : r = 0 ∨ r = 1 ∨ r = 2 := (by decide +kernel : ∀ i : Fin 3,
      i = 0 ∨ i = 1 ∨ i = 2) r
    rcases hr with rfl | rfl | rfl <;>
      simp [toObserver, Term.eval, KFOL.Term.eval, WinnerSet.view_choice,
        show (0 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 2 by decide,
        show (2 : Fin 3) ≠ 1 by decide, hx ht.1, hy ht.2];
      simp [PlayerView.choice]

/-- A single pure term retains every endpoint and every omission of the observer. -/
theorem exists_pure_observer_witness (t : KFOL.Term (Fin 3) Var) (ht : t.IsCore) :
    ∃ p : Term Var, p.IsPure ∧ ∀ v : Var → WinnerSet (Fin 3),
      let q := Value.ofView (WinnerSet.view 0 (t.eval v))
      let w := p.eval (fun j => Value.ofView (WinnerSet.view 0 (v j)))
      (q = .b → w = .b) ∧ (q = .c → w = .c) ∧ (q ≠ .possible → w ≠ .possible) := by
  let s := toObserver t ht
  refine ⟨s.selectPure, s.selectPure_isPure, fun v => ?_⟩
  have h := s.eval_selectPure_resolves (fun j => Value.ofView (WinnerSet.view 0 (v j)))
  have hv := congrArg Value.ofView (view_eval_toObserver t ht v)
  rw [Value.ofView_toView] at hv
  change Value.Resolves _ ((toObserver t ht).eval _) at h
  rw [hv] at h
  have preserve : ∀ w q : Value, w.Resolves q →
      (q = .b → w = .b) ∧ (q = .c → w = .c) ∧ (q ≠ .possible → w ≠ .possible) := by
    unfold Value.Resolves
    decide +kernel
  exact preserve _ _ h

/-- Restrict a core witness to a positive coalition and extract one pure term
that works on all projected rows simultaneously. -/
theorem exists_pure_observer_witness_of_profile
    (t : Equational.Term (Equational.CoreSymbol (Fin 3)) Var) (A : Var → Bool)
    (positive : Core.profile 0 A t = true) :
    ∃ p : Term {x // A x = true}, p.IsPure ∧ ∀ v : Var → WinnerSet (Fin 3),
      let w := p.eval (fun j => Value.ofView (WinnerSet.view 0 (v j.val)))
      (t.realize v = WinnerSet.singleton 1 → w = .b) ∧
      (t.realize v = WinnerSet.singleton 2 → w = .c) ∧
      (0 ∉ (t.realize v).val → w ≠ .possible) := by
  obtain ⟨u, _, hu⟩ := Core.exists_view_below_of_profile 0 A t positive
  obtain ⟨p, hp, hw⟩ := exists_pure_observer_witness _ (Equational.Core.isCore_decode u)
  refine ⟨p, hp, fun v => ?_⟩
  have h := hw (fun j => v j.val)
  rw [Equational.Core.eval_decode] at h
  have hbelow := (WinnerSet.view_below_iff _ _ _).mp (hu v)
  have hb : (1 : Fin 3) ≠ 0 := by decide
  have hc : (2 : Fin 3) ≠ 0 := by decide
  refine ⟨fun e => h.1 ?_, fun e => h.2.1 ?_, fun e => h.2.2 ?_⟩
  · rw [(WinnerSet.view_eq_other_iff 0 _ ⟨1, hb⟩).mpr (hbelow.2 1 hb e)]
    rfl
  · rw [(WinnerSet.view_eq_other_iff 0 _ ⟨2, hc⟩).mpr (hbelow.2 2 hc e)]
    rfl
  · intro mark
    apply e
    apply hbelow.1
    apply (WinnerSet.view_eq_possible_iff _ _).mp
    apply Value.viewEquiv.symm.injective
    exact mark

/-- Realize a bichain expression by owned choice on three roles. -/
def fromObserver : Term Var → KFOL.Term (Fin 3) Var
  | .var j => .var j
  | .inf x y => .choice 1 (fromObserver x) (fromObserver y)
  | .sup x y => .choice 2 (fromObserver x) (fromObserver y)
  | .union x y => .choice 0 (fromObserver x) (fromObserver y)

theorem fromObserver_isCore (p : Term Var) : (fromObserver p).IsCore := by
  induction p <;> simp_all [fromObserver, KFOL.Term.IsCore]

theorem view_eval_fromObserver (p : Term Var) (v : Var → WinnerSet (Fin 3)) :
    WinnerSet.view 0 ((fromObserver p).eval v) =
      Value.toView (p.eval (fun j => Value.ofView (WinnerSet.view 0 (v j)))) := by
  induction p with
  | var j => exact (Value.toView_ofView _).symm
  | inf x y hx hy =>
    simp [fromObserver, Term.eval, KFOL.Term.eval, WinnerSet.view_choice, hx, hy]
  | sup x y hx hy =>
    simp [fromObserver, Term.eval, KFOL.Term.eval, WinnerSet.view_choice, hx, hy]
  | union x y hx hy =>
    simp [fromObserver, Term.eval, KFOL.Term.eval, WinnerSet.view_choice, hx, hy,
      PlayerView.choice]

/-- Endpoint and omission constraints on arbitrary rows are equivalent for
core witnesses and pure bichain witnesses. -/
theorem observer_interpolation_iff {Row : Type*} (rows : Row → Var → WinnerSet (Fin 3))
    (requireB requireC requireOmission : Row → Prop) :
    (∃ t : KFOL.Term (Fin 3) Var, t.IsCore ∧ ∀ r,
      (requireB r → t.eval (rows r) = WinnerSet.singleton 1) ∧
      (requireC r → t.eval (rows r) = WinnerSet.singleton 2) ∧
      (requireOmission r → 0 ∉ (t.eval (rows r)).val)) ↔
    (∃ p : Term Var, p.IsPure ∧ ∀ r,
      let w := p.eval (fun j => Value.ofView (WinnerSet.view 0 (rows r j)))
      (requireB r → w = .b) ∧ (requireC r → w = .c) ∧ (requireOmission r → w ≠ .possible)) := by
  have hb : (1 : Fin 3) ≠ 0 := by decide
  have hc : (2 : Fin 3) ≠ 0 := by decide
  constructor
  · rintro ⟨t, ht, hrows⟩
    obtain ⟨p, hp, hw⟩ := exists_pure_observer_witness t ht
    refine ⟨p, hp, fun r => ?_⟩
    have h := hw (rows r)
    refine ⟨fun e => h.1 ?_, fun e => h.2.1 ?_, fun e => h.2.2 ?_⟩
    · rw [(WinnerSet.view_eq_other_iff 0 _ ⟨1, hb⟩).mpr ((hrows r).1 e)]
      rfl
    · rw [(WinnerSet.view_eq_other_iff 0 _ ⟨2, hc⟩).mpr ((hrows r).2.1 e)]
      rfl
    · intro mark
      apply (hrows r).2.2 e
      apply (WinnerSet.view_eq_possible_iff _ _).mp
      apply Value.viewEquiv.symm.injective
      exact mark
  · rintro ⟨p, _, hrows⟩
    refine ⟨fromObserver p, fromObserver_isCore p, fun r => ?_⟩
    have h := view_eval_fromObserver p (rows r)
    refine ⟨fun e => ?_, fun e => ?_, fun e mark => ?_⟩
    · apply (WinnerSet.view_eq_other_iff 0 _ ⟨1, hb⟩).mp
      rw [h, (hrows r).1 e]
      rfl
    · apply (WinnerSet.view_eq_other_iff 0 _ ⟨2, hc⟩).mp
      rw [h, (hrows r).2.1 e]
      rfl
    · apply (hrows r).2.2 e
      apply Value.viewEquiv.injective
      exact h.symm.trans ((WinnerSet.view_eq_possible_iff _ _).mpr mark)

end KFOL.Bichain

namespace KFOL.Bichain.Quantified

open PlayerView WinnerSet

/-- The core row instance corresponding to the checked quantified cube game. -/
noncomputable def coreRows (F : Formula) (α : ℕ → Bool) :
    ({z // z ∈ allRows F} ⊕ Bool) → Lab → WinnerSet (Fin 3)
  | .inl z, j => representative (Function.Embedding.refl _) 0 (rows F z.val j).toView
  | .inr false, j => representative (Function.Embedding.refl _) 0
      (Value.ofBool (!inJ F (.relay 0) j)).toView
  | .inr true, j => representative (Function.Embedding.refl _) 0
      (Value.ofBool (inI F (.br 0 (α 0)) j)).toView

/-- Quantified truth is equivalent to interpolation by a core term. -/
theorem sat_iff_core_interpolation (F : Formula) (hwf : F.WF) (α : ℕ → Bool) :
    sat F F.n 0 α ↔ ∃ t : KFOL.Term (Fin 3) Lab, t.IsCore ∧
      t.eval (coreRows F α (.inr false)) = singleton 1 ∧
      t.eval (coreRows F α (.inr true)) = singleton 2 ∧
      ∀ z : {z // z ∈ allRows F}, 0 ∉ (t.eval (coreRows F α (.inl z))).val := by
  rw [sat_iff_separator F hwf α]
  have h := observer_interpolation_iff (coreRows F α)
    (· = .inr false) (· = .inr true) (fun r => ∃ z, r = .inl z)
  refine Iff.trans (?_ : _ ↔ _) (h.symm.trans ?_)
  · simp only [cell, CubeQuery.Holds]
    apply exists_congr
    intro p
    constructor
    · rintro ⟨hp, hm, hc, hb⟩
      refine ⟨hp, fun r => ⟨?_, ?_, ?_⟩⟩
      · rintro rfl
        simpa [coreRows, view_representative] using hb
      · rintro rfl
        simpa [coreRows, view_representative] using hc
      · rintro ⟨z, rfl⟩
        simpa [coreRows, view_representative] using hm z.val z.property
    · rintro ⟨hp, h⟩
      refine ⟨hp, fun z hz => ?_, ?_, ?_⟩
      · simpa [coreRows, view_representative] using (h (.inl ⟨z, hz⟩)).2.2 ⟨⟨z, hz⟩, rfl⟩
      · simpa [coreRows, view_representative] using (h (.inr true)).2.1 rfl
      · simpa [coreRows, view_representative] using (h (.inr false)).1 rfl
  · apply exists_congr
    intro t
    constructor
    · rintro ⟨ht, htRows⟩
      exact ⟨ht, (htRows _).1 rfl, (htRows _).2.1 rfl, fun z => (htRows _).2.2 ⟨z, rfl⟩⟩
    · rintro ⟨ht, hb, hc, hm⟩
      refine ⟨ht, fun r => ⟨?_, ?_, ?_⟩⟩
      · rintro rfl
        exact hb
      · rintro rfl
        exact hc
      · rintro ⟨z, rfl⟩
        exact hm z

end KFOL.Bichain.Quantified

namespace KFOL.Bichain.Quantified

open WinnerSet

private theorem coreRows_restrict (F : Formula) (wf : F.WF) (α : ℕ → Bool)
    (r : {z // z ∈ allRows F} ⊕ Bool) (j : Lab) :
    coreRows F α r (j.restrict F).val = coreRows F α r j := by
  rcases r with ⟨z, hz⟩ | b
  · simp only [coreRows, Lab.restrict, rows_limit F wf hz]
  · cases b
    · simp only [coreRows, Lab.restrict, inJ_limit F (show (Vtx.relay 0).InInstance F from Nat.zero_le _) j]
    · simp only [coreRows, Lab.restrict, inI_limit F wf
        (show (Vtx.br 0 (α 0)).InInstance F from Nat.zero_le _) j]

private theorem eval_relabel_core {X Y : Type*} (t : KFOL.Term (Fin 3) X)
    (ht : t.IsCore) (f : X → Y) :
    (t.subst (fun j => .var (f j))).IsCore := by
  induction t with
  | winner r => cases ht
  | rename p t ih => cases ht
  | var j => trivial
  | choice r x y hx hy => exact ⟨hx ht.1, hy ht.2⟩

/-- The core interpolation equivalence uses only finitely many coordinates. -/
theorem sat_iff_finite_core_interpolation (F : Formula) (hwf : F.WF) (α : ℕ → Bool) :
    sat F F.n 0 α ↔ ∃ t : KFOL.Term (Fin 3) (FiniteLab F), t.IsCore ∧
      t.eval (fun j => coreRows F α (.inr false) j.val) = singleton 1 ∧
      t.eval (fun j => coreRows F α (.inr true) j.val) = singleton 2 ∧
      ∀ z : {z // z ∈ allRows F},
        0 ∉ (t.eval (fun j => coreRows F α (.inl z) j.val)).val := by
  rw [sat_iff_core_interpolation F hwf α]
  constructor
  · rintro ⟨t, ht, hb, hc, hm⟩
    refine ⟨t.subst (fun j => .var (j.restrict F)), eval_relabel_core t ht (Lab.restrict F), ?_, ?_, ?_⟩
    · simpa only [KFOL.Term.eval_subst, KFOL.Term.eval, coreRows_restrict F hwf] using hb
    · simpa only [KFOL.Term.eval_subst, KFOL.Term.eval, coreRows_restrict F hwf] using hc
    · intro z
      simpa only [KFOL.Term.eval_subst, KFOL.Term.eval, coreRows_restrict F hwf] using hm z
  · rintro ⟨t, ht, hb, hc, hm⟩
    refine ⟨t.subst (fun j => .var j.val), eval_relabel_core t ht Subtype.val, ?_, ?_, ?_⟩
    · simpa only [KFOL.Term.eval_subst, KFOL.Term.eval] using hb
    · simpa only [KFOL.Term.eval_subst, KFOL.Term.eval] using hc
    · intro z
      simpa only [KFOL.Term.eval_subst, KFOL.Term.eval] using hm z

end KFOL.Bichain.Quantified
