module

public import KFOL.Core.ProfileBudgets.Pruning

/-! # Removing inputs compulsory in every pruning at one owner -/

@[expose] public section
namespace KFOL.Core.CompulsoryPruning

open ProfileBudgets
variable {Role V : Type*} [DecidableEq Role] [DecidableEq V]

/-- All finite sets of input names obtained by pruning at the owner `r`. -/
def Supports (r : Role) : CoreTerm Role V → Set (Finset V)
  | .var x => {{x}}
  | .func (.choice q) a =>
    if q = r then {H | ∃ S ∈ Supports r (a 0), ∃ T ∈ Supports r (a 1), S ∪ T = H}
    else Supports r (a 0) ∪ Supports r (a 1)

@[simp] theorem supports_var (r : Role) (x : V) (H : Finset V) :
    H ∈ Supports r (.var x) ↔ H = {x} := Iff.rfl

theorem owned {r : Role} {s t : CoreTerm Role V} {H : Finset V} :
    H ∈ Supports r (choiceTerm r s t) ↔
      ∃ S ∈ Supports r s, ∃ T ∈ Supports r t, S ∪ T = H := by simp [Supports, choiceTerm]

theorem foreign {r q : Role} (ne : q ≠ r) {s t : CoreTerm Role V} {H : Finset V} :
    H ∈ Supports r (choiceTerm q s t) ↔ H ∈ Supports r s ∨ H ∈ Supports r t := by
  simp [Supports, choiceTerm, ne]

omit [DecidableEq Role] in
private theorem vars_choice (q : Role) (x y : CoreTerm Role V) :
    (choiceTerm q x y).varFinset = x.varFinset ∪ y.varFinset := by
  simp [choiceTerm, FirstOrder.Language.Term.varFinset, Finset.univ_fin2]

theorem supports_iff_prunes (r : Role) (t : CoreTerm Role V) (H : Finset V) :
    H ∈ Supports r t ↔ ∃ s, Prunes r t s ∧ s.varFinset = H := by
  constructor
  · induction t using induction_choice generalizing H with
    | var x => rintro (rfl : H = {x}); exact ⟨_, .var x, rfl⟩
    | choice q x y hx hy =>
      by_cases qr : q = r
      · subst q
        rintro h
        obtain ⟨A, ha, B, hb, rfl⟩ := owned.mp h
        obtain ⟨x', px, rfl⟩ := hx A ha
        obtain ⟨y', py, rfl⟩ := hy B hb
        exact ⟨_, .owned px py, vars_choice _ _ _⟩
      · intro h
        rcases (foreign qr).mp h with h | h
        · obtain ⟨x', px, e⟩ := hx H h
          exact ⟨_, .left qr px, e⟩
        · obtain ⟨y', py, e⟩ := hy H h
          exact ⟨_, .right qr py, e⟩
  · rintro ⟨s, p, rfl⟩
    induction p with
    | var => rfl
    | owned _ _ hx hy => exact owned.mpr ⟨_, hx, _, hy, (vars_choice _ _ _).symm⟩
    | left ne _ h => exact (foreign ne).mpr (Or.inl h)
    | right ne _ h => exact (foreign ne).mpr (Or.inr h)

theorem support_nonempty (r : Role) (t : CoreTerm Role V) {H : Finset V} (hs : H ∈ Supports r t) :
    H.Nonempty := by
  induction t using induction_choice generalizing H with
  | var x => obtain rfl := (supports_var r x H).mp hs; exact Finset.singleton_nonempty _
  | choice q x y hx hy =>
    by_cases eq : q = r
    · subst q
      obtain ⟨A, ha, B, _, rfl⟩ := owned.mp hs
      exact (hx ha).mono Finset.subset_union_left
    · exact ((foreign eq).mp hs).elim hx hy

/-- A name forced in every r-pruning is the only leaf name of some
q-pruning, for each different owner q. -/
theorem foreign_singleton (r q : Role) (ne : q ≠ r) (t : CoreTerm Role V) (c : V)
    (forced : ∀ H ∈ Supports r t, c ∈ H) : {c} ∈ Supports q t := by
  classical
  induction t using induction_choice with
  | var x =>
    obtain rfl : c = x := Finset.mem_singleton.mp (forced {x} rfl)
    rfl
  | choice s x y hx hy =>
    by_cases sr : s = r
    · subst s
      apply (foreign ne.symm).mpr
      by_cases h : ∀ H ∈ Supports r x, c ∈ H
      · exact Or.inl (hx h)
      · push Not at h
        obtain ⟨A, ha, miss⟩ := h
        exact Or.inr (hy (fun B hb => (Finset.mem_union.mp
          (forced _ (owned.mpr ⟨A, ha, B, hb, rfl⟩))).resolve_left miss))
    · have lx := hx (fun H hs => forced H ((foreign sr).mpr (Or.inl hs)))
      have ly := hy (fun H hs => forced H ((foreign sr).mpr (Or.inr hs)))
      by_cases sq : s = q
      · subst s
        exact owned.mpr ⟨_, lx, _, ly, Finset.union_self _⟩
      · exact (foreign sq).mpr (Or.inl lx)

/-- A residual term on the surviving variables. At the distinguished owner
the support lifts after adding erased inputs. At other owners it lifts verbatim. -/
structure Residual (r : Role) (C : Finset V) (t u : CoreTerm Role V) : Prop where
  vars : u.varFinset ⊆ t.varFinset \ C
  own : ∀ H ∈ Supports r u, ∃ A ∈ Supports r t, A \ C = H
  other : ∀ q, q ≠ r → Supports q u ⊆ Supports q t

private theorem Residual.choice {r : Role} {C : Finset V} {x y u v : CoreTerm Role V}
    (s : Role) (l : Residual r C x u) (h : Residual r C y v) :
    Residual r C (choiceTerm s x y) (choiceTerm s u v) where
  vars := by
    rw [vars_choice, vars_choice]
    intro i hi
    rcases Finset.mem_union.mp hi with hu | hv
    · obtain ⟨hx, hc⟩ := Finset.mem_sdiff.mp (l.vars hu)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hx, hc⟩
    · obtain ⟨hy, hc⟩ := Finset.mem_sdiff.mp (h.vars hv)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hy, hc⟩
  own := by
    intro H hH
    by_cases sr : s = r
    · subst s
      obtain ⟨U, hu, W, hw, rfl⟩ := owned.mp hH
      obtain ⟨A, ha, rfl⟩ := l.own U hu
      obtain ⟨B, hb, rfl⟩ := h.own W hw
      exact ⟨A ∪ B, owned.mpr ⟨_, ha, _, hb, rfl⟩, Finset.union_sdiff_distrib _ _ _⟩
    · rcases (foreign sr).mp hH with hu | hv
      · obtain ⟨A, ha, e⟩ := l.own H hu
        exact ⟨A, (foreign sr).mpr (Or.inl ha), e⟩
      · obtain ⟨B, hb, e⟩ := h.own H hv
        exact ⟨B, (foreign sr).mpr (Or.inr hb), e⟩
  other := by
    intro q qr H hH
    by_cases sq : s = q
    · subst s
      obtain ⟨U, hu, W, hw, rfl⟩ := owned.mp hH
      exact owned.mpr ⟨U, l.other q qr hu, W, h.other q qr hw, rfl⟩
    · exact (foreign sq).mpr (((foreign sq).mp hH).imp (fun hu => l.other q qr hu) (fun hv => h.other q qr hv))

private theorem Residual.skip_right {r : Role} {C : Finset V} {x u y : CoreTerm Role V}
    (l : Residual r C x u) {B : Finset V} (hy : B ∈ Supports r y) (sub : B ⊆ C) :
    Residual r C (choiceTerm r x y) u where
  vars := by
    rw [vars_choice]
    intro i hi
    obtain ⟨hx, hc⟩ := Finset.mem_sdiff.mp (l.vars hi)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hx, hc⟩
  own := by
    intro H hu
    obtain ⟨A, ha, rfl⟩ := l.own H hu
    exact ⟨A ∪ B, owned.mpr ⟨_, ha, _, hy, rfl⟩, by
      rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr sub, Finset.union_empty]⟩
  other q qr _ hu := (foreign (Ne.symm qr)).mpr (Or.inl (l.other q qr hu))

private theorem Residual.skip_left {r : Role} {C : Finset V} {x y v : CoreTerm Role V}
    {A : Finset V} (hx : A ∈ Supports r x) (sub : A ⊆ C) (h : Residual r C y v) :
    Residual r C (choiceTerm r x y) v where
  vars := by
    rw [vars_choice]
    intro i hi
    obtain ⟨hy, hc⟩ := Finset.mem_sdiff.mp (h.vars hi)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hy, hc⟩
  own := by
    intro H hv
    obtain ⟨B, hb, rfl⟩ := h.own H hv
    exact ⟨A ∪ B, owned.mpr ⟨_, hx, _, hb, rfl⟩, by
      rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_empty_iff_subset.mpr sub, Finset.empty_union]⟩
  other q qr _ hv := (foreign (Ne.symm qr)).mpr (Or.inr (h.other q qr hv))

/-- Treat erased inputs as the identity at r and as an absorber at every
foreign gate. Either a whole r-pruning was erased or a residual word survives. -/
theorem erase (r : Role) (C : Finset V) (t : CoreTerm Role V) :
    (∃ H ∈ Supports r t, H ⊆ C) ∨ ∃ u, Residual r C t u := by
  induction t using induction_choice with
  | var i =>
    by_cases hi : i ∈ C
    · exact Or.inl ⟨{i}, rfl, Finset.singleton_subset_iff.mpr hi⟩
    · right
      refine ⟨.var i, ?_, ?_, ?_⟩
      · intro x hx
        obtain rfl : x = i := Finset.mem_singleton.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_singleton_self _, hi⟩
      · intro H hH
        obtain rfl := (supports_var _ _ _).mp hH
        exact ⟨{i}, rfl, by simp [hi]⟩
      · exact fun _ _ => Set.Subset.rfl
  | choice s x y hx hy =>
    rcases hx with ⟨A, ha, ac⟩ | ⟨u, l⟩ <;> rcases hy with ⟨B, hb, bc⟩ | ⟨v, h⟩
    · left
      by_cases sr : s = r
      · subst s
        exact ⟨_, owned.mpr ⟨A, ha, B, hb, rfl⟩, Finset.union_subset ac bc⟩
      · exact ⟨A, (foreign sr).mpr (Or.inl ha), ac⟩
    · by_cases sr : s = r
      · subst s
        exact Or.inr ⟨v, h.skip_left ha ac⟩
      · exact Or.inl ⟨A, (foreign sr).mpr (Or.inl ha), ac⟩
    · by_cases sr : s = r
      · subst s
        exact Or.inr ⟨u, l.skip_right hb bc⟩
      · exact Or.inl ⟨B, (foreign sr).mpr (Or.inr hb), bc⟩
    · exact Or.inr ⟨_, l.choice s h⟩

private theorem exists_fold (r : Role) (C : Finset V) (cn : C.Nonempty) :
    ∃ t : CoreTerm Role V, t.varFinset = C ∧ (∀ H ∈ Supports r t, H = C) ∧
      ∀ q, q ≠ r → ∀ H ∈ Supports q t, ∃ c ∈ C, H = {c} := by
  classical
  induction C using Finset.induction with
  | empty => simp at cn
  | insert c C hc ih =>
    by_cases cn' : C.Nonempty
    · obtain ⟨t, vars, whole, leaf⟩ := ih cn'
      refine ⟨choiceTerm r (.var c) t, ?_, ?_, ?_⟩
      · rw [vars_choice, vars]
        simp [FirstOrder.Language.Term.varFinset]
      · intro H hh
        obtain ⟨A, ha, B, hb, rfl⟩ := owned.mp hh
        obtain rfl := (supports_var r c A).mp ha
        simp [whole B hb]
      · intro q qr H hh
        rcases (foreign (Ne.symm qr)).mp hh with ha | hb
        · exact ⟨c, Finset.mem_insert_self _ _, (supports_var q c H).mp ha⟩
        · obtain ⟨d, hd, eq⟩ := leaf q qr H hb
          exact ⟨d, Finset.mem_insert_of_mem hd, eq⟩
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp cn'
      refine ⟨.var c, rfl, fun _ hh => hh, fun q _ H hh => ?_⟩
      exact ⟨c, Finset.mem_singleton_self _, (supports_var q c H).mp hh⟩

/-- All prunings must belong to the family of their owner, and every
variable in the word must belong to the designated set of available inputs. -/
def FeasibleOn (W : Set V) (F : Role → Finset V → Prop) : Prop :=
  ∃ t : CoreTerm Role V, (t.varFinset : Set V) ⊆ W ∧ ∀ q H, H ∈ Supports q t → F q H

/-- Remove a nonempty set compulsory in every allowed nonempty r-support.
If it is itself allowed, its fold suffices. Otherwise the remaining word
uses only inputs outside it, and adds it back to each r-support. -/
theorem feasibleOn_iff (r : Role) (C : Finset V) (cn : C.Nonempty) (W : Set V)
    (available : (C : Set V) ⊆ W) (F : Role → Finset V → Prop)
    (compulsory : ∀ H, H.Nonempty → F r H → C ⊆ H) :
    FeasibleOn W F ↔
      (∀ c ∈ C, ∀ q, q ≠ r → F q {c}) ∧
        (F r C ∨ FeasibleOn (W \ (C : Set V))
          (fun q H => if q = r then F q (H ∪ C) else F q H)) := by
  constructor
  · rintro ⟨t, vars, safe⟩
    have forced (H : Finset V) (hs : H ∈ Supports r t) : C ⊆ H :=
      compulsory H (support_nonempty r t hs) (safe r H hs)
    refine ⟨fun c hc q qr => safe q {c} (foreign_singleton r q qr t c (fun H hs => forced H hs hc)), ?_⟩
    rcases erase r C t with ⟨H, hs, sub⟩ | ⟨u, residual⟩
    · exact Or.inl ((Finset.Subset.antisymm sub (forced H hs)) ▸ safe r H hs)
    · right
      refine ⟨u, ?_, ?_⟩
      · intro i hi
        obtain ⟨ht, miss⟩ := Finset.mem_sdiff.mp (residual.vars hi)
        exact ⟨vars ht, miss⟩
      · intro q H hs
        by_cases qr : q = r
        · subst q
          obtain ⟨A, ha, rfl⟩ := residual.own H hs
          simpa only [ite_true, Finset.sdiff_union_of_subset (forced A ha)] using safe r A ha
        · simpa only [ite_eq_right qr] using safe q H (residual.other q qr hs)
  · rintro ⟨singletons, h⟩
    obtain ⟨f, fv, whole, atLeaves⟩ := exists_fold r C cn
    rcases h with block | ⟨t, vars, safe⟩
    · refine ⟨f, fv ▸ available, ?_⟩
      intro q H hh
      by_cases qr : q = r
      · subst q
        exact (whole H hh) ▸ block
      · obtain ⟨c, hc, rfl⟩ := atLeaves q qr H hh
        exact singletons c hc q qr
    · refine ⟨choiceTerm r t f, ?_, ?_⟩
      · rw [vars_choice, fv, Finset.coe_union]
        exact Set.union_subset (fun i hi => (vars hi).1) available
      · intro q H hh
        by_cases qr : q = r
        · subst q
          obtain ⟨A, ha, B, hb, rfl⟩ := owned.mp hh
          rw [whole B hb]
          simpa only [ite_true] using safe r A ha
        · rcases (foreign (Ne.symm qr)).mp hh with ht | hf
          · simpa only [ite_eq_right qr] using safe q H ht
          · obtain ⟨c, hc, rfl⟩ := atLeaves q qr H hf
            exact singletons c hc q qr

end KFOL.Core.CompulsoryPruning
