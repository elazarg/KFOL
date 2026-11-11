module

public import KFOL.Definitions.CoreFunctions
public import KFOL.Algorithms.FiniteHorn
public import KFOL.Algebra.Monotone
public import KFOL.Algebra.ChoiceSupport
public import KFOL.Algebra.TestDomains
public import KFOL.Algebra.Idempotent

/-! # Recognition and synthesis by atomic cuts

Each reachable fact has a single core term as its witness, satisfying the
bound at every row. A finite union assembles these witnesses into the maximum
bounded value. Completeness follows by cutting a root at its absorbing atoms.
-/

@[expose] public section

namespace KFOL.Core.Cuts

universe u v w
variable {Role : Type u} {Row : Type v} {Var : Type w}

private theorem atomStep_iff (owner a b c : Role) :
    AtomStep owner a b c ↔
      c ∈ (WinnerSet.choice owner (WinnerSet.singleton a) (WinnerSet.singleton b)).val := by
  classical
  by_cases h : a = owner ∨ b = owner
  · rcases h with ha | hb
    · simp [AtomStep, WinnerSet.choice, ha]
    · simp [AtomStep, WinnerSet.choice, hb]
  · simp [AtomStep, WinnerSet.choice, (not_or.mp h).1, (not_or.mp h).2, or_comm]

private theorem exists_atomStep (owner : Role) (A B : WinnerSet Role) (c : Role)
    (hc : c ∈ (WinnerSet.choice owner A B).val) :
    ∃ a ∈ A.val, ∃ b ∈ B.val, AtomStep owner a b c := by
  classical
  by_cases h : A = WinnerSet.singleton owner ∨ B = WinnerSet.singleton owner
  · have he : c = owner := by simpa [WinnerSet.choice, h] using hc
    subst c
    rcases h with ha | hb
    · obtain ⟨b, hb⟩ := B.property
      exact ⟨owner, by simp [ha], b, hb, Or.inl ⟨Or.inl rfl, rfl⟩⟩
    · obtain ⟨a, ha⟩ := A.property
      exact ⟨a, ha, owner, by simp [hb], Or.inl ⟨Or.inr rfl, rfl⟩⟩
  · have hm : c ∈ A.val ∨ c ∈ B.val := by simpa [WinnerSet.choice, h] using hc
    rcases hm with ha | hb
    · by_cases he : c = owner
      · obtain ⟨b, hb⟩ := B.property
        exact ⟨c, ha, b, hb, Or.inl ⟨Or.inl he, he⟩⟩
      · obtain ⟨b, hb, hbr⟩ := WinnerSet.exists_mem_ne_of_ne_singleton owner B (not_or.mp h).2
        exact ⟨c, ha, b, hb, Or.inr ⟨he, hbr, Or.inl rfl⟩⟩
    · by_cases he : c = owner
      · obtain ⟨a, ha⟩ := A.property
        exact ⟨a, ha, c, hb, Or.inl ⟨Or.inr he, he⟩⟩
      · obtain ⟨a, ha, har⟩ := WinnerSet.exists_mem_ne_of_ne_singleton owner A (not_or.mp h).1
        exact ⟨a, ha, c, hb, Or.inr ⟨har, he, Or.inr rfl⟩⟩

private theorem cut_sound (U : Row → WinnerSet Role) (owner : Role)
    (B L R : State Role Row) (hcut : Cut U owner B L R)
    (s t : Row → WinnerSet Role)
    (hs : ∀ i, (s i).val ⊆ region U L i) (ht : ∀ i, (t i).val ⊆ region U R i) :
    ∀ i, (WinnerSet.choice owner (s i) (t i)).val ⊆ region U B i := by
  classical
  intro i
  rcases hcut i with ⟨hl, hr⟩ | ⟨hm, hl, _⟩ | ⟨hm, _, hr⟩
  · apply (WinnerSet.choice_subset_union owner _ _).trans
    apply Set.union_subset
    · simpa only [region, hl] using hs i
    · simpa only [region, hr] using ht i
  · have he : s i = WinnerSet.singleton owner :=
      WinnerSet.eq_singleton_of_subset _ _ (by simpa only [region, hl] using hs i)
    have hc : WinnerSet.choice owner (s i) (t i) = WinnerSet.singleton owner := by
      simp [WinnerSet.choice, he]
    rw [hc]
    exact Set.singleton_subset_iff.mpr hm
  · have he : t i = WinnerSet.singleton owner :=
      WinnerSet.eq_singleton_of_subset _ _ (by simpa only [region, hr] using ht i)
    have hc : WinnerSet.choice owner (s i) (t i) = WinnerSet.singleton owner := by
      simp [WinnerSet.choice, he]
    rw [hc]
    exact Set.singleton_subset_iff.mpr hm

/-- A reachable fact has one witness valid simultaneously at all rows. -/
theorem derives_sound (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role)
    {f : Fact Role Row} (hf : FiniteHorn.Derives (system values U) f) :
    ∃ t : Term Role Var, t.IsCore ∧
      (∀ i, (t.eval (values i)).val ⊆ region U f.bounds i) ∧
      f.winner ∈ (t.eval (values f.row)).val := by
  induction hf with
  | seed hs =>
    obtain ⟨x, hx, hm⟩ := hs
    exact ⟨.var x, trivial, hx, hm⟩
  | @step p q f hr _ _ hp hq =>
    obtain ⟨s, hs, hbS, hmS⟩ := hp
    obtain ⟨t, ht, hbT, hmT⟩ := hq
    obtain ⟨hpr, hqr, owner, hcut, hstep⟩ := hr
    refine ⟨.choice owner s t, ⟨hs, ht⟩,
      cut_sound U owner _ _ _ hcut _ _ hbS hbT, ?_⟩
    have hl : (WinnerSet.singleton p.winner).val ⊆ (s.eval (values f.row)).val :=
      Set.singleton_subset_iff.mpr (hpr ▸ hmS)
    have hr : (WinnerSet.singleton q.winner).val ⊆ (t.eval (values f.row)).val :=
      Set.singleton_subset_iff.mpr (hqr ▸ hmT)
    exact (WinnerSet.choice_mono owner hl hr) ((atomStep_iff _ _ _ _).mp hstep)

private theorem root_cut (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role)
    (owner : Role) (s t : Term Role Var) (B : State Role Row)
    (hb : ∀ i, ((Term.choice owner s t).eval (values i)).val ⊆ region U B i) :
    ∃ L R : State Role Row, Cut U owner B L R ∧
      (∀ i, (s.eval (values i)).val ⊆ region U L i) ∧
      (∀ i, (t.eval (values i)).val ⊆ region U R i) := by
  classical
  let L : State Role Row := fun i =>
    if s.eval (values i) = WinnerSet.singleton owner then .atom owner
    else if t.eval (values i) = WinnerSet.singleton owner then .top else B i
  let R : State Role Row := fun i =>
    if s.eval (values i) = WinnerSet.singleton owner then .top
    else if t.eval (values i) = WinnerSet.singleton owner then .atom owner else B i
  refine ⟨L, R, ?_, ?_, ?_⟩
  · intro i
    by_cases hs : s.eval (values i) = WinnerSet.singleton owner
    · right; left
      refine ⟨?_, by simp [L, hs], by simp [R, hs]⟩
      exact hb i (by simp [Term.eval, WinnerSet.choice, hs])
    · by_cases ht : t.eval (values i) = WinnerSet.singleton owner
      · right; right
        refine ⟨?_, by simp [L, hs, ht], by simp [R, hs, ht]⟩
        exact hb i (by simp [Term.eval, WinnerSet.choice, ht])
      · left; exact ⟨by simp [L, hs, ht], by simp [R, hs, ht]⟩
  · intro i
    by_cases hs : s.eval (values i) = WinnerSet.singleton owner
    · simp [region, L, hs]
    · by_cases ht : t.eval (values i) = WinnerSet.singleton owner
      · simp [region, L, hs, ht]
      · have h := hb i
        simp only [Term.eval, WinnerSet.choice, hs, ht, or_self, ite_false,
          WinnerSet.val_union] at h
        simpa only [region, L, ite_eq_right hs, ite_eq_right ht] using
          Set.Subset.trans Set.subset_union_left h
  · intro i
    by_cases hs : s.eval (values i) = WinnerSet.singleton owner
    · simp [region, R, hs]
    · by_cases ht : t.eval (values i) = WinnerSet.singleton owner
      · simp [region, R, hs, ht]
      · have h := hb i
        simp only [Term.eval, WinnerSet.choice, hs, ht, or_self, ite_false,
          WinnerSet.val_union] at h
        simpa only [region, R, ite_eq_right hs, ite_eq_right ht] using
          Set.Subset.trans Set.subset_union_right h

/-- Every membership of every bounded core term is derivable by atomic cuts. -/
theorem derives_complete (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role)
    (t : Term Role Var) (ht : t.IsCore) (B : State Role Row)
    (hb : ∀ i, (t.eval (values i)).val ⊆ region U B i) (i : Row) (r : Role)
    (hr : r ∈ (t.eval (values i)).val) :
    FiniteHorn.Derives (system values U) ⟨B, i, r⟩ := by
  induction t generalizing B r with
  | winner => exact False.elim ht
  | rename => exact False.elim ht
  | var x => exact .seed ⟨x, hb, hr⟩
  | choice owner s t ihs iht =>
    obtain ⟨L, R, hcut, hs, ht'⟩ := root_cut values U owner s t B hb
    obtain ⟨a, ha, b, hb', hstep⟩ := exists_atomStep owner _ _ r hr
    exact FiniteHorn.Derives.step (a := ⟨L, i, a⟩) (b := ⟨R, i, b⟩)
      ⟨rfl, rfl, owner, hcut, hstep⟩
      (ihs ht.1 L hs a ha) (iht ht.2 R ht' b hb')

private theorem unionList_core (three : Fin 3 ↪ Role) (base : Term Role Var)
    (terms : List (Term Role Var)) (hb : base.IsCore) (ht : ∀ t ∈ terms, t.IsCore) :
    (terms.foldr (Term.unionTerm three) base).IsCore := by
  induction terms with
  | nil => exact hb
  | cons t ts ih =>
    have htc := ht t (List.mem_cons_self)
    have hrest := ih (fun s hs => ht s (List.mem_cons_of_mem _ hs))
    exact ⟨⟨htc, hrest⟩, ⟨htc, hrest⟩⟩

private theorem unionList_subset (three : Fin 3 ↪ Role) (base : Term Role Var)
    (terms : List (Term Role Var)) (values : Row → Var → WinnerSet Role)
    (U : Row → WinnerSet Role) (B : State Role Row)
    (hb : ∀ i, (base.eval (values i)).val ⊆ region U B i)
    (ht : ∀ t ∈ terms, ∀ i, (t.eval (values i)).val ⊆ region U B i) :
    ∀ i, ((terms.foldr (Term.unionTerm three) base).eval (values i)).val ⊆ region U B i := by
  induction terms with
  | nil => exact hb
  | cons t ts ih =>
    intro i
    rw [List.foldr_cons, Term.eval_unionTerm]
    exact Set.union_subset (ht t (List.mem_cons_self) i)
      (ih (fun s hs => ht s (List.mem_cons_of_mem _ hs)) i)

private theorem unionList_mem (three : Fin 3 ↪ Role) (base : Term Role Var)
    (terms : List (Term Role Var)) (v : Var → WinnerSet Role)
    (t : Term Role Var) (ht : t ∈ terms) :
    (t.eval v).val ⊆ ((terms.foldr (Term.unionTerm three) base).eval v).val := by
  induction terms with
  | nil => simp at ht
  | cons s ts ih =>
    rw [List.foldr_cons, Term.eval_unionTerm]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Set.subset_union_left
    · exact (ih ht).trans Set.subset_union_right

/-- All reachable memberships at a bound can be assembled into one term.
This term is the maximum of all term values satisfying that bound. -/
theorem maximum_of_reachable [Fintype Role] [Fintype Row]
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role)
    (U : Row → WinnerSet Role) (B : State Role Row)
    (h : ∃ i r, FiniteHorn.Derives (system values U) ⟨B, i, r⟩) :
    ∃ t : Term Role Var, t.IsCore ∧
      (∀ i, (t.eval (values i)).val ⊆ region U B i) ∧
      ∀ i r, r ∈ (t.eval (values i)).val ↔
        FiniteHorn.Derives (system values U) ⟨B, i, r⟩ := by
  classical
  let J := {p : Row × Role // FiniteHorn.Derives (system values U) ⟨B, p.1, p.2⟩}
  obtain ⟨i₀, r₀, h₀⟩ := h
  let j₀ : J := ⟨(i₀, r₀), h₀⟩
  have witnesses (j : J) := derives_sound values U j.property
  choose term core bound member using witnesses
  let terms := Finset.univ.toList.map term
  let t := terms.foldr (Term.unionTerm three) (term j₀)
  have hcore : t.IsCore := unionList_core three _ _ (core j₀) (by
    intro s hs
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
    exact core j)
  have hbound : ∀ i, (t.eval (values i)).val ⊆ region U B i :=
    unionList_subset three _ _ values U B (bound j₀) (by
      intro s hs
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
      exact bound j)
  refine ⟨t, hcore, hbound, ?_⟩
  intro i r
  constructor
  · exact derives_complete values U t hcore B hbound i r
  · intro hr
    let j : J := ⟨(i, r), hr⟩
    have hm : term j ∈ terms := List.mem_map.mpr ⟨j, by simp, rfl⟩
    exact unionList_mem three _ terms (values i) (term j) hm (member j)

/-- The saturated memberships at a bound have one common witness term. -/
theorem maximum_of_saturated [Fintype Role] [Fintype Row]
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role)
    (U : Row → WinnerSet Role) (B : State Role Row)
    (h : ∃ i r, (⟨B, i, r⟩ : Fact Role Row) ∈ FiniteHorn.saturate (system values U)) :
    ∃ t : Term Role Var, t.IsCore ∧
      (∀ i, (t.eval (values i)).val ⊆ region U B i) ∧
      ∀ i r, r ∈ (t.eval (values i)).val ↔
        (⟨B, i, r⟩ : Fact Role Row) ∈ FiniteHorn.saturate (system values U) := by
  obtain ⟨i, r, hr⟩ := h
  obtain ⟨t, ht, hb, he⟩ := maximum_of_reachable three values U B
    ⟨i, r, (FiniteHorn.mem_saturate_iff _ _).mp hr⟩
  exact ⟨t, ht, hb, fun i r => (he i r).trans (FiniteHorn.mem_saturate_iff _ _).symm⟩

/-- Exact recognition and simultaneous synthesis for a finite nonempty
family of sampled valuations. No agreement is asserted outside those rows. -/
theorem recognizes_iff [Fintype Role] [Fintype Row] [Nonempty Row]
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role)
    (U : Row → WinnerSet Role) :
    Recognizes values U ↔
      ∃ t : Term Role Var, t.IsCore ∧ ∀ i, t.eval (values i) = U i := by
  classical
  constructor
  · intro h
    let B : State Role Row := fun _ => .target
    let i₀ : Row := Classical.choice inferInstance
    obtain ⟨r₀, hr₀⟩ := (U i₀).property
    have h₀ : FiniteHorn.Derives (system values U) ⟨B, i₀, r₀⟩ :=
      (FiniteHorn.mem_saturate_iff _ _).mp (h i₀ r₀ hr₀)
    obtain ⟨t, ht, hb, he⟩ := maximum_of_reachable three values U B ⟨i₀, r₀, h₀⟩
    refine ⟨t, ht, ?_⟩
    intro i
    apply Subtype.ext
    apply Set.Subset.antisymm (hb i)
    intro r hr
    exact (he i r).mpr ((FiniteHorn.mem_saturate_iff _ _).mp (h i r hr))
  · rintro ⟨t, ht, he⟩ i r hr
    apply (FiniteHorn.mem_saturate_iff _ _).mpr
    apply derives_complete values U t ht (fun _ => .target)
    · intro j; simp only [he j, region]; exact Set.Subset.rfl
    · simpa only [he i] using hr

/-- The finite cut test characterizes entire term operations at every finite
input arity, including arity zero. -/
theorem operation_iff [Fintype Role] [Fintype Var] (three : Fin 3 ↪ Role)
    (f : (Var → WinnerSet Role) → WinnerSet Role) :
    CutRecognizes f ↔
      ∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v := by
  classical
  let _ := Fintype.ofFinite (WinnerSet Role)
  let _ : Nonempty (Var → WinnerSet Role) := ⟨fun _ => WinnerSet.singleton (three 0)⟩
  exact recognizes_iff three (fun v x => v x) f

/-- The number of possible Horn facts is the stated uniform round bound. -/
theorem fact_card [Fintype Role] [Fintype Row] :
    Fintype.card (Fact Role Row) =
      Fintype.card Role * Fintype.card Row * (Fintype.card Role + 2) ^ Fintype.card Row := by
  classical
  let e : Bound Role ≃ Option (Option Role) :=
    { toFun := fun b => match b with
        | .target => none
        | .top => some none
        | .atom r => some (some r)
      invFun := fun b => match b with
        | none => .target
        | some none => .top
        | some (some r) => .atom r
      left_inv := by intro b; cases b <;> rfl
      right_inv := by intro b; rcases b with _ | (_ | r) <;> rfl }
  have hb : Fintype.card (Bound Role) = Fintype.card Role + 2 := by
    simpa [Nat.add_assoc] using Fintype.card_congr e
  calc
    Fintype.card (Fact Role Row) = (Fintype.card (Bound Role)) ^ Fintype.card Row *
        (Fintype.card Row * Fintype.card Role) := by
      rw [Fintype.card_congr Fact.equivProd]
      simp only [Fintype.card_prod, Fintype.card_fun]
    _ = _ := by rw [hb]; ac_rfl

/-- The explicit number of rounds already reaches a fixed point. -/
theorem round_bound [Fintype Role] [Fintype Row]
    (values : Row → Var → WinnerSet Role) (U : Row → WinnerSet Role) :
    let N := Fintype.card Role * Fintype.card Row *
      (Fintype.card Role + 2) ^ Fintype.card Row
    FiniteHorn.step (system values U) (FiniteHorn.stage (system values U) N) =
      FiniteHorn.stage (system values U) N := by
  simpa only [FiniteHorn.saturate, fact_card] using FiniteHorn.saturate_fixed (system values U)

end KFOL.Core.Cuts
