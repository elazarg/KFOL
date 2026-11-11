module

public import KFOL.Core.OwnerElimination
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max

/-! # Completeness of owner-elimination certificates

Every finite relation closed under owned choice has a checked clause
presentation. Union closure gives separation by clauses with at most one
membership premise. The resulting finite-sample criterion is expressed only
through membership clauses and their finite owner-elimination checks.
-/

@[expose] public section

namespace KFOL.Core.OwnerElimination
open WinnerSet
universe u v
variable {Row : Type u} {Role : Type v}
variable [DecidableEq Row] [DecidableEq Role] [Fintype Role]

def CompleteFor (F : Finset (Clause Row Role)) (R : (Row → WinnerSet Role) → Prop) : Prop :=
  ∀ C, supports F C = true ↔ ∀ x, R x → C.Holds x

omit [DecidableEq Row] [DecidableEq Role] [Fintype Role] in
private theorem invalid_witness {R : (Row → WinnerSet Role) → Prop}
    {C : Clause Row Role} (h : ¬∀ x, R x → C.Holds x) :
    ∃ x, R x ∧ C.Premise x ∧ Absent C.head x := by
  classical
  simp only [Clause.Holds, Clause.Head] at h
  push Not at h
  obtain ⟨x, hx, hp, hn⟩ := h
  refine ⟨x, hx, hp, ?_⟩
  intro p hp hm
  exact hn p hp hm

private theorem block_absent_iff {x : Row → WinnerSet Role}
    {S : Finset (Atom Row Role)} {i : Row} {r : Role} :
    Absent (blockHead S i r) x ↔ Absent S x ∧ x i = singleton r := by
  constructor
  · intro h
    refine ⟨fun p hp => h p (Finset.mem_union_left _ hp), ?_⟩
    apply eq_singleton_of_subset
    intro k hk
    change k = r
    by_contra hkr
    exact h (i,k) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨k, by simp [hkr], rfl⟩)) hk
  · rintro ⟨hS, hi⟩
    exact absent_blockHead hS hi

private def Safe (C : Clause Row Role) (r : Role) (x : Row → WinnerSet Role) : Prop :=
  ∀ p, C.premise = some p → p.2 ≠ r → x p.1 ≠ singleton r

private theorem blocker_witness {R : (Row → WinnerSet Role) → Prop}
    {F : Finset (Clause Row Role)} (hcomplete : CompleteFor F R)
    (C : Clause Row Role) (r : Role) (S : Finset (Atom Row Role)) (i : Row)
    (hn : checkBlocker F C r S i ≠ true) :
    ∃ x, R x ∧ Absent S x ∧ x i = singleton r ∧ Safe C r x := by
  classical
  have witness (D : Clause Row Role) (hs : supports F D ≠ true) :
      ∃ x, R x ∧ D.Premise x ∧ Absent D.head x :=
    invalid_witness (fun h => hs ((hcomplete D).mpr h))
  cases hp : C.premise with
  | none =>
    have hh : supports F ⟨none, blockHead S i r⟩ ≠ true := by
      simpa [checkBlocker, hp] using hn
    obtain ⟨x, hx, _, hab⟩ := witness _ hh
    obtain ⟨hS, hi⟩ := block_absent_iff.mp hab
    exact ⟨x, hx, hS, hi, by simp [Safe, hp]⟩
  | some p =>
    by_cases hr : p.2 = r
    · have hh : supports F ⟨none, blockHead S i r⟩ ≠ true := by
        simpa [checkBlocker, hp, hr] using hn
      obtain ⟨x, hx, _, hab⟩ := witness _ hh
      obtain ⟨hS, hi⟩ := block_absent_iff.mp hab
      refine ⟨x, hx, hS, hi, ?_⟩
      intro q hq hqr
      have he : q = p := Option.some.inj (hq.symm.trans hp)
      exact (hqr (he ▸ hr)).elim
    · have hh : ¬∀ s ∈ Finset.univ.erase r,
          supports F ⟨some (p.1, s), blockHead S i r⟩ = true := by
        simpa [checkBlocker, hp, hr] using hn
      push Not at hh
      obtain ⟨s, hs, hbad⟩ := hh
      obtain ⟨x, hx, hpre, hab⟩ := witness _ hbad
      obtain ⟨hS, hi⟩ := block_absent_iff.mp hab
      refine ⟨x, hx, hS, hi, ?_⟩
      intro q hq _ he
      have hqp : q = p := Option.some.inj (hq.symm.trans hp)
      subst q
      have hm : s ∈ (x p.1).val := hpre
      have hsr : s = r := by simpa [he] using hm
      exact (Finset.mem_erase.mp hs).1 hsr

omit [DecidableEq Row] [DecidableEq Role] [Fintype Role] in
private theorem absent_choice {S : Finset (Atom Row Role)} {r : Role}
    {x y : Row → WinnerSet Role} (hx : Absent S x) (hy : Absent S y) :
    Absent S (fun i => choice r (x i) (y i)) := by
  intro p hp hm
  rcases choice_subset_union r _ _ hm with hm | hm
  · exact hx p hp hm
  · exact hy p hp hm

omit [DecidableEq Row] [Fintype Role] in
private theorem premise_choice {C : Clause Row Role} {r : Role}
    {x y : Row → WinnerSet Role} (hx : C.Premise x) (hy : Safe C r y) :
    C.Premise (fun i => choice r (x i) (y i)) := by
  classical
  cases hp : C.premise with
  | none => simp [Clause.Premise, hp]
  | some p =>
    simp only [Clause.Premise, hp] at hx ⊢
    have hm : p.2 ∈ (x p.1).val := by simpa [Clause.Premise, hp] using hx
    change p.2 ∈ (choice r (x p.1) (y p.1)).val
    by_cases hr : p.2 = r
    · rw [hr] at hm ⊢
      exact (mem_choice_owner r _ _).mpr (Or.inl hm)
    · apply (mem_choice_other r p.2 (Ne.symm hr) _ _).mpr
      refine ⟨Or.inl hm, ?_, hy p hp hr⟩
      intro he
      exact hr (by simpa [he] using hm)


private theorem combine_bad_blockers {R : (Row → WinnerSet Role) → Prop}
    {F : Finset (Clause Row Role)} (hclosed : ChoiceClosed R)
    (hcomplete : CompleteFor F R) (C : Clause Row Role) (r : Role)
    (S : Finset (Atom Row Role)) (todo : List (Atom Row Role))
    (hbad : ∀ i ∈ todo, checkBlocker F C r S i.1 ≠ true)
    (x : Row → WinnerSet Role) (hx : R x) (hpre : C.Premise x) (hS : Absent S x) :
    ∃ z, R z ∧ C.Premise z ∧ Absent S z ∧
      (∀ i ∈ todo, z i.1 = singleton r) ∧
      (∀ j, x j = singleton r → z j = singleton r) := by
  classical
  induction todo generalizing x with
  | nil => exact ⟨x, hx, hpre, hS, by simp, fun _ h => h⟩
  | cons i rest ih =>
    obtain ⟨y, hy, hSy, hyi, hsafe⟩ :=
      blocker_witness hcomplete C r S i.1 (hbad i (by simp))
    let z : Row → WinnerSet Role := fun j => choice r (x j) (y j)
    have hz : R z := hclosed r x y hx hy
    have hzi : z i.1 = singleton r := by simp [z, choice, hyi]
    have hzx (j : Row) (hj : x j = singleton r) : z j = singleton r := by
      simp [z, choice, hj]
    obtain ⟨w, hw, hwp, hwS, hwr, hwz⟩ :=
      ih (fun j hj => hbad j (List.mem_cons_of_mem i hj)) z hz
        (premise_choice hpre hsafe) (absent_choice hS hSy)
    refine ⟨w, hw, hwp, hwS, ?_, fun j hj => hwz j (hzx j hj)⟩
    intro j hj
    rcases List.mem_cons.mp hj with he | hj
    · subst j
      exact hwz i.1 hzi
    · exact hwr j hj

private theorem valid_blocker_progress {R : (Row → WinnerSet Role) → Prop}
    {F : Finset (Clause Row Role)} (hclosed : ChoiceClosed R)
    (hcomplete : CompleteFor F R) (C : Clause Row Role)
    (hvalid : ∀ x, R x → C.Holds x) (r : Role)
    (S : Finset (Atom Row Role)) (hinit : initial C r ⊆ S)
    (hterminal : supports F ⟨C.premise, S⟩ ≠ true) :
    ∃ i ∈ C.head, i ∉ S ∧ i.2 ≠ r ∧ checkBlocker F C r S i.1 = true := by
  classical
  by_contra hnone
  have hbad (i : Atom Row Role) (hi : i ∈ C.head \ S) :
      checkBlocker F C r S i.1 ≠ true := by
    intro hb
    obtain ⟨hih, hiS⟩ := Finset.mem_sdiff.mp hi
    apply hnone
    refine ⟨i, hih, hiS, ?_, hb⟩
    intro hir
    exact hiS (hinit (Finset.mem_filter.mpr ⟨hih, hir⟩))
  obtain ⟨x, hx, hpre, hS⟩ := invalid_witness
    (fun hv => hterminal ((hcomplete ⟨C.premise, S⟩).mpr hv))
  obtain ⟨z, hz, hzp, hzS, hzrest, _⟩ := combine_bad_blockers hclosed hcomplete C r S
    (C.head \ S).toList (fun i hi => hbad i (Finset.mem_toList.mp hi)) x hx hpre hS
  obtain ⟨i, hi, him⟩ := hvalid z hz hzp
  by_cases hiS : i ∈ S
  · exact hzS i hiS him
  · have hir : i.2 ≠ r := by
      intro he
      exact hiS (hinit (Finset.mem_filter.mpr ⟨hi, he⟩))
    have hzi := hzrest i (Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨hi, hiS⟩))
    exact hir (by simpa [hzi] using him)


theorem exists_checked_order {R : (Row → WinnerSet Role) → Prop}
    {F : Finset (Clause Row Role)} (hclosed : ChoiceClosed R)
    (hcomplete : CompleteFor F R) (C : Clause Row Role)
    (hvalid : ∀ x, R x → C.Holds x) (r : Role)
    (S : Finset (Atom Row Role)) (hinit : initial C r ⊆ S) :
    ∃ order, checkSteps F C r S order = true := by
  classical
  generalize hn : (C.head \ S).card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases ht : supports F ⟨C.premise, S⟩ = true
    · exact ⟨[], ht⟩
    obtain ⟨i, hi, hiS, hir, hb⟩ :=
      valid_blocker_progress hclosed hcomplete C hvalid r S hinit ht
    have hlt : (C.head \ insert i S).card < n := by
      rw [Finset.sdiff_insert, ← hn]
      exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hi, hiS⟩)
    obtain ⟨rest, hrest⟩ := ih _ hlt (insert i S)
      (fun p hp => Finset.mem_insert_of_mem (hinit hp)) rfl
    refine ⟨i :: rest, ?_⟩
    simp only [checkSteps, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hi, hiS, hir⟩, hb⟩, hrest⟩

theorem complete_family_checked {R : (Row → WinnerSet Role) → Prop}
    {F : Finset (Clause Row Role)} (hclosed : ChoiceClosed R)
    (hcomplete : CompleteFor F R) (hvalid : ∀ C ∈ F, ∀ x, R x → C.Holds x) :
    ∃ orders, checkFamily F orders = true := by
  classical
  have horder (C : Clause Row Role) (r : Role) :
      ∃ order, C ∈ F → checkSteps F C r (initial C r) order = true := by
    by_cases hC : C ∈ F
    · obtain ⟨order, ho⟩ := exists_checked_order hclosed hcomplete C (hvalid C hC) r
        (initial C r) Finset.Subset.rfl
      exact ⟨order, fun _ => ho⟩
    · exact ⟨[], fun h => (hC h).elim⟩
  choose orders horders using horder
  refine ⟨orders, ?_⟩
  simpa only [checkFamily, decide_eq_true_eq] using
    (show ∀ C ∈ F, ∀ r : Role,
      checkSteps F C r (initial C r) (orders C r) = true from
      fun C hC r => horders C r hC)

theorem exists_complete_family [Fintype Row]
    (R : (Row → WinnerSet Role) → Prop) :
    ∃ F : Finset (Clause Row Role), CompleteFor F R ∧
      ∀ C ∈ F, ∀ x, R x → C.Holds x := by
  classical
  let : Fintype (Clause Row Role) := Fintype.ofInjective
    (fun C : Clause Row Role => (C.premise, C.head)) (by
      intro C D h
      cases C
      cases D
      simpa using h)
  let F : Finset (Clause Row Role) := Finset.univ.filter (fun C => ∀ x, R x → C.Holds x)
  have hvalid : ∀ C ∈ F, ∀ x, R x → C.Holds x := by
    intro C hC
    exact (Finset.mem_filter.mp hC).2
  refine ⟨F, ?_, hvalid⟩
  intro C
  constructor
  · intro hc x hx
    exact supports_sound hc (fun D hD => hvalid D hD x hx)
  · intro hc
    simp only [supports, Bool.or_eq_true, decide_eq_true_eq]
    right
    refine ⟨C, ?_, Or.inr rfl, Finset.Subset.rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩

theorem exists_complete_certificate [Fintype Row]
    (R : (Row → WinnerSet Role) → Prop) (hclosed : ChoiceClosed R) :
    ∃ (F : Finset (Clause Row Role))
      (orders : Clause Row Role → Role → List (Atom Row Role)),
      CompleteFor F R ∧ (∀ C ∈ F, ∀ x, R x → C.Holds x) ∧
        checkFamily F orders = true := by
  obtain ⟨F, hcomplete, hvalid⟩ := exists_complete_family R
  obtain ⟨orders, horders⟩ := complete_family_checked hclosed hcomplete hvalid
  exact ⟨F, orders, hcomplete, hvalid, horders⟩


private noncomputable def memberships [Fintype Row] (x : Row → WinnerSet Role) :
    Finset (Atom Row Role) := by
  classical
  exact Finset.univ.filter (fun p => p.2 ∈ (x p.1).val)

omit [DecidableEq Row] [DecidableEq Role] in
private theorem mem_memberships [Fintype Row] (x : Row → WinnerSet Role)
    (p : Atom Row Role) : p ∈ memberships x ↔ p.2 ∈ (x p.1).val := by
  classical
  simp [memberships]

omit [DecidableEq Row] [DecidableEq Role] in
private theorem memberships_injective [Fintype Row] :
    Function.Injective (memberships (Row := Row) (Role := Role)) := by
  intro x y h
  funext i
  apply Subtype.ext
  ext r
  rw [← mem_memberships x (i,r), ← mem_memberships y (i,r), h]

private theorem memberships_union [Fintype Row] (x y : Row → WinnerSet Role) :
    memberships (fun i => (x i).union (y i)) = memberships x ∪ memberships y := by
  classical
  ext p
  simp only [mem_memberships, val_union, Set.mem_union, Finset.mem_union]

theorem separate_union_closed [Fintype Row]
    {R : (Row → WinnerSet Role) → Prop}
    (hunion : ∀ x y, R x → R y → R (fun i => (x i).union (y i)))
    (x : Row → WinnerSet Role) (hx : ¬R x) :
    ∃ C : Clause Row Role, (∀ y, R y → C.Holds y) ∧ ¬C.Holds x := by
  classical
  let outside := Finset.univ \ memberships x
  let below : Finset (Row → WinnerSet Role) :=
    Finset.univ.filter (fun y => R y ∧ memberships y ⊆ memberships x)
  by_cases hne : below.Nonempty
  · obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image below (fun z => (memberships z).card) hne
    obtain ⟨hyR, hyx⟩ := (Finset.mem_filter.mp hy).2
    have hmaximal (z : Row → WinnerSet Role) (hzR : R z)
        (hzx : memberships z ⊆ memberships x) : memberships z ⊆ memberships y := by
      let w := fun i => (y i).union (z i)
      have hwR : R w := hunion y z hyR hzR
      have hww : memberships w = memberships y ∪ memberships z := memberships_union y z
      have hwx : memberships w ⊆ memberships x := by
        rw [hww]
        exact Finset.union_subset hyx hzx
      have hwbelow : w ∈ below := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwR, hwx⟩
      have hle := hmax w hwbelow
      have heq : memberships y = memberships w := Finset.eq_of_subset_of_card_le
        (by rw [hww]; exact Finset.subset_union_left) hle
      rw [heq, hww]
      exact Finset.subset_union_right
    have hnequal : memberships y ≠ memberships x := by
      intro he
      exact hx (memberships_injective he ▸ hyR)
    obtain ⟨p, hpx, hpy⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hyx, hnequal⟩)
    refine ⟨⟨some p, outside⟩, ?_, ?_⟩
    · intro z hz hpz
      by_contra hh
      have hzx : memberships z ⊆ memberships x := by
        intro q hq
        by_contra hqx
        exact hh ⟨q, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hqx⟩,
          (mem_memberships z q).mp hq⟩
      exact hpy (hmaximal z hz hzx ((mem_memberships z p).mpr hpz))
    · intro hc
      obtain ⟨q, hq, hqx⟩ := hc ((mem_memberships x p).mp hpx)
      exact (Finset.mem_sdiff.mp hq).2 ((mem_memberships x q).mpr hqx)
  · refine ⟨⟨none, outside⟩, ?_, ?_⟩
    · intro y hy _
      by_contra hh
      apply hne
      refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, ?_⟩⟩
      intro p hp
      by_contra hpx
      exact hh ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpx⟩,
        (mem_memberships y p).mp hp⟩
    · intro hc
      obtain ⟨p, hp, hpx⟩ := hc trivial
      exact (Finset.mem_sdiff.mp hp).2 ((mem_memberships x p).mpr hpx)

theorem complete_family_models [Fintype Row]
    {R : (Row → WinnerSet Role) → Prop} {F : Finset (Clause Row Role)}
    (hcomplete : CompleteFor F R)
    (hvalid : ∀ C ∈ F, ∀ x, R x → C.Holds x)
    (hunion : ∀ x y, R x → R y → R (fun i => (x i).union (y i)))
    (x : Row → WinnerSet Role) : R x ↔ Satisfies F x := by
  constructor
  · intro hx C hC
    exact hvalid C hC x hx
  · intro hx
    by_contra hn
    obtain ⟨C, hC, hnot⟩ := separate_union_closed hunion x hn
    exact hnot (supports_sound ((hcomplete C).mpr hC) hx)


omit [DecidableEq Row] [DecidableEq Role] [Fintype Role] in
theorem ChoiceClosed.union {R : (Row → WinnerSet Role) → Prop}
    (hclosed : ChoiceClosed R) (three : Fin 3 ↪ Role)
    (x y : Row → WinnerSet Role) (hx : R x) (hy : R y) :
    R (fun i => (x i).union (y i)) := by
  have hh := hclosed (three 2) _ _ (hclosed (three 0) x y hx hy)
    (hclosed (three 1) x y hx hy)
  have he : (fun i => choice (three 2) (choice (three 0) (x i) (y i))
      (choice (three 1) (x i) (y i))) = (fun i => (x i).union (y i)) := by
    funext i
    exact three_owner_union _ _ _ _ _
      (three.injective.ne (by decide)) (three.injective.ne (by decide))
      (three.injective.ne (by decide))
  simpa only [he] using hh

theorem choiceClosed_iff_checked_clauses [Fintype Row]
    (three : Fin 3 ↪ Role) (R : (Row → WinnerSet Role) → Prop) :
    ChoiceClosed R ↔
      ∃ (F : Finset (Clause Row Role))
        (orders : Clause Row Role → Role → List (Atom Row Role)),
        checkFamily F orders = true ∧ (∀ x, R x ↔ Satisfies F x) := by
  constructor
  · intro hclosed
    obtain ⟨F, orders, hcomplete, hvalid, horders⟩ := exists_complete_certificate R hclosed
    exact ⟨F, orders, horders, fun x => complete_family_models hcomplete hvalid
      (hclosed.union three) x⟩
  · rintro ⟨F, orders, horders, hmodels⟩ r x y hx hy
    exact (hmodels _).mpr (choice_preserves horders ((hmodels x).mp hx) ((hmodels y).mp hy) r)


theorem finite_sample_iff_checked_clauses [Fintype Row] {Var : Type*}
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role)
    (target : Row → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ i, t.eval (values i) = target i) ↔
      ∀ (F : Finset (Clause Row Role))
        (orders : Clause Row Role → Role → List (Atom Row Role)),
        checkFamily F orders = true →
        (∀ j, Satisfies F (fun i => values i j)) → Satisfies F target := by
  constructor
  · rintro ⟨t, ht, he⟩ F orders horders hcolumns
    have hh := core_preserves horders (fun j i => values i j) hcolumns t ht
    simpa only [he] using hh
  · intro htests
    let R : (Row → WinnerSet Role) → Prop := fun x =>
      ∃ t : Term Role Var, t.IsCore ∧ ∀ i, t.eval (values i) = x i
    have hclosed : ChoiceClosed R := by
      rintro r x y ⟨a, ha, hea⟩ ⟨b, hb, heb⟩
      exact ⟨.choice r a b, ⟨ha, hb⟩, by intro i; simp only [Term.eval, hea, heb]⟩
    obtain ⟨F, orders, horders, hmodels⟩ :=
      (choiceClosed_iff_checked_clauses three R).mp hclosed
    apply (hmodels target).mpr
    apply htests F orders horders
    intro j
    exact (hmodels _).mp ⟨.var j, trivial, fun _ => rfl⟩

theorem truth_table_iff_checked_clauses {Var : Type*} [Fintype Var]
    [DecidableEq (Var → WinnerSet Role)]
    (three : Fin 3 ↪ Role) (f : (Var → WinnerSet Role) → WinnerSet Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ v, t.eval v = f v) ↔
      ∀ (F : Finset (Clause (Var → WinnerSet Role) Role))
        (orders : Clause (Var → WinnerSet Role) Role → Role →
          List (Atom (Var → WinnerSet Role) Role)),
        checkFamily F orders = true →
        (∀ j, Satisfies F (fun v => v j)) → Satisfies F f := by
  classical
  exact finite_sample_iff_checked_clauses three (fun v j => v j) f


theorem finite_sample_sets_iff_checked_clauses [Fintype Row] {Var : Type*}
    (three : Fin 3 ↪ Role) (values : Row → Var → WinnerSet Role)
    (target : Row → Set Role) :
    (∃ t : Term Role Var, t.IsCore ∧ ∀ i, (t.eval (values i)).val = target i) ↔
      ∀ (F : Finset (Clause Row Role))
        (orders : Clause Row Role → Role → List (Atom Row Role)),
        checkFamily F orders = true →
        (∀ j, Satisfies F (fun i => values i j)) → SatisfiesSets F target := by
  classical
  constructor
  · rintro ⟨t, ht, he⟩ F orders horders hcolumns
    have hh := core_preserves horders (fun j i => values i j) hcolumns t ht
    have hraw : SatisfiesSets F (fun i => (t.eval (values i)).val) := hh
    simpa only [he] using hraw
  · intro htests
    obtain ⟨F, orders, hcomplete, hvalid, horders⟩ :=
      exists_complete_certificate (fun _ : Row → WinnerSet Role => True)
        (by intro r x y hx hy; trivial)
    have htF := htests F orders horders (fun j C hC => hvalid C hC _ trivial)
    have hnonempty (i : Row) : (target i).Nonempty := by
      let D : Clause Row Role := ⟨none, Finset.univ.image (fun r : Role => (i,r))⟩
      have hD : ∀ x : Row → WinnerSet Role, True → D.Holds x := by
        intro x _ _
        obtain ⟨r, hr⟩ := (x i).property
        exact ⟨(i,r), Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, hr⟩
      have hs : supports F D = true := (hcomplete D).mpr hD
      obtain ⟨p, hp, hm⟩ := supportsSets_sound hs htF trivial
      obtain ⟨r, _, he⟩ := Finset.mem_image.mp hp
      subst p
      exact ⟨r, hm⟩
    let packed : Row → WinnerSet Role := fun i => ⟨target i, hnonempty i⟩
    obtain ⟨t, ht, he⟩ := (finite_sample_iff_checked_clauses three values packed).mpr
      (fun F orders ho hc => htests F orders ho hc)
    exact ⟨t, ht, fun i => congrArg Subtype.val (he i)⟩


/-- The checked presentation excludes empty coordinates as well as every
other raw tuple outside the invariant relation. -/
theorem raw_choiceClosed_iff_checked_clauses [Fintype Row]
    (three : Fin 3 ↪ Role) (R : (Row → WinnerSet Role) → Prop) :
    ChoiceClosed R ↔
      ∃ (F : Finset (Clause Row Role))
        (orders : Clause Row Role → Role → List (Atom Row Role)),
        checkFamily F orders = true ∧
          (∀ x : Row → Set Role,
            (∃ y : Row → WinnerSet Role, R y ∧ ∀ i, (y i).val = x i) ↔ SatisfiesSets F x) := by
  classical
  constructor
  · intro hclosed
    obtain ⟨F, orders, hcomplete, hvalid, horders⟩ := exists_complete_certificate R hclosed
    refine ⟨F, orders, horders, fun x => ?_⟩
    constructor
    · rintro ⟨y, hy, he⟩
      have hh : SatisfiesSets F (fun i => (y i).val) := fun C hC => hvalid C hC y hy
      simpa only [he] using hh
    · intro hx
      have hnonempty (i : Row) : (x i).Nonempty := by
        let D : Clause Row Role := ⟨none, Finset.univ.image (fun r : Role => (i,r))⟩
        have hD : ∀ y : Row → WinnerSet Role, R y → D.Holds y := by
          intro y _ _
          obtain ⟨r, hr⟩ := (y i).property
          exact ⟨(i,r), Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩, hr⟩
        have hs : supports F D = true := (hcomplete D).mpr hD
        obtain ⟨p, hp, hm⟩ := supportsSets_sound hs hx trivial
        obtain ⟨r, _, he⟩ := Finset.mem_image.mp hp
        subst p
        exact ⟨r, hm⟩
      let packed : Row → WinnerSet Role := fun i => ⟨x i, hnonempty i⟩
      refine ⟨packed, ?_, fun _ => rfl⟩
      exact (complete_family_models hcomplete hvalid (hclosed.union three) packed).mpr hx
  · rintro ⟨F, orders, horders, hrawmodels⟩
    apply (choiceClosed_iff_checked_clauses three R).mpr
    refine ⟨F, orders, horders, fun y => ?_⟩
    constructor
    · intro hy
      exact (hrawmodels (fun i => (y i).val)).mp ⟨y, hy, fun _ => rfl⟩
    · intro hy
      obtain ⟨z, hz, he⟩ := (hrawmodels (fun i => (y i).val)).mpr hy
      have hzy : z = y := funext (fun i => Subtype.ext (he i))
      exact hzy ▸ hz

/-- Complete raw relation presentations and finite-sample interpolation are
both characterized by the same finite owner-elimination checks. -/
theorem complete_certificates [Fintype Row] {Var : Type*}
    (three : Fin 3 ↪ Role) (R : (Row → WinnerSet Role) → Prop)
    (values : Row → Var → WinnerSet Role) (target : Row → Set Role) :
    (ChoiceClosed R ↔
      ∃ (F : Finset (Clause Row Role))
        (orders : Clause Row Role → Role → List (Atom Row Role)),
        checkFamily F orders = true ∧
          (∀ x : Row → Set Role,
            (∃ y : Row → WinnerSet Role, R y ∧ ∀ i, (y i).val = x i) ↔ SatisfiesSets F x)) ∧
    ((∃ t : Term Role Var, t.IsCore ∧ ∀ i, (t.eval (values i)).val = target i) ↔
      ∀ (F : Finset (Clause Row Role))
        (orders : Clause Row Role → Role → List (Atom Row Role)),
        checkFamily F orders = true →
        (∀ j, Satisfies F (fun i => values i j)) → SatisfiesSets F target) :=
  ⟨raw_choiceClosed_iff_checked_clauses three R,
    finite_sample_sets_iff_checked_clauses three values target⟩

end KFOL.Core.OwnerElimination
