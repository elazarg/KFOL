module

public import KFOL.Algebra.Views
public import KFOL.Algebra.ChoiceSupport
public import KFOL.Core.StatusModel
public import KFOL.Definitions.CoreCertificates
public import KFOL.Definitions.Core

/-! # Checked owner-elimination certificates for core invariant clauses

Clauses have at most one positive membership premise. A finite family is
certified simultaneously: each owner order rules out absorbing children and
passes the remaining head absences to the children. Certificate checking uses
only finite data; the soundness theorem applies to arbitrary core terms.
-/

@[expose] public section

namespace KFOL.Core.OwnerElimination

open WinnerSet

universe u v w
variable {Row : Type u} {Role : Type v}

namespace Clause

variable [DecidableEq Row] [DecidableEq Role]

def eval (C : Clause Row Role) (x : Row → WinnerSet.StatusModel.Value Role) : Bool :=
  (!(match C.premise with
      | none => true
      | some p => decide (p.2 ∈ (x p.1).val))) ||
    decide (∃ p ∈ C.head, p.2 ∈ (x p.1).val)

omit [DecidableEq Row] in
theorem eval_eq_true_iff (C : Clause Row Role)
    (x : Row → WinnerSet.StatusModel.Value Role) :
    C.eval x = true ↔ C.Holds (fun i => WinnerSet.StatusModel.Value.toWinner (x i)) := by
  cases hp : C.premise with
  | none => simp [eval, Holds, Premise, Head, hp, WinnerSet.StatusModel.Value.toWinner]
  | some p =>
    simp [eval, Holds, Premise, Head, hp, WinnerSet.StatusModel.Value.toWinner]
    tauto

omit [DecidableEq Row] [DecidableEq Role] in
theorem subsumes_sound {D C : Clause Row Role} (h : D.Subsumes C)
    {x : Row → WinnerSet Role} (hD : D.Holds x) : C.Holds x := by
  intro hp
  have hpre : D.Premise x := by
    rcases h.1 with hn | he
    · simp [Premise, hn]
    · simpa only [Premise, he] using hp
  obtain ⟨p, hp, hm⟩ := hD hpre
  exact ⟨p, h.2 hp, hm⟩

theorem tautology_sound (C : Clause Row Role) (h : C.tautology = true)
    (x : Row → WinnerSet Role) : C.Holds x := by
  cases hp : C.premise with
  | none => simp [tautology, hp] at h
  | some p =>
    have hm : p ∈ C.head := by simpa [tautology, hp] using h
    intro hpre
    exact ⟨p, hm, by simpa [Premise, hp] using hpre⟩

end Clause

variable [DecidableEq Row] [DecidableEq Role]

theorem supports_sound {F : Finset (Clause Row Role)} {C : Clause Row Role}
    (h : supports F C = true) {x : Row → WinnerSet Role} (hF : Satisfies F x) :
    C.Holds x := by
  simp only [supports, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ht | ⟨D, hD, hs⟩
  · exact C.tautology_sound ht x
  · exact Clause.subsumes_sound hs (hF D hD)

variable [Fintype Role]

theorem absent_blockHead {S : Finset (Atom Row Role)} {i : Row} {r : Role}
    {x : Row → WinnerSet Role} (hS : Absent S x) (hi : x i = singleton r) :
    Absent (blockHead S i r) x := by
  intro p hp hm
  rcases Finset.mem_union.mp hp with hp | hp
  · exact hS p hp hm
  · obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hp
    subst p
    have hsr : s ≠ r := (Finset.mem_erase.mp hs).1
    exact hsr (by simpa [hi] using hm)


theorem blocker_excludes {F : Finset (Clause Row Role)} {C : Clause Row Role}
    {r : Role} {S : Finset (Atom Row Role)} {i : Row} {x : Row → WinnerSet Role}
    (hcheck : checkBlocker F C r S i = true) (hF : Satisfies F x)
    (hS : Absent S x)
    (hpre : ∀ p, C.premise = some p → p.2 ≠ r → x p.1 ≠ singleton r) :
    x i ≠ singleton r := by
  intro hi
  have hab := absent_blockHead hS hi
  cases hp : C.premise with
  | none =>
    have hc : supports F ⟨none, blockHead S i r⟩ = true := by
      simpa [checkBlocker, hp] using hcheck
    obtain ⟨p, hm, hv⟩ := supports_sound hc hF trivial
    exact hab p hm hv
  | some p =>
    by_cases hr : p.2 = r
    · have hc : supports F ⟨none, blockHead S i r⟩ = true := by
        simpa [checkBlocker, hp, hr] using hcheck
      obtain ⟨q, hm, hv⟩ := supports_sound hc hF trivial
      exact hab q hm hv
    · obtain ⟨s, hs, hsr⟩ := exists_mem_ne_of_ne_singleton r (x p.1) (hpre p hp hr)
      have hc : supports F ⟨some (p.1, s), blockHead S i r⟩ = true := by
        have hc : ∀ s ∈ Finset.univ.erase r,
            supports F ⟨some (p.1, s), blockHead S i r⟩ = true := by
          simpa [checkBlocker, hp, hr] using hcheck
        exact hc s (by simp [hsr])
      obtain ⟨q, hm, hv⟩ := supports_sound hc hF hs
      exact hab q hm hv

omit [DecidableEq Row] [DecidableEq Role] [Fintype Role] in
theorem child_premise_not_atom {C : Clause Row Role} {r : Role}
    {x y : Row → WinnerSet Role}
    (hpre : C.Premise (fun i => choice r (x i) (y i))) :
    ∀ p, C.premise = some p → p.2 ≠ r →
      x p.1 ≠ singleton r ∧ y p.1 ≠ singleton r := by
  intro p hp hpr
  have hm : p.2 ∈ (choice r (x p.1) (y p.1)).val := by
    simpa [Clause.Premise, hp] using hpre
  exact (mem_choice_other r p.2 (Ne.symm hpr) _ _).mp hm |>.2

theorem steps_sound {F : Finset (Clause Row Role)} {C : Clause Row Role}
    {r : Role} {x y : Row → WinnerSet Role}
    (hx : Satisfies F x) (hy : Satisfies F y)
    (hpre : C.Premise (fun i => choice r (x i) (y i)))
    (hhead : Absent C.head (fun i => choice r (x i) (y i)))
    (S : Finset (Atom Row Role)) (order : List (Atom Row Role))
    (hcheck : checkSteps F C r S order = true)
    (hSx : Absent S x) (hSy : Absent S y) : False := by
  induction order generalizing S with
  | nil =>
    have hc : supports F ⟨C.premise, S⟩ = true := hcheck
    cases hp : C.premise with
    | none =>
      obtain ⟨p, hm, hv⟩ := supports_sound hc hx (by simp [Clause.Premise, hp])
      exact hSx p hm hv
    | some p =>
      have hm : p.2 ∈ (choice r (x p.1) (y p.1)).val := by
        simpa [Clause.Premise, hp] using hpre
      rcases choice_subset_union r _ _ hm with hm | hm
      · obtain ⟨q, hq, hv⟩ := supports_sound hc hx (by simpa [Clause.Premise, hp] using hm)
        exact hSx q hq hv
      · obtain ⟨q, hq, hv⟩ := supports_sound hc hy (by simpa [Clause.Premise, hp] using hm)
        exact hSy q hq hv
  | cons i rest ih =>
    have hc := hcheck
    simp only [checkSteps, Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨hi, _, hir⟩, hb⟩, ht⟩
    have hpx := fun p hp hr => (child_premise_not_atom hpre p hp hr).1
    have hpy := fun p hp hr => (child_premise_not_atom hpre p hp hr).2
    have hnx := blocker_excludes hb hx hSx hpx
    have hny := blocker_excludes hb hy hSy hpy
    have hix : i.2 ∉ (x i.1).val := by
      intro hm
      exact hhead i hi ((mem_choice_other r i.2 (Ne.symm hir) _ _).mpr ⟨Or.inl hm, hnx, hny⟩)
    have hiy : i.2 ∉ (y i.1).val := by
      intro hm
      exact hhead i hi ((mem_choice_other r i.2 (Ne.symm hir) _ _).mpr ⟨Or.inr hm, hnx, hny⟩)
    apply ih (insert i S) ht
    · intro p hp
      rcases Finset.mem_insert.mp hp with he | hp
      · simpa [he] using hix
      · exact hSx p hp
    · intro p hp
      rcases Finset.mem_insert.mp hp with he | hp
      · simpa [he] using hiy
      · exact hSy p hp


theorem choice_preserves {F : Finset (Clause Row Role)}
    {orders : Clause Row Role → Role → List (Atom Row Role)}
    (hcheck : checkFamily F orders = true)
    {x y : Row → WinnerSet Role} (hx : Satisfies F x) (hy : Satisfies F y)
    (r : Role) : Satisfies F (fun i => choice r (x i) (y i)) := by
  intro C hC hpre
  by_contra hn
  have hhead : Absent C.head (fun i => choice r (x i) (y i)) := by
    intro p hp hm
    exact hn ⟨p, hp, hm⟩
  have hc : checkSteps F C r (initial C r) (orders C r) = true := by
    have hc : ∀ C ∈ F, ∀ r : Role,
        checkSteps F C r (initial C r) (orders C r) = true := by
      simpa only [checkFamily, decide_eq_true_eq] using hcheck
    exact hc C hC r
  apply steps_sound hx hy hpre hhead (initial C r) (orders C r) hc
  · intro p hp hm
    obtain ⟨hp, hr⟩ := Finset.mem_filter.mp hp
    exact hhead p hp (by
      rw [hr] at hm ⊢
      exact (mem_choice_owner r _ _).mpr (Or.inl hm))
  · intro p hp hm
    obtain ⟨hp, hr⟩ := Finset.mem_filter.mp hp
    exact hhead p hp (by
      rw [hr] at hm ⊢
      exact (mem_choice_owner r _ _).mpr (Or.inr hm))

theorem core_preserves {Var : Type w} {F : Finset (Clause Row Role)}
    {orders : Clause Row Role → Role → List (Atom Row Role)}
    (hcheck : checkFamily F orders = true) (columns : Var → Row → WinnerSet Role)
    (hcolumns : ∀ j, Satisfies F (columns j)) (t : Term Role Var) (ht : t.IsCore) :
    Satisfies F (fun i => t.eval (fun j => columns j i)) := by
  induction t with
  | winner r => contradiction
  | var j => exact hcolumns j
  | choice r a b iha ihb =>
    exact choice_preserves hcheck (iha ht.1) (ihb ht.2) r
  | rename p t ih => contradiction

def checkColumns {Var : Type w} [Fintype Var] (F : Finset (Clause Row Role))
    (columns : Var → Row → StatusModel.Value Role) : Bool :=
  decide (∀ j : Var, ∀ C ∈ F, C.eval (columns j) = true)

omit [DecidableEq Row] [Fintype Role] in
theorem checkColumns_sound {Var : Type w} [Fintype Var]
    {F : Finset (Clause Row Role)} {columns : Var → Row → StatusModel.Value Role}
    (hc : checkColumns F columns = true) :
    ∀ j, Satisfies F (fun i => StatusModel.Value.toWinner (columns j i)) := by
  have hh : ∀ j : Var, ∀ C ∈ F, C.eval (columns j) = true := by
    simpa only [checkColumns, decide_eq_true_eq] using hc
  intro j C hC
  exact (Clause.eval_eq_true_iff C (columns j)).mp (hh j C hC)

theorem certificate_sound {Var : Type w} [Fintype Var]
    {F : Finset (Clause Row Role)}
    {orders : Clause Row Role → Role → List (Atom Row Role)}
    {columns : Var → Row → StatusModel.Value Role}
    (hc : checkColumns F columns = true) (ho : checkFamily F orders = true)
    (t : Term Role Var) (ht : t.IsCore) :
    Satisfies F (fun i => t.eval (fun j => StatusModel.Value.toWinner (columns j i))) :=
  core_preserves ho _ (checkColumns_sound hc) t ht

theorem checkSteps_length_le {F : Finset (Clause Row Role)} {C : Clause Row Role}
    {r : Role} (S : Finset (Atom Row Role)) (order : List (Atom Row Role))
    (hcheck : checkSteps F C r S order = true) :
    order.length ≤ (C.head \ S).card := by
  induction order generalizing S with
  | nil => simp
  | cons i rest ih =>
    have hc := hcheck
    simp only [checkSteps, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hi, hiS, _⟩, _⟩, hrest⟩ := hc
    have hh := ih (insert i S) hrest
    have hc := Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hi, hiS⟩)
    rw [← Finset.sdiff_insert] at hc
    simp only [List.length_cons]
    omega


omit [DecidableEq Row] [DecidableEq Role] [Fintype Role] in
@[simp] theorem Clause.holdsSets_val (C : Clause Row Role) (x : Row → WinnerSet Role) :
    C.HoldsSets (fun i => (x i).val) ↔ C.Holds x := Iff.rfl

omit [DecidableEq Row] [DecidableEq Role] [Fintype Role] in
@[simp] theorem satisfiesSets_val (F : Finset (Clause Row Role)) (x : Row → WinnerSet Role) :
    SatisfiesSets F (fun i => (x i).val) ↔ Satisfies F x := Iff.rfl

omit [Fintype Role] in
theorem supportsSets_sound {F : Finset (Clause Row Role)} {C : Clause Row Role}
    (h : supports F C = true) {x : Row → Set Role} (hF : SatisfiesSets F x) :
    C.HoldsSets x := by
  simp only [supports, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ht | ⟨D, hD, hs⟩
  · cases hp : C.premise with
    | none => simp [Clause.tautology, hp] at ht
    | some p =>
      have hm : p ∈ C.head := by simpa [Clause.tautology, hp] using ht
      intro hpre
      exact ⟨p, hm, by simpa [Clause.HoldsSets, hp] using hpre⟩
  · intro hp
    have hpre : match D.premise with | none => True | some p => p.2 ∈ x p.1 := by
      rcases hs.1 with hn | he
      · simp [hn]
      · simp only [he]
        cases hpre : C.premise with
        | none => trivial
        | some p => simpa only [hpre] using hp
    obtain ⟨p, hp, hm⟩ := hF D hD hpre
    exact ⟨p, hs.2 hp, hm⟩


end KFOL.Core.OwnerElimination
