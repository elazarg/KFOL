module

public import KFOL.Algebra.Monotone
public import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max

/-! # Thinning an owned-choice spine at its last resets -/

@[expose] public section
namespace KFOL.Core.Spine

variable {Role : Type*}

abbrev Attachment (Role : Type*) := Role × WinnerSet Role

/-- An attachment is a reset when its helper is its own atom. -/
def Resets (step : Attachment Role) : Prop := step.2 = WinnerSet.singleton step.1

/-- Attach successive fixed helpers to an input. -/
noncomputable def eval (steps : List (Attachment Role)) (input : WinnerSet Role) : WinnerSet Role :=
  steps.foldl (fun x step => WinnerSet.choice step.1 x step.2) input

private theorem eval_mono (steps : List (Attachment Role)) {x y : WinnerSet Role}
    (sub : x.val ⊆ y.val) : (eval steps x).val ⊆ (eval steps y).val := by
  induction steps generalizing x y with
  | nil => exact sub
  | cons s steps ih =>
    exact ih (WinnerSet.choice_mono s.1 sub Set.Subset.rfl)

/-- Deleting any nonresetting attachments can only decrease the value
on a fixed passive valuation if the entire spine is reset free. -/
theorem eval_sublist_le_of_no_reset {short long : List (Attachment Role)}
    (sub : short.Sublist long) (no : ∀ step ∈ long, ¬ Resets step) (x : WinnerSet Role) :
    (eval short x).val ⊆ (eval long x).val := by
  induction sub generalizing x with
  | slnil => exact Set.Subset.rfl
  | cons s _ ih =>
    apply (ih (fun step h => no step (List.mem_cons_of_mem _ h)) x).trans
    exact eval_mono _ (WinnerSet.subset_choice_of_right_ne _ _ _ (no s (by simp)))
  | cons_cons s _ ih =>
    exact ih (fun step h => no step (List.mem_cons_of_mem _ h)) _

/-- When the last reset and a sublist of its suffix are retained, the
resulting value is contained in the old value, independently of which
earlier attachments are retained. -/
theorem eval_le_with_last_reset (first keptFirst : List (Attachment Role))
    (reset : Attachment Role) (fires : Resets reset)
    {last keptLast : List (Attachment Role)} (sub : keptLast.Sublist last)
    (none : ∀ step ∈ last, ¬ Resets step) (x : WinnerSet Role) :
    (eval (keptFirst ++ reset :: keptLast) x).val ⊆
      (eval (first ++ reset :: last) x).val := by
  simp only [eval, List.foldl_append, List.foldl_cons,
    show reset.2 = WinnerSet.singleton reset.1 from fires, WinnerSet.choice,
    or_true, ite_true]
  exact eval_sublist_le_of_no_reset sub none _

/-- A winner present at the start can disappear only at a helper which
resets to a different owner. -/
theorem exists_foreign_reset_of_not_mem_eval (steps : List (Attachment Role))
    {x : WinnerSet Role} {r : Role} (present : r ∈ x.val) (absent : r ∉ (eval steps x).val) :
    ∃ step ∈ steps, step.1 ≠ r ∧ Resets step := by
  induction steps generalizing x with
  | nil => exact (absent present).elim
  | cons head tail ih =>
    by_cases foreign : head.1 ≠ r ∧ Resets head
    · exact ⟨head, by simp, foreign⟩
    · have survives : r ∈ (WinnerSet.choice head.1 x head.2).val := by
        by_cases resets : Resets head
        · have same : head.1 = r := not_ne_iff.mp (fun ne => foreign ⟨ne, resets⟩)
          have atom := (WinnerSet.choice_eq_owner_iff x head.2 head.1).2 (Or.inr resets)
          rw [atom, same]
          simp
        · exact WinnerSet.subset_choice_of_right_ne _ _ _ resets present
      obtain ⟨step, step_mem, step_resets⟩ := ih survives absent
      exact ⟨step, List.mem_cons_of_mem _ step_mem, step_resets⟩

/-- A singleton reached from a different value needs a reset at its own owner. -/
theorem exists_reset_of_eval_eq_singleton (steps : List (Attachment Role))
    {x : WinnerSet Role} {r : Role} (initial : x ≠ WinnerSet.singleton r)
    (final : eval steps x = WinnerSet.singleton r) :
    ∃ step ∈ steps, step.1 = r ∧ Resets step := by
  induction steps generalizing x with
  | nil => exact (initial final).elim
  | cons head tail ih =>
    by_cases wins : WinnerSet.choice head.1 x head.2 = WinnerSet.singleton r
    · have own : head.1 = r := by
        by_contra ne
        exact initial ((WinnerSet.choice_eq_other_iff _ _ _ ne).mp wins).1
      have resets : Resets head := (WinnerSet.choice_eq_owner_iff x head.2 head.1).mp
        (by simpa only [own] using wins) |>.resolve_left (fun atom => initial (by simpa only [own] using atom))
      exact ⟨head, by simp, own, resets⟩
    · obtain ⟨step, inside, owner, resets⟩ := ih wins final
      exact ⟨step, List.mem_cons_of_mem _ inside, owner, resets⟩

/-- If the designated helper can supply the omitted winner or reset to
its own owner, a different carried value forces a foreign reset somewhere
in the intervening spine. -/
theorem exists_foreign_reset_of_helper_eq_or_mem (before after : List (Attachment Role))
    {x h : WinnerSet Role} {b c : Role} (distinct : b ≠ c)
    (initial : x ≠ WinnerSet.singleton b) (helper : h = WinnerSet.singleton b ∨ c ∈ h.val)
    (absent : c ∉ (eval (before ++ (b, h) :: after) x).val) :
    ∃ step ∈ before ++ (b, h) :: after, step.1 ≠ c ∧ Resets step := by
  rcases helper with own | present
  · exact ⟨(b, h), by simp, distinct, own⟩
  · by_cases carried : eval before x = WinnerSet.singleton b
    · obtain ⟨step, inside, owner, resets⟩ := exists_reset_of_eval_eq_singleton before initial carried
      exact ⟨step, List.mem_append_left _ inside, owner.trans_ne distinct, resets⟩
    · have no : h ≠ WinnerSet.singleton b := by
        rintro rfl
        have same : c = b := by simpa using present
        exact distinct same.symm
      have passes : c ∈ (WinnerSet.choice b (eval before x) h).val := by
        rw [WinnerSet.choice, ite_eq_right (not_or.mpr ⟨carried, no⟩), WinnerSet.val_union]
        exact Or.inr present
      have lost : c ∉ (eval after (WinnerSet.choice b (eval before x) h)).val := by
        simpa only [eval, List.foldl_append, List.foldl_cons] using absent
      obtain ⟨step, inside, foreign, resets⟩ := exists_foreign_reset_of_not_mem_eval after passes lost
      exact ⟨step, List.mem_append_right _ (List.mem_cons_of_mem _ inside), foreign, resets⟩

/-- Retain the last matching position for each query that matches at all.
The number of retained positions is bounded by the number of queries. -/
theorem exists_last_positions {Letter Query : Type*} [Fintype Query]
    (word : List Letter) (fires : Query → Letter → Prop) :
    ∃ kept : Finset (Fin word.length), kept.card ≤ Fintype.card Query ∧
      ∀ q (i : Fin word.length), fires q word[i] → ∃ j ∈ kept, i ≤ j ∧ fires q word[j] := by
  classical
  let candidates (q : Query) : Finset (Fin word.length) :=
    Finset.univ.filter (fun i : Fin word.length => fires q word[i])
  let active : Finset Query := Finset.univ.filter (fun q => (candidates q).Nonempty)
  let last (q : active) : Fin word.length :=
    (candidates q).max' (Finset.mem_filter.mp q.property).2
  refine ⟨active.attach.image last, ?_, ?_⟩
  · exact (Finset.card_image_le.trans Finset.card_attach.le).trans (Finset.card_le_univ _)
  · intro q i hi
    have mem : i ∈ candidates q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    have nonempty : (candidates q).Nonempty := ⟨i, mem⟩
    let a : active := ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, nonempty⟩⟩
    have latest : last a ∈ candidates q := Finset.max'_mem _ _
    exact ⟨last a, Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩,
      Finset.le_max' _ _ mem, (Finset.mem_filter.mp latest).2⟩

end KFOL.Core.Spine
