module

public import KFOL.Algebra.ChoiceSupport
public import KFOL.Algebra.TestDomains
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi

/-! # Distinguishing transversal families by core word contexts

The inputs are a hub and a family of pairs. A transversal selects one member
of each pair. The word indexed by a family of transversals keeps the hub
unless the selected menus of some transversal are all the owner's singleton.
-/

@[expose] public section

namespace KFOL.Core.TransversalContexts

open scoped Classical

universe u v w

variable {Role : Type u} {I : Type v} [Nonempty I]

/-- Union of a nonempty indexed family of menus. -/
def menuUnion {J : Type w} [Nonempty J] (v : J → WinnerSet Role) : WinnerSet Role :=
  ⟨⋃ j, (v j).val, by
    obtain ⟨j⟩ := ‹Nonempty J›
    exact (v j).property.mono (Set.subset_iUnion _ j)⟩

private theorem menuUnion_eq_singleton_iff {J : Type w} [Nonempty J]
    (v : J → WinnerSet Role) (r : Role) :
    menuUnion v = WinnerSet.singleton r ↔ ∀ j, v j = WinnerSet.singleton r := by
  constructor
  · intro h j
    apply WinnerSet.eq_singleton_of_subset
    exact (Set.subset_iUnion (fun j => (v j).val) j).trans (le_of_eq (congrArg Subtype.val h))
  · intro h
    apply WinnerSet.eq_singleton_of_subset
    exact Set.iUnion_subset (fun j => le_of_eq (congrArg Subtype.val (h j)))

/-- A transversal in the family is posted entirely at the given owner. -/
def Fires (r : Role) (S : Finset (I → Bool)) (v : I × Bool → WinnerSet Role) : Prop :=
  ∃ t ∈ S, ∀ i, v (i, t i) = WinnerSet.singleton r

/-- The operation indexed by a transversal family, with the hub as its final argument. -/
noncomputable def word (r : Role) (S : Finset (I → Bool))
    (v : I × Bool → WinnerSet Role) (hub : WinnerSet Role) : WinnerSet Role :=
  if Fires r S v then menuUnion v else (menuUnion v).union hub

/-- For a nonempty family the context uses the word with its hole at the hub.
The empty family acts by the identity context. -/
noncomputable def context (r : Role) (D : Finset (I → Bool))
    (v : I × Bool → WinnerSet Role) (hole : WinnerSet Role) : WinnerSet Role :=
  if D.Nonempty then word r D v hole else hole

/-- Substitution of the family word into the hub takes the union of the two families. -/
theorem context_word (r : Role) (D S : Finset (I → Bool))
    (v : I × Bool → WinnerSet Role) (hub : WinnerSet Role) :
    context r D v (word r S v hub) = word r (S ∪ D) v hub := by
  by_cases hd : D.Nonempty
  · have hu : Fires r (S ∪ D) v ↔ Fires r S v ∨ Fires r D v := by
      simp only [Fires, Finset.mem_union, or_and_right, exists_or]
    apply Subtype.ext
    by_cases hS : Fires r S v <;> by_cases hD : Fires r D v <;>
      simp [context, word, hd, hS, hD, hu]
  · simp [context, Finset.not_nonempty_iff_eq_empty.mp hd]

private theorem exists_union_term {J : Type w} [Nonempty J] [Fintype J] {Var : Type v}
    (three : Fin 3 ↪ Role) (leaf : J → Var) :
    ∃ t : Term Role Var, t.IsCore ∧
      ∀ v : Var → WinnerSet Role, t.eval v = menuUnion (fun j => v (leaf j)) := by
  let F (j : J) (v : Var → WinnerSet Role) := (v (leaf j)).val
  have all := Finset.univ_nonempty (α := J)
  obtain ⟨t, hc, he⟩ := Finset.sup'_induction all F
    (p := fun f => ∃ t : Term Role Var, t.IsCore ∧ ∀ v, (t.eval v).val = f v)
    (fun _ ⟨s, hs, es⟩ _ ⟨t, ht, et⟩ => ⟨Term.unionTerm three s t,
      by simp [Term.unionTerm, Term.IsCore, hs, ht], fun v => by
        rw [Term.eval_unionTerm, WinnerSet.val_union, es, et]; rfl⟩)
    (fun j _ => ⟨.var (leaf j), trivial, fun _ => rfl⟩)
  refine ⟨t, hc, fun v => Subtype.ext ?_⟩
  rw [he, Finset.sup'_apply]
  ext x
  simp [Finset.sup'_eq_sup, F, menuUnion]

/-- Every family word is realized by a constant-free, switch-free owned-choice term. -/
theorem exists_word_term [Fintype I] (three : Fin 3 ↪ Role) (r : Role) (S : Finset (I → Bool)) :
    ∃ t : Term Role (Option (I × Bool)), t.IsCore ∧ ∀ v,
      t.eval v = word r S (fun p => v (some p)) (v none) := by
  obtain ⟨u, huc, hue⟩ := exists_union_term (J := I × Bool) three some
  by_cases hs : S.Nonempty
  · have clauses (t : I → Bool) := exists_union_term three (fun i => some (i,t i))
    choose cs hcs ecs using clauses
    obtain ⟨h, hhc, ehe⟩ := Term.exists_core_choice_fold r S hs cs (fun t _ => hcs t)
    refine ⟨Term.unionTerm three u (.choice r (.var none) h),
      by simp [Term.unionTerm, Term.IsCore, huc, hhc], ?_⟩
    intro v
    let U := menuUnion (fun p : I × Bool => v (some p))
    have hits : h.eval v = WinnerSet.singleton r ↔ Fires r S (fun p => v (some p)) := by
      rw [ehe, WinnerSet.choiceFold_eq_owner_iff]
      simp only [ecs, menuUnion_eq_singleton_iff, Fires]
    have sub : (h.eval v).val ⊆ U.val := by
      rw [ehe]
      let := WinnerSet.choiceSemilattice r
      apply Finset.sup'_induction hs (fun j => (cs j).eval v)
        (p := fun a : WinnerSet Role => a.val ⊆ U.val)
      · intro a ha b hb
        exact (WinnerSet.choice_subset_union r a b).trans (Set.union_subset ha hb)
      · intro t _
        rw [ecs]
        exact Set.iUnion_subset (fun i => Set.subset_iUnion (fun p : I × Bool => (v (some p)).val) (i,t i))
    rw [Term.eval_unionTerm, hue]
    change U.union (WinnerSet.choice r (v none) (h.eval v)) =
      if Fires r S (fun p => v (some p)) then U else U.union (v none)
    by_cases hit : h.eval v = WinnerSet.singleton r
    · rw [ite_eq_left (hits.mp hit)]
      have eq := (WinnerSet.choice_eq_owner_iff (v none) (h.eval v) r).2 (Or.inr hit)
      rw [eq]
      exact Subtype.ext (Set.union_eq_left.mpr (hit ▸ sub))
    · rw [ite_eq_right (fun hh => hit (hits.mpr hh))]
      by_cases hub : v none = WinnerSet.singleton r
      · rw [(WinnerSet.choice_eq_owner_iff _ _ r).2 (Or.inl hub), hub]
      · apply Subtype.ext
        simp only [WinnerSet.choice, not_or_intro hub hit, ite_false, WinnerSet.val_union]
        exact (Set.union_assoc ..).symm.trans
          (Set.union_eq_left.mpr (sub.trans Set.subset_union_left))
  · refine ⟨Term.unionTerm three u (.var none),
      by simp [Term.unionTerm, Term.IsCore, huc], fun v => ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hs, Term.eval_unionTerm, hue, word, Fires, Term.eval]

/-- The contexts likewise use only variables and owned choices, including the identity. -/
theorem exists_context_term [Fintype I] (three : Fin 3 ↪ Role) (r : Role) (D : Finset (I → Bool)) :
    ∃ t : Term Role (Option (I × Bool)), t.IsCore ∧ ∀ v,
      t.eval v = context r D (fun p => v (some p)) (v none) := by
  by_cases hd : D.Nonempty
  · simpa only [context, ite_eq_left hd] using exists_word_term three r D
  · exact ⟨.var none, trivial, fun _ => by simp [context, hd, Term.eval]⟩

/-- Distinct transversal families already give distinct operations on singleton inputs. -/
theorem word_eq_iff (three : Fin 3 ↪ Role) (r : Role) (S T : Finset (I → Bool)) :
    word r S = word r T ↔ S = T := by
  refine ⟨fun he => ?_, congrArg (word r)⟩
  obtain ⟨s, hsr, _⟩ := exists_role_outside_pair three r r
  obtain ⟨k, hkr, hks⟩ := exists_role_outside_pair three r s
  ext t
  let v (p : I × Bool) := WinnerSet.singleton (if p.2 = t p.1 then r else s)
  have detect (A : Finset (I → Bool)) : Fires r A v ↔ t ∈ A := by
    constructor
    · rintro ⟨u, hu, hit⟩
      have eq : u = t := funext fun i => by
        by_contra hn
        exact hsr (WinnerSet.singleton_inj.mp (by simpa [v, hn] using hit i))
      simpa [eq] using hu
    · intro ht
      exact ⟨t, ht, fun i => by simp [v]⟩
  have outside : k ∉ (menuUnion v).val := by
    rintro h
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp h
    by_cases hb : p.2 = t p.1 <;> simp_all [v]
  have probe (A : Finset (I → Bool)) :
      k ∉ (word r A v (WinnerSet.singleton k)).val ↔ t ∈ A := by
    by_cases ha : t ∈ A <;> simp [word, detect, ha, outside]
  rw [← probe S, ← probe T, he]

/-- Two family words pass precisely the same tests against the single full-family
target if and only if their families agree. To read the membership of one
transversal, fill in all the others with one context. -/
theorem same_full_target_contexts_iff [Fintype I] (three : Fin 3 ↪ Role) (r : Role)
    (S T : Finset (I → Bool)) :
    (∀ D : Finset (I → Bool),
      (∀ v hub, context r D v (word r S v hub) = word r Finset.univ v hub) ↔
      (∀ v hub, context r D v (word r T v hub) = word r Finset.univ v hub)) ↔ S = T := by
  have test (A : Finset (I → Bool)) (t : I → Bool) :
      (∀ v hub, context r (Finset.univ.erase t) v (word r A v hub) = word r Finset.univ v hub) ↔
        t ∈ A := by
    simp only [context_word, ← funext_iff, word_eq_iff three]
    constructor
    · intro h
      have hm := congrArg (fun B : Finset (I → Bool) => t ∈ B) h
      simpa using hm
    · intro ht
      ext s
      by_cases he : s = t <;> simp [he, ht]
  constructor
  · intro h
    ext t
    exact (test S t).symm.trans ((h (Finset.univ.erase t)).trans (test T t))
  · rintro rfl _
    rfl

end KFOL.Core.TransversalContexts
