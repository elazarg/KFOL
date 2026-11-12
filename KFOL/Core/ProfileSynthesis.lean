module

public import KFOL.Definitions.CoreFunctions
public import KFOL.Core.Folds
public import Mathlib.Data.Fintype.Pi

/-! # Synthesis of all singleton-winning profiles

Every owner chooses one of its winning coalitions. A leaf returns the union
of the variables in their common intersection. The intersection condition
makes every leaf nonempty. An owner can choose a coalition contained in its
input exactly when that input is winning; every other owner can choose the
whole variable set. This proves the converse of the common-source theorem.
-/

@[expose] public section

namespace KFOL.Core

universe u v w

variable {Role : Type u} [DecidableEq Role] {Var : Type v}

private theorem profile_top (i : Role)
    (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile i (fun _ => true) t = true := by
  induction t using induction_choice with
  | var x => rfl
  | choice r s t hs ht => simp [profile_choice, hs, ht]

/-- The three conditions hold for every core term, at arbitrary arity. -/
theorem admissibleProfiles_profile (t : Equational.Term (Equational.CoreSymbol Role) Var) :
    AdmissibleProfiles (fun i v => profile i v t) where
  mono r _ _ h := profile_mono r _ _ h t
  top r := profile_top r t
  common_source v h := profile_common_source id Function.injective_id v t h

private theorem profile_union (three : Fin 3 ↪ Role) (i : Role) (v : Var → Bool)
    (s t : Equational.Term (Equational.CoreSymbol Role) Var) :
    profile i v (unionTerm three s t) = true ↔
      profile i v s = true ∧ profile i v t = true := by
  have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := three.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := three.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  simp only [unionTerm, profile_choice]
  split_ifs <;> simp_all

noncomputable def unionFamily (three : Fin 3 ↪ Role) {A : Type w}
    [Fintype A] (a : A) (f : A → Equational.Term (Equational.CoreSymbol Role) Var) :
    Equational.Term (Equational.CoreSymbol Role) Var :=
  (Finset.univ.toList.map f).foldr (unionTerm three) (f a)

private theorem profile_unionFamily (three : Fin 3 ↪ Role) {A : Type w}
    [Fintype A] (a : A) (f : A → Equational.Term (Equational.CoreSymbol Role) Var)
    (i : Role) (v : Var → Bool) :
    profile i v (unionFamily three a f) = true ↔ ∀ x, profile i v (f x) = true := by
  have aux (xs : List (Equational.Term (Equational.CoreSymbol Role) Var)) :
      profile i v (xs.foldr (unionTerm three) (f a)) = true ↔
        profile i v (f a) = true ∧ ∀ t ∈ xs, profile i v t = true := by
    induction xs with
    | nil => simp
    | cons t xs ih => simp only [List.foldr_cons, profile_union, ih, List.mem_cons,
        forall_eq_or_imp]; tauto
  simp only [unionFamily, aux, List.forall_mem_map, Finset.mem_toList, Finset.mem_univ,
    forall_const]
  exact ⟨And.right, fun h => ⟨h a, h⟩⟩

noncomputable def choiceFamily (r : Role) {A : Type w} [Fintype A]
    (a : A) (f : A → Equational.Term (Equational.CoreSymbol Role) Var) :
    Equational.Term (Equational.CoreSymbol Role) Var :=
  foldTerm r (Finset.univ.toList.map f) (f a)

private theorem profile_choiceFamily_owner (r : Role) {A : Type w} [Fintype A]
    (a : A) (f : A → Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → Bool) :
    profile r v (choiceFamily r a f) = true ↔ ∃ x, profile r v (f x) = true := by
  rw [choiceFamily, profile_fold_owner]
  constructor
  · rintro (ha | ⟨t, ht, hp⟩)
    · exact ⟨a, ha⟩
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp ht
      exact ⟨x, hp⟩
  · rintro ⟨x, hx⟩
    exact Or.inr ⟨f x, List.mem_map.mpr ⟨x, by simp, rfl⟩, hx⟩

private theorem profile_choiceFamily_other (r i : Role) (hri : r ≠ i)
    {A : Type w} [Fintype A] (a : A)
    (f : A → Equational.Term (Equational.CoreSymbol Role) Var) (v : Var → Bool) :
    profile i v (choiceFamily r a f) = true ↔ ∀ x, profile i v (f x) = true := by
  simp only [choiceFamily, profile_fold_other r i hri, List.forall_mem_map,
    Finset.mem_toList, Finset.mem_univ, forall_const]
  exact ⟨And.right, fun h => ⟨h a, h⟩⟩

namespace ProfileSynthesis

variable [Fintype Role] [Fintype Var] {F : Role → (Var → Bool) → Bool}
    (hF : AdmissibleProfiles F)

abbrev Winning (r : Role) := {v : Var → Bool // F r v = true}

def full (r : Role) : Winning (F := F) r := ⟨fun _ => true, hF.top r⟩

abbrev Assignment := ∀ r : Role, Winning (F := F) r

abbrev Intersection (a : Assignment (F := F)) := {x : Var // ∀ r, (a r).val x = true}

noncomputable def leaf (three : Fin 3 ↪ Role) (a : Assignment (F := F)) :
    Equational.Term (Equational.CoreSymbol Role) Var :=
  unionFamily three
    (⟨(hF.common_source (fun r => (a r).val) (fun r => (a r).property)).choose,
      (hF.common_source (fun r => (a r).val) (fun r => (a r).property)).choose_spec⟩ :
        Intersection a)
    (fun x => .var x.val)

private theorem profile_leaf (three : Fin 3 ↪ Role) (a : Assignment (F := F))
    (i : Role) (v : Var → Bool) :
    profile i v (leaf hF three a) = true ↔ ∀ x, (∀ r, (a r).val x = true) → v x = true := by
  rw [leaf, profile_unionFamily]
  exact ⟨fun h x hx => h ⟨x, hx⟩, fun h x => h x.val x.property⟩

noncomputable def build (three : Fin 3 ↪ Role) :
    List Role → Assignment (F := F) → Equational.Term (Equational.CoreSymbol Role) Var
  | [], a => leaf hF three a
  | r :: rs, a => by
      classical
      exact choiceFamily r (full hF r)
        (fun w => build three rs (Function.update a r w))

private theorem positive_fixed (three : Fin 3 ↪ Role) (rs : List Role)
    (a : Assignment (F := F)) (i : Role) (v : Var → Bool) (hi : i ∉ rs)
    (hav : ∀ x, (a i).val x = true → v x = true) :
    profile i v (build hF three rs a) = true := by
  classical
  induction rs generalizing a with
  | nil => exact (profile_leaf hF three a i v).mpr (fun x hx => hav x (hx i))
  | cons r rs ih =>
    have hri : r ≠ i := fun he => hi (he ▸ List.mem_cons_self)
    apply (profile_choiceFamily_other r i hri _ _ _).mpr
    intro w
    apply ih (Function.update a r w) (fun h => hi (List.mem_cons_of_mem r h))
    simpa only [Function.update_of_ne hri.symm] using hav

private theorem positive (three : Fin 3 ↪ Role) (rs : List Role) (hn : rs.Nodup)
    (a : Assignment (F := F)) (i : Role) (v : Var → Bool) (hi : i ∈ rs)
    (hv : F i v = true) : profile i v (build hF three rs a) = true := by
  classical
  induction rs generalizing a with
  | nil => simp at hi
  | cons r rs ih =>
    rcases List.nodup_cons.mp hn with ⟨hr, hns⟩
    by_cases hri : r = i
    · subst r
      apply (profile_choiceFamily_owner i _ _ _).mpr
      refine ⟨⟨v, hv⟩, positive_fixed hF three rs _ i v hr ?_⟩
      simp
    · apply (profile_choiceFamily_other r i hri _ _ _).mpr
      intro w
      exact ih hns _ (List.mem_of_ne_of_mem (Ne.symm hri) hi)

private theorem negative (three : Fin 3 ↪ Role) (rs : List Role)
    (a : Assignment (F := F)) (i : Role) (v : Var → Bool) (hv : F i v ≠ true)
    (ha : ∀ r, r ≠ i → r ∉ rs → (a r).val = fun _ => true) :
    profile i v (build hF three rs a) ≠ true := by
  classical
  induction rs generalizing a with
  | nil =>
    intro hp
    apply hv
    apply hF.mono i (a i).val v
      (fun x hx => (profile_leaf hF three a i v).mp hp x (fun r => ?_)) (a i).property
    by_cases hr : r = i
    · subst r; exact hx
    · rw [ha r hr (by simp)]
  | cons r rs ih =>
    by_cases hri : r = i
    · subst r
      intro hp
      obtain ⟨w, hw⟩ := (profile_choiceFamily_owner i _ _ _).mp hp
      apply ih (Function.update a i w) ?_ hw
      intro r hri hr
      rw [Function.update_of_ne hri]
      exact ha r hri (by simp [hri, hr])
    · intro hp
      apply ih (Function.update a r (full hF r)) ?_
        ((profile_choiceFamily_other r i hri _ _ _).mp hp (full hF r))
      intro j hji hj
      by_cases hjr : j = r
      · subst j; simp [full]
      · rw [Function.update_of_ne hjr]
        exact ha j hji (by simp [hjr, hj])

end ProfileSynthesis

/-- The finite coalition construction realizing a prescribed admissible family. -/
noncomputable def synthesizeProfiles [Fintype Role] [Fintype Var]
    (three : Fin 3 ↪ Role) (F : Role → (Var → Bool) → Bool)
    (hF : AdmissibleProfiles F) : Equational.Term (Equational.CoreSymbol Role) Var :=
  ProfileSynthesis.build hF three Finset.univ.toList (ProfileSynthesis.full hF)

theorem profile_synthesizeProfiles [Fintype Role] [Fintype Var]
    (three : Fin 3 ↪ Role) (F : Role → (Var → Bool) → Bool)
    (hF : AdmissibleProfiles F) (i : Role) (v : Var → Bool) :
    profile i v (synthesizeProfiles three F hF) = F i v := by
  classical
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hp
    by_contra hv
    exact ProfileSynthesis.negative hF three _ _ i v hv (by simp) hp
  · intro hv
    exact ProfileSynthesis.positive hF three _ (Finset.nodup_toList _) _ i v (by simp) hv

/-- A family is realizable by a single core term exactly when its winning
coalitions satisfy monotonicity, unanimity, and the common-source condition.
The variable type can be any finite type; no arity bound is imposed. -/
theorem exists_term_iff_admissibleProfiles [Fintype Role] [Fintype Var]
    (three : Fin 3 ↪ Role) (F : Role → (Var → Bool) → Bool) :
    (∃ t : Equational.Term (Equational.CoreSymbol Role) Var,
      ∀ i v, profile i v t = F i v) ↔ AdmissibleProfiles F := by
  classical
  constructor
  · rintro ⟨t, ht⟩
    have he : (fun i v => profile i v t) = F := funext (fun i => funext (ht i))
    exact he ▸ admissibleProfiles_profile t
  · intro hF
    exact ⟨synthesizeProfiles three F hF, profile_synthesizeProfiles three F hF⟩

/-- The Boolean profiles describe actual singleton outputs, including on
mixed atomic and ambiguous valuations. -/
theorem winnerSet_eq_singleton_iff_profile
    (t : Equational.Term (Equational.CoreSymbol Role) Var) (i : Role)
    (v : Var → WinnerSet Role) :
    letI := Equational.coreStructure Role
    t.realize v = WinnerSet.singleton i ↔
      profile i (fun x => decide (v x = WinnerSet.singleton i)) t = true := by
  classical
  let _ := Equational.coreStructure Role
  induction t using induction_choice with
  | var x => simp
  | choice r s t hs ht =>
    change WinnerSet.choice r (s.realize v) (t.realize v) = WinnerSet.singleton i ↔ _
    by_cases hri : r = i
    · subst r
      simp only [WinnerSet.choice_eq_owner_iff, profile_choice, ite_true, Bool.or_eq_true,
        hs, ht]
    · simp only [WinnerSet.choice_eq_other_iff _ _ r hri, profile_choice,
        ite_eq_right hri, Bool.and_eq_true, hs, ht]

end KFOL.Core
