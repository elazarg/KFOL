module

public import KFOL.Core.CrownRegions
public import KFOL.Algebra.Views

/-! # Crown obstructions have trivial ghost residuals

Fixing any input to an ambiguous menu omitting the queried owner makes that
owner's output bit exactly the union of the remaining input bits. In
particular all codimension-one canonical ghost sections are input unions.
-/

@[expose] public section
namespace KFOL.Core.Crown
open WinnerSet
universe u v
variable {Role : Type u} {Var : Type v} [Nonempty Var]

/-- An ambiguous input that omits the queried owner leaves only the union of
all remaining inputs visible to that owner, for every selected crown. -/
theorem membership_of_ambiguous_omission (vertices : Fin 3 ↪ Var)
    (b c : Role) (next : Equiv.Perm Var) (selected : Set Var)
    (values : Var → WinnerSet Role) (j : Var) (k : Role)
    (hamb : (values j).Ambiguous) (hnot : k ∉ (values j).val) :
    k ∈ (operation b c next selected values).val ↔
      ∃ i, i ≠ j ∧ k ∈ (values i).val := by
  classical
  by_cases hex : ∃ i ∈ selected, Cylinder b c next i values
  · have hpos := hex
    obtain ⟨i, _, hi⟩ := hex
    have hji : j ≠ i := by
      intro he
      subst j
      exact hamb c hi.1
    have hjnext : j = next i := by
      by_contra hn
      exact hamb b (hi.2.2.2 j hji hn)
    rw [operation, ite_eq_left hpos]
    constructor
    · intro hk
      rcases hk with hk | hk
      · have hkb : k = b := hk
        subst k
        obtain ⟨q, hqi, hqn⟩ := exists_role_outside_pair vertices i (next i)
        refine ⟨q, ?_, ?_⟩
        · intro hqj
          exact hqn (hqj.trans hjnext)
        · rw [hi.2.2.2 q hqi hqn]
          rfl
      · have hkc : k = c := hk
        subst k
        exact ⟨i, Ne.symm hji, by rw [hi.1]; rfl⟩
    · rintro ⟨q, hqj, hk⟩
      by_cases hqi : q = i
      · right
        simpa only [hqi, hi.1] using hk
      · left
        have hqn : q ≠ next i := by
          intro he
          exact hqj (he.trans hjnext.symm)
        simpa only [hi.2.2.2 q hqi hqn] using hk
  · rw [operation, ite_eq_right hex]
    simp only [inputUnion, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_, hi⟩
      intro he
      exact hnot (he ▸ hi)
    · rintro ⟨i, _, hi⟩
      exact ⟨i, hi⟩

/-- Any nonempty family of ambiguous inputs omitting the queried owner can
be erased simultaneously: only the remaining inputs contribute that owner. -/
theorem membership_of_ambiguous_omitted_family (vertices : Fin 3 ↪ Var)
    (b c : Role) (next : Equiv.Perm Var) (selected : Set Var)
    (values : Var → WinnerSet Role) (S : Set Var) (hne : S.Nonempty) (k : Role)
    (hamb : ∀ j ∈ S, (values j).Ambiguous)
    (hnot : ∀ j ∈ S, k ∉ (values j).val) :
    k ∈ (operation b c next selected values).val ↔
      ∃ i, i ∉ S ∧ k ∈ (values i).val := by
  obtain ⟨j, hj⟩ := hne
  rw [membership_of_ambiguous_omission vertices b c next selected values j k
    (hamb j hj) (hnot j hj)]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, fun hiS => hnot i hiS hi, hi⟩
  · rintro ⟨i, hiS, hi⟩
    exact ⟨i, fun he => hiS (he.symm ▸ hj), hi⟩

/-- The canonical impossible representative gives the same trivial residual
for every queried owner. -/
theorem membership_representative_section [DecidableEq Var] (vertices : Fin 3 ↪ Var)
    (three : Fin 3 ↪ Role) (b c : Role) (next : Equiv.Perm Var)
    (selected : Set Var) (values : Var → WinnerSet Role) (j : Var) (k : Role) :
    k ∈ (operation b c next selected
      (Function.update values j (PlayerView.representative three k .impossible))).val ↔
      ∃ i, i ≠ j ∧ k ∈ (values i).val := by
  classical
  have hrep := (WinnerSet.view_eq_impossible_iff k _).mp
    (PlayerView.view_representative three k .impossible)
  have h := membership_of_ambiguous_omission vertices b c next selected
    (Function.update values j (PlayerView.representative three k .impossible)) j k
    (by simpa only [Function.update_self, WinnerSet.Ambiguous] using hrep.2)
    (by simpa only [Function.update_self] using hrep.1)
  rw [h]
  constructor
  · rintro ⟨i, hij, hi⟩
    exact ⟨i, hij, by simpa only [Function.update_of_ne hij] using hi⟩
  · rintro ⟨i, hij, hi⟩
    exact ⟨i, hij, by simpa only [Function.update_of_ne hij] using hi⟩

/-- Every codimension-one ghost residual of a crown operation is exactly the
union of its remaining input menus. -/
theorem ghost_residual_eq_union [DecidableEq Var] (vertices : Fin 3 ↪ Var)
    (three : Fin 3 ↪ Role) (b c : Role) (next : Equiv.Perm Var)
    (selected : Set Var) (values : Var → WinnerSet Role) (j : Var) :
    {k | k ∈ (operation b c next selected
      (Function.update values j (PlayerView.representative three k .impossible))).val} =
      ⋃ i, ⋃ (_ : i ≠ j), (values i).val := by
  classical
  ext k
  simpa only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop] using
    membership_representative_section vertices three b c next selected values j k

end KFOL.Core.Crown
