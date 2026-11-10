module
public import KFOL.Strategic.Compilation
public import KFOL.Algebra.Semilattice
@[expose] public section
namespace KFOL.Strategic.FiniteChoice
universe u v
variable {Role : Type u} {Index : Type v} {branches : Index → Tree Role}

/-- The root optimality condition follows from complete deviations, and is
sufficient only together with perfection in every continuation. -/
theorem spe_iff (owner : Role) (plan : Profile branches) :
    IsSubgamePerfect owner plan ↔
      (∀ i, Strategic.IsSubgamePerfect (plan.continuation i)) ∧
      ((∃ i, Strategic.winner (plan.continuation i) = owner) → winner plan = owner) := by
  constructor
  · rintro ⟨hn,hsub⟩
    refine ⟨hsub,?_⟩
    rintro ⟨i,hi⟩
    exact hn owner ⟨i,plan.continuation⟩
      ⟨fun h => (h rfl).elim,fun _ => Strategic.change_refl _ _⟩ hi
  · rintro ⟨hsub,hlocal⟩
    refine ⟨?_,hsub⟩
    intro player replacement hdev hw
    by_cases he : owner = player
    · rcases he with rfl
      exact hlocal ⟨replacement.action,Strategic.spe_nash (hsub replacement.action)
        owner (replacement.continuation replacement.action) (hdev.2 _) hw⟩
    · have ha := hdev.1 he
      unfold winner at hw ⊢
      rw [← ha] at hw
      exact Strategic.spe_nash (hsub plan.action) player
        (replacement.continuation plan.action) (hdev.2 _) hw

open Classical in
/-- Actual finite-action equilibrium winners satisfy the same absorbing-owner
or union rule as binary choice, with independent profiles off the chosen path. -/
theorem possibleWinners_eq (owner : Role) (branches : Index → Tree Role) :
    possibleWinners owner branches =
      if ∃ i, Strategic.value (branches i) = WinnerSet.singleton owner then {owner}
      else {player | ∃ i, player ∈ Strategic.possibleWinners (branches i)} := by
  classical
  ext player
  by_cases hf : ∃ i, Strategic.value (branches i) = WinnerSet.singleton owner
  · rw [ite_eq_left hf]
    constructor
    · rintro ⟨plan,hp,hw⟩
      obtain ⟨i,hi⟩ := hf
      have hs := (spe_iff owner plan).mp hp
      have he : Strategic.possibleWinners (branches i) = {owner} := congrArg Subtype.val hi
      exact hw.symm.trans (hs.2 ⟨i,Strategic.winner_of_singleton owner he _ (hs.1 i)⟩)
    · intro he
      change player = owner at he
      subst player
      obtain ⟨chosen,hc⟩ := hf
      choose plans hplans using fun i => Strategic.exists_spe (branches i)
      have hw : Strategic.winner (plans chosen) = owner :=
        Strategic.winner_of_singleton owner (congrArg Subtype.val hc) _ (hplans chosen)
      refine ⟨⟨chosen,plans⟩,(spe_iff owner _).mpr ⟨hplans,fun _ => hw⟩,hw⟩
  · rw [ite_eq_right hf]
    constructor
    · rintro ⟨plan,hp,hw⟩
      exact ⟨plan.action,plan.continuation plan.action,hp.2 _,hw⟩
    · rintro ⟨chosen,selected,hselected,hwin⟩
      have hlose (i : Index) : ∃ p : Strategic.Profile (branches i),
          Strategic.IsSubgamePerfect p ∧ Strategic.winner p ≠ owner :=
        Strategic.exists_spe_losing (branches i) owner (fun h => hf ⟨i,Subtype.ext h⟩)
      have hplans (i : Index) : ∃ p : Strategic.Profile (branches i),
          Strategic.IsSubgamePerfect p ∧
          (i = chosen → Strategic.winner p = player) ∧
          (i ≠ chosen → Strategic.winner p ≠ owner) := by
        by_cases he : i = chosen
        · subst i
          exact ⟨selected,hselected,fun _ => hwin,fun h => (h rfl).elim⟩
        · obtain ⟨p,hp,hl⟩ := hlose i
          exact ⟨p,hp,fun h => (he h).elim,fun _ => hl⟩
      choose plans hperfect hchosen hother using hplans
      have hw : winner (⟨chosen,plans⟩ : Profile branches) = player := hchosen chosen rfl
      refine ⟨⟨chosen,plans⟩,(spe_iff owner _).mpr ⟨hperfect,?_⟩,hw⟩
      rintro ⟨i,hi⟩
      by_cases he : i = chosen
      · subst i
        exact hi
      · exact (hother i he hi).elim

/-- The root action set is finite and nonempty, so its actual SPE value is
exactly the semilattice fold of the continuation SPE values. -/
theorem possibleWinners_eq_fold [Fintype Index] [Nonempty Index]
    (owner : Role) (branches : Index → Tree Role) :
    possibleWinners owner branches =
      (WinnerSet.choiceFold owner Finset.univ Finset.univ_nonempty
        (fun i => Strategic.value (branches i))).val := by
  classical
  rw [possibleWinners_eq]
  by_cases hf : ∃ i, Strategic.value (branches i) = WinnerSet.singleton owner
  · rw [ite_eq_left hf]
    exact congrArg Subtype.val ((WinnerSet.choiceFold_eq_owner_iff owner Finset.univ
      Finset.univ_nonempty (fun i => Strategic.value (branches i))).mpr (by simpa using hf)).symm
  · rw [ite_eq_right hf]
    ext player
    simpa only [Finset.mem_univ,true_and,Strategic.value,Set.mem_ofPred_eq] using
      (WinnerSet.mem_choiceFold_of_no_owner owner Finset.univ Finset.univ_nonempty
        (fun i => Strategic.value (branches i)) (fun i _ hi => hf ⟨i,hi⟩) player).symm

/-- Binary public syntax suffices for an actual finite-action quantifier,
including its full contingent SPE interpretation. -/
theorem exists_binary_tree [Fintype Index] [Nonempty Index]
    (owner : Role) (branches : Index → Tree Role) :
    ∃ binary : Tree Role, Strategic.possibleWinners binary = possibleWinners owner branches := by
  obtain ⟨term,hterm⟩ := Term.exists_choice_fold owner Finset.univ Finset.univ_nonempty
    (fun i : Index => (.var i : Term Role Index))
  refine ⟨Strategic.compile branches term,?_⟩
  have he := (Strategic.value_compile branches term).trans (hterm (fun i => Strategic.value (branches i)))
  rw [possibleWinners_eq_fold]
  exact congrArg Subtype.val he
end KFOL.Strategic.FiniteChoice
