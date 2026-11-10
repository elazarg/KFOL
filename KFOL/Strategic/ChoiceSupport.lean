module

public import KFOL.Algebra.ChoiceSupport
public import KFOL.Strategic.FiniteChoices

/-! # Finite support of an arbitrary observed root decision

A root may have any nonempty action index type. Its continuations are actual
finite binary games, with independent full plans at every unchosen action.
The theorem reduces its equilibrium winner value after those games are fixed;
it does not define arbitrary infinitary recursive games.
-/

@[expose] public section

namespace KFOL.Strategic.FiniteChoice

universe u v
variable {Role : Type u} {Index : Type v}

/-- Restricting the root actions to a nonempty finite support has precisely
the owned-choice fold of the actual continuation SPE values. -/
theorem possibleWinners_restrict_eq_fold (owner : Role) (branches : Index → Tree Role)
    (S : Finset Index) (hS : S.Nonempty) :
    possibleWinners owner (fun i : S => branches i.val) =
      (WinnerSet.choiceFold owner S hS (fun i => Strategic.value (branches i))).val := by
  classical
  rw [possibleWinners_eq]
  by_cases he : ∃ i : S, Strategic.value (branches i.val) = WinnerSet.singleton owner
  · rw [ite_eq_left he]
    obtain ⟨i, hi⟩ := he
    exact congrArg Subtype.val ((WinnerSet.choiceFold_eq_owner_iff owner S hS
      (fun i => Strategic.value (branches i))).mpr ⟨i.val, i.property, hi⟩) |>.symm
  · rw [ite_eq_right he]
    ext winner
    rw [WinnerSet.mem_choiceFold_of_no_owner owner S hS (fun i => Strategic.value (branches i))]
    · constructor
      · rintro ⟨i, hi⟩
        exact ⟨i.val, i.property, hi⟩
      · rintro ⟨i, hi, hw⟩
        exact ⟨⟨i, hi⟩, hw⟩
    · intro i hi heq
      exact he ⟨⟨i, hi⟩, heq⟩

/-- At most K-1 actual continuation games suffice for the complete SPE winner
set of a root decision with arbitrary nonempty action set, when K≥2. -/
theorem exists_small_support [Fintype Role] [Nontrivial Role] [Nonempty Index]
    (owner : Role) (branches : Index → Tree Role) :
    ∃ (S : Finset Index) (_ : S.Nonempty), S.card ≤ Fintype.card Role - 1 ∧
      possibleWinners owner (fun i : S => branches i.val) = possibleWinners owner branches := by
  classical
  obtain ⟨S, hS, hc, he⟩ := WinnerSet.exists_small_choice_support owner
    (fun i => Strategic.value (branches i))
  refine ⟨S, hS, hc, ?_⟩
  rw [possibleWinners_restrict_eq_fold owner branches S hS, he, possibleWinners_eq]
  rfl

/-- The supported decision has an actual binary core term using only the
selected original continuation games. Equality is between winner sets defined
by full subgame-perfect profiles on both sides. -/
theorem exists_small_binary_tree [Fintype Role] [Nontrivial Role] [Nonempty Index]
    (owner : Role) (branches : Index → Tree Role) :
    ∃ (S : Finset Index) (_ : S.Nonempty) (term : Term Role S),
      S.card ≤ Fintype.card Role - 1 ∧ term.IsCore ∧
      Strategic.possibleWinners (Strategic.compile (fun i : S => branches i.val) term) =
        possibleWinners owner branches := by
  classical
  obtain ⟨S, hS, hc, hs⟩ := exists_small_support owner branches
  let _ : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  obtain ⟨term, hcore, hterm⟩ := Term.exists_core_choice_fold owner Finset.univ Finset.univ_nonempty
    (fun i : S => (.var i : Term Role S)) (fun _ _ => trivial)
  refine ⟨S, hS, term, hc, hcore, ?_⟩
  have hv := (Strategic.value_compile (fun i : S => branches i.val) term).trans
    (hterm (fun i => Strategic.value (branches i.val)))
  exact (congrArg Subtype.val hv).trans ((possibleWinners_eq_fold owner
    (fun i : S => branches i.val)).symm.trans hs)

/-- The bound is sharp already for terminal continuation games: preserving
all nonowner winners forces selection of every nonowner action. -/
theorem terminal_support_sharp [Fintype Role] [DecidableEq Role]
    (owner : Role) (S : Finset Role) (hS : S.Nonempty) (hn : owner ∉ S)
    (he : possibleWinners owner (fun i : S => Tree.leaf i.val) = {r | r ≠ owner}) :
    S = Finset.univ.erase owner ∧ S.card = Fintype.card Role - 1 := by
  have hfold := possibleWinners_restrict_eq_fold owner (fun i => Tree.leaf i) S hS
  simp only [Strategic.value_leaf] at hfold
  exact WinnerSet.choice_support_sharp owner S hS hn (hfold.symm.trans he)

end KFOL.Strategic.FiniteChoice
