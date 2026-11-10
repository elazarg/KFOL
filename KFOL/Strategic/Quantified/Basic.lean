module

public import KFOL.Definitions.Quantified
public import KFOL.Algebra.Basic

/-! # Whole-profile backward induction for arbitrary public action families -/

@[expose] public section

namespace KFOL.Strategic.QuantifiedTree

universe u v
variable {Role : Type u}

theorem deviation_refl (player : Role) (game : QuantifiedTree.{u,v} Role)
    (plan : Profile game) : Deviation player plan plan := by
  induction game with
  | leaf r => trivial
  | node owner Action nonempty next ih => exact ⟨fun _ => rfl,fun a => ih a (plan.2 a)⟩

theorem spe_nash {game : QuantifiedTree.{u,v} Role} {plan : Profile game}
    (perfect : IsSubgamePerfect plan) : IsNash plan := by
  cases game with
  | leaf r => exact perfect
  | node owner Action nonempty next => exact perfect.1

@[simp] theorem spe_leaf (r : Role) (plan : Profile (.leaf r : QuantifiedTree.{u,v} Role)) :
    IsSubgamePerfect plan := by
  intro player replacement _ hw
  exact hw

/-- Local optimality is derived from whole-player deviations, and suffices
only when all continuations are independently subgame perfect. -/
theorem spe_node_iff (owner : Role) (Action : Type v) (nonempty : Nonempty Action)
    (next : Action → QuantifiedTree.{u,v} Role) (plan : Profile (.node owner Action nonempty next)) :
    IsSubgamePerfect plan ↔
      (∀ a, IsSubgamePerfect (plan.2 a)) ∧
      ((∃ a, winner (plan.2 a) = owner) → winner plan = owner) := by
  constructor
  · rintro ⟨hn,hsub⟩
    refine ⟨hsub,?_⟩
    rintro ⟨a,ha⟩
    exact hn owner (⟨a,plan.2⟩ : Profile (.node owner Action nonempty next))
      ⟨fun h => (h rfl).elim,fun b => deviation_refl owner (next b) (plan.2 b)⟩ ha
  · rintro ⟨hsub,hlocal⟩
    refine ⟨?_,hsub⟩
    intro player replacement hdev hw
    by_cases he : owner = player
    · rcases he with rfl
      exact hlocal ⟨replacement.1,spe_nash (hsub replacement.1)
        owner (replacement.2 replacement.1) (hdev.2 _) hw⟩
    · have ha := hdev.1 he
      change winner (replacement.2 replacement.1) = player at hw
      change winner (plan.2 plan.1) = player
      rw [← ha] at hw
      exact spe_nash (hsub plan.1) player (replacement.2 plan.1) (hdev.2 _) hw

/-- Backward induction over the actual tree, without an arity or a uniform
finite-depth premise. Classical choice supplies all off-path plans. -/
theorem exists_spe (game : QuantifiedTree.{u,v} Role) :
    ∃ plan : Profile game, IsSubgamePerfect plan := by
  classical
  induction game with
  | leaf r => exact ⟨PUnit.unit,spe_leaf r _⟩
  | node owner Action nonempty next ih =>
    choose plans perfect using ih
    by_cases he : ∃ a, winner (plans a) = owner
    · obtain ⟨a,ha⟩ := he
      exact ⟨⟨a,plans⟩,(spe_node_iff owner Action nonempty next _).2 ⟨perfect,fun _ => ha⟩⟩
    · obtain ⟨a⟩ := nonempty
      exact ⟨⟨a,plans⟩,(spe_node_iff owner Action ⟨a⟩ next _).2
        ⟨perfect,fun h => (he h).elim⟩⟩

theorem possibleWinners_ne (game : QuantifiedTree.{u,v} Role) :
    (possibleWinners game).Nonempty := by
  obtain ⟨plan,perfect⟩ := exists_spe game
  exact ⟨winner plan,plan,perfect,rfl⟩

@[simp] theorem possibleWinners_leaf (r : Role) :
    possibleWinners (.leaf r : QuantifiedTree.{u,v} Role) = {r} := by
  ext player
  constructor
  · rintro ⟨plan,_,hw⟩
    exact hw.symm
  · intro hp
    exact ⟨PUnit.unit,spe_leaf r _,hp.symm⟩

theorem winner_of_singleton {game : QuantifiedTree.{u,v} Role} (owner : Role)
    (only : possibleWinners game = {owner}) (plan : Profile game)
    (perfect : IsSubgamePerfect plan) : winner plan = owner := by
  have hw : winner plan ∈ possibleWinners game := ⟨plan,perfect,rfl⟩
  simpa only [only,Set.mem_singleton_iff] using hw

theorem exists_spe_losing (game : QuantifiedTree.{u,v} Role) (owner : Role)
    (not_only : possibleWinners game ≠ {owner}) :
    ∃ plan : Profile game, IsSubgamePerfect plan ∧ winner plan ≠ owner := by
  classical
  have hex : ∃ player ∈ possibleWinners game, player ≠ owner := by
    by_contra h
    push Not at h
    apply not_only
    obtain ⟨player,hp⟩ := possibleWinners_ne game
    ext r
    constructor
    · exact h r
    · intro he
      change r = owner at he
      have hp' := h player hp
      simpa only [he,hp'] using hp
  obtain ⟨player,⟨plan,perfect,hw⟩,hne⟩ := hex
  exact ⟨plan,perfect,fun he => hne (hw.symm.trans he)⟩

/-- Bundling the actual equilibrium observation only after proving it
nonempty. The definition does not use the owned-choice recurrence. -/
def value (game : QuantifiedTree.{u,v} Role) : WinnerSet Role :=
  ⟨possibleWinners game,possibleWinners_ne game⟩

@[simp] theorem value_leaf (r : Role) : value (.leaf r : QuantifiedTree.{u,v} Role) =
    WinnerSet.singleton r := Subtype.ext (possibleWinners_leaf r)

open Classical in
/-- The arbitrary-action rule is a theorem about independently specified
whole-profile SPE, with independent off-path continuation equilibria. -/
theorem possibleWinners_node (owner : Role) (Action : Type v) (nonempty : Nonempty Action)
    (next : Action → QuantifiedTree.{u,v} Role) :
    possibleWinners (.node owner Action nonempty next) =
      if ∃ a, possibleWinners (next a) = {owner} then {owner}
      else {player | ∃ a, player ∈ possibleWinners (next a)} := by
  classical
  ext player
  by_cases hf : ∃ a, possibleWinners (next a) = {owner}
  · rw [ite_eq_left hf]
    constructor
    · rintro ⟨plan,hp,hw⟩
      obtain ⟨a,ha⟩ := hf
      have hs := (spe_node_iff owner Action nonempty next plan).mp hp
      exact hw.symm.trans (hs.2 ⟨a,winner_of_singleton owner ha _ (hs.1 a)⟩)
    · intro he
      change player = owner at he
      subst player
      obtain ⟨chosen,hc⟩ := hf
      choose plans hplans using fun a => exists_spe (next a)
      have hw : winner (plans chosen) = owner := winner_of_singleton owner hc _ (hplans chosen)
      exact ⟨⟨chosen,plans⟩,(spe_node_iff owner Action nonempty next _).mpr
        ⟨hplans,fun _ => hw⟩,hw⟩
  · rw [ite_eq_right hf]
    constructor
    · rintro ⟨plan,hp,hw⟩
      exact ⟨plan.1,plan.2 plan.1,hp.2 _,hw⟩
    · rintro ⟨chosen,selected,hselected,hwin⟩
      have hplans (a : Action) : ∃ plan : Profile (next a), IsSubgamePerfect plan ∧
          (a = chosen → winner plan = player) ∧ (a ≠ chosen → winner plan ≠ owner) := by
        by_cases he : a = chosen
        · subst a
          exact ⟨selected,hselected,fun _ => hwin,fun h => (h rfl).elim⟩
        · obtain ⟨plan,hp,hl⟩ := exists_spe_losing (next a) owner (fun h => hf ⟨a,h⟩)
          exact ⟨plan,hp,fun h => (he h).elim,fun _ => hl⟩
      choose plans hperfect hchosen hother using hplans
      have hw : winner (game := .node owner Action nonempty next) ⟨chosen,plans⟩ = player :=
        hchosen chosen rfl
      refine ⟨⟨chosen,plans⟩,(spe_node_iff owner Action nonempty next _).mpr ⟨hperfect,?_⟩,hw⟩
      rintro ⟨a,ha⟩
      by_cases he : a = chosen
      · subst a
        exact ha
      · exact (hother a he ha).elim

end KFOL.Strategic.QuantifiedTree
