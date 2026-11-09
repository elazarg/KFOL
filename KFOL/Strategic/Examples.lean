module

public import KFOL.Strategic.Adequacy

/-! # An equilibrium supported by actions in an unreached subtree -/

@[expose] public section

namespace KFOL.Strategic

universe u

/-- The profile choosing the right branch wins for b. Its unreached left
subgame chooses c; it remains optimal there for b, who cannot win there. -/
theorem off_path_equilibrium {Role : Type u} (a b c : Role)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let p := Profile.node a true (.node b true (.leaf a) (.leaf c))
      (.node b false (.leaf b) (.leaf c))
    IsSubgamePerfect p ∧ winner p = b := by
  dsimp only
  refine ⟨?_, rfl⟩
  apply (spe_node_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (spe_node_iff _ _ _ _).mpr
    refine ⟨spe_leaf _, spe_leaf _, ?_⟩
    simp [LocallyOptimal, winner, hab, hbc.symm]
  · apply (spe_node_iff _ _ _ _).mpr
    exact ⟨spe_leaf _, spe_leaf _, fun _ => rfl⟩
  · simp [LocallyOptimal, winner, hac.symm, hab.symm]

/-- Ordinary Nash can ignore a losing action in an unreached proper subgame;
our independently specified SPE excludes that profile. -/
theorem nash_not_spe {Role : Type u} (a b : Role) (hab : a ≠ b) :
    let p := Profile.node a false (.leaf a) (.node b true (.leaf b) (.leaf a))
    IsNash p ∧ ¬IsSubgamePerfect p := by
  dsimp only
  constructor
  · intro i q hd hw
    cases q with
    | node _ c p q =>
      cases hd with
      | node hr _ _ =>
        by_cases hi : a = i
        · exact hi
        · have hc : false = c := hr hi
          subst c
          cases p
          exact hw
  · intro hp
    have hright : IsSubgamePerfect (.node b true (.leaf b) (.leaf a)) :=
      ((spe_node_subgames _ _ _ _).mp hp).2.2
    have ho := ((spe_node_iff _ _ _ _).mp hright).2.2
    exact hab (ho (Or.inl rfl))

end KFOL.Strategic
