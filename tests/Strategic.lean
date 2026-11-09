module

import KFOL.Strategic

/- The distinctions in these profiles are essential to public-game semantics.
They exercise unvisited subgames, arbitrary inactive roles and independent copies. -/

example {Role : Type*} (a b : Role) (hab : a ≠ b) :
    let p := KFOL.Strategic.Profile.node a false (.leaf a)
      (.node b true (.leaf b) (.leaf a))
    KFOL.Strategic.IsNash p ∧ ¬KFOL.Strategic.IsSubgamePerfect p :=
  KFOL.Strategic.nash_not_spe a b hab

example :
    let p := KFOL.Strategic.Profile.node (0 : Fin 4) true
      (.node 1 true (.leaf 0) (.leaf 2)) (.node 1 false (.leaf 1) (.leaf 2))
    KFOL.Strategic.IsSubgamePerfect p ∧ KFOL.Strategic.winner p = 1 :=
  KFOL.Strategic.off_path_equilibrium 0 1 2 (by decide) (by decide) (by decide)

#print axioms KFOL.Strategic.value_node
#print axioms KFOL.Strategic.spe_iff_gameTheory
#print axioms KFOL.Strategic.canForce_iff_value_singleton
