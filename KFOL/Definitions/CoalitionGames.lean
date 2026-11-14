module

public import KFOL.Definitions.CoalitionMaps
public import KFOL.Definitions.Strategic

/-! # Recomputing equilibria after role coalescing

The relabelled game changes both terminal winners and decision owners.
Its possible winners are defined using independent full-profile SPE.
-/

@[expose] public section

namespace KFOL.Strategic.Tree

universe u v

/-- Replace every owner and terminal winner by its team label. -/
def mapRoles {Role : Type u} {Team : Type v} (f : Role → Team) : Tree Role → Tree Team
  | .leaf r => .leaf (f r)
  | .node r g h => .node (f r) (mapRoles f g) (mapRoles f h)

end KFOL.Strategic.Tree

namespace KFOL.CoalitionMaps

universe u v

/-- Equal old equilibrium-winner observations remain equal when the roles
are coalesced and equilibria are recomputed. -/
def GameDescends {Role : Type u} {Team : Type v} (f : Role → Team) : Prop :=
  ∀ G H : Strategic.Tree Role,
    Strategic.possibleWinners G = Strategic.possibleWinners H →
    Strategic.possibleWinners (G.mapRoles f) = Strategic.possibleWinners (H.mapRoles f)

end KFOL.CoalitionMaps
