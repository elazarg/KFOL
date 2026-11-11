module

public import KFOL.Definitions.Strategic
public import KFOL.Definitions.Counting

/-! # Syntax size of public game trees -/

@[expose] public section

namespace KFOL.Strategic.Tree

universe u
variable {Role : Type u}

/-- Number of individual binary decisions, counting repeated subtrees again. -/
def choiceCount : Tree Role → ℕ
  | .leaf _ => 0
  | .node _ g h => g.choiceCount + h.choiceCount + 1

/-- The same public game as a closed algebraic term. -/
def toTerm : Tree Role → Term Role Empty
  | .leaf r => .winner r
  | .node r g h => .choice r g.toTerm h.toTerm

/-- Absorbing decisions, evaluated with the actual SPE values of the subgames. -/
noncomputable def absorbingCount (g : Tree Role) : ℕ :=
  g.toTerm.absorbingCount Empty.elim

end KFOL.Strategic.Tree
