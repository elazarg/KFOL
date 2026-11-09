module

public import KFOL.Definitions.Rounds

/-! # Actual menu and winner restrictions of the scalar constructors -/

@[expose] public section

namespace KFOL.Rounds.Game

universe u
variable {Role : Type u}

/-- Exchanging the designated pair preserves the literal menu/winner restriction. -/
theorem UsesOnly.symm {game : Game Role} {a b : Role} (h : game.UsesOnly a b) :
    game.UsesOnly b a := by
  revert h
  induction game with
  | leaf who => exact Or.symm
  | round sizes next ih =>
    intro h
    exact ⟨(fun i hia hib => h.1 i hib hia),fun actions => ih actions (h.2 actions)⟩

variable [DecidableEq Role]

/-- Actual diagonal commitments activate only their designated pair. -/
theorem UsesOnly.diagonal {a b : Role} {left right : Game Role}
    (hl : left.UsesOnly a b) (hr : right.UsesOnly a b) :
    (diagonal a b left right).UsesOnly a b := by
  constructor
  · intro who ha hb
    simp [binarySizes,ha,hb]
  · intro actions
    dsimp only [diagonal]
    split
    · split
      · exact hl
      · exact Or.inr rfl
    · split
      · exact Or.inr rfl
      · exact hr

/-- A public choice by a member of the pair preserves its literal restriction. -/
theorem UsesOnly.publicChoice {a b owner : Role} (howner : owner = a ∨ owner = b)
    {left right : Game Role} (hl : left.UsesOnly a b) (hr : right.UsesOnly a b) :
    (publicChoice owner left right).UsesOnly a b := by
  constructor
  · intro who ha hb
    have hne : who ≠ owner := by
      rcases howner with rfl | rfl <;> assumption
    simp [hne]
  · intro actions
    dsimp only [publicChoice]
    split <;> assumption

/-- Every actual reciprocal game lies in the designated two-role fragment. -/
theorem usesOnly_reciprocal (a b : Role) (n : ℕ) : (reciprocal a b n).UsesOnly a b := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih => exact UsesOnly.diagonal ih (Or.inl rfl)

/-- Scalar syntax, including exchange and public extrema, realizes only games
with the designated pair's menus and winners. -/
theorem ScalarTerm.usesOnly_game (term : ScalarTerm) (a b : Role) :
    (term.game a b).UsesOnly a b := by
  induction term generalizing a b with
  | zero => exact Or.inr rfl
  | one => exact Or.inl rfl
  | diagonal left right hl hr => exact UsesOnly.diagonal (hl a b) (hr a b)
  | complement term ih => exact (ih b a).symm
  | sup left right hl hr => exact UsesOnly.publicChoice (Or.inl rfl) (hl a b) (hr a b)
  | inf left right hl hr => exact UsesOnly.publicChoice (Or.inr rfl) (hl a b) (hr a b)

/-- The diagonal constructor has actual Boolean commitments and preserves
Boolean menus throughout its independently occurring continuations. -/
theorem BooleanMenus.diagonal {a b : Role} {left right : Game Role}
    (hl : left.BooleanMenus) (hr : right.BooleanMenus) :
    (diagonal a b left right).BooleanMenus := by
  constructor
  · intro who
    simp only [binarySizes]
    split <;> omega
  · intro actions
    dsimp only [diagonal]
    split
    · split
      · exact hl
      · trivial
    · split
      · trivial
      · exact hr

/-- Public binary choice also stays within the literal Boolean menu fragment. -/
theorem BooleanMenus.publicChoice {owner : Role} {left right : Game Role}
    (hl : left.BooleanMenus) (hr : right.BooleanMenus) :
    (publicChoice owner left right).BooleanMenus := by
  constructor
  · intro who
    change (if who = owner then 1 else 0) ≤ 1
    split <;> omega
  · intro actions
    dsimp only [publicChoice]
    split <;> assumption

/-- Every reciprocal witness in the infinite family uses only Boolean menus. -/
theorem booleanMenus_reciprocal (a b : Role) (n : ℕ) :
    (reciprocal a b n).BooleanMenus := by
  induction n with
  | zero => trivial
  | succ n ih => exact BooleanMenus.diagonal ih trivial

/-- Every threshold witness of the no-finite-winner-algebra theorem uses only
Boolean menus, regardless of any additional inactive roles. -/
theorem booleanMenus_threshold (a b c : Role) (n m : ℕ) :
    (threshold a b c n m).BooleanMenus :=
  BooleanMenus.publicChoice (booleanMenus_reciprocal a b (n+1))
    (booleanMenus_reciprocal a c (m+1))

/-- The entire small scalar fragment uses literal Boolean commitments. -/
theorem ScalarTerm.booleanMenus_game (term : ScalarTerm) (a b : Role) :
    (term.game a b).BooleanMenus := by
  induction term generalizing a b with
  | zero => trivial
  | one => trivial
  | diagonal left right hl hr => exact BooleanMenus.diagonal (hl a b) (hr a b)
  | complement term ih => exact ih b a
  | sup left right hl hr => exact BooleanMenus.publicChoice (hl a b) (hr a b)
  | inf left right hl hr => exact BooleanMenus.publicChoice (hl a b) (hr a b)

end KFOL.Rounds.Game
