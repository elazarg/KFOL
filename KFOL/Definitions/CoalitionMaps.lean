module

public import KFOL.Definitions.Public

/-! # When a map of roles acts on winner values

A role map changes every owner's objective as well as terminal winners.
Descent asks independently whether one map of winner values commutes with
all owned choices and sends each winner atom to the renamed atom.
-/

@[expose] public section

namespace KFOL.CoalitionMaps

universe u v

variable {Role : Type u} {Team : Type v}

/-- The direct image of a nonempty winner set. -/
def image (f : Role → Team) (A : WinnerSet Role) : WinnerSet Team :=
  ⟨f '' A.val, A.property.image f⟩

/-- A value map interprets all atoms and all owner-indexed choices. -/
def Intertwines (f : Role → Team) (h : WinnerSet Role → WinnerSet Team) : Prop :=
  (∀ r, h (WinnerSet.singleton r) = WinnerSet.singleton (f r)) ∧
  ∀ r A B, h (WinnerSet.choice r A B) =
    WinnerSet.choice (f r) (h A) (h B)

/-- Role coalescing has an interpretation on the existing winner carrier. -/
def Descends (f : Role → Team) : Prop := ∃ h, Intertwines f h

/-- All roles form one team. -/
def IsConstant (f : Role → Team) : Prop := ∃ q, ∀ r, f r = q

/-- One role is alone in one team, and every other role joins the other. -/
def HasSingletonBlock (f : Role → Team) : Prop :=
  ∃ c q, f c ≠ q ∧ ∀ r, r ≠ c → f r = q

/-- The explicit three possibilities in the descent classification. -/
def Admissible (f : Role → Team) : Prop :=
  Function.Injective f ∨ IsConstant f ∨ HasSingletonBlock f

/-- The exceptional two-team quotient observes only the singleton role's
forced win. Its value need not be the direct image of the original value. -/
noncomputable def collapse (c : Role) (q s : Team) (A : WinnerSet Role) : WinnerSet Team :=
  if A = WinnerSet.singleton c then WinnerSet.singleton s else WinnerSet.singleton q

end KFOL.CoalitionMaps
