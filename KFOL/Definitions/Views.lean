module

public import KFOL.Definitions.Core

/-!
# Player observations and their quotient operations

A player's view records possible membership, any other player's singleton,
or ambiguity omitting the observer. These observations are defined directly
from winner sets, independently of term evaluation or contextual equivalence.
-/

@[expose] public section

namespace KFOL

universe u v

/-- Three kinds of view; `other` excludes the observing player. -/
inductive PlayerView {Role : Type u} (k : Role) where
  | possible
  | other (r : {r : Role // r ≠ k})
  | impossible

namespace WinnerSet

variable {Role : Type u}

/-- The membership bit and every other player's singleton test. -/
def SameView (k : Role) (A B : WinnerSet Role) : Prop :=
  (k ∈ A.val ↔ k ∈ B.val) ∧
    ∀ r, r ≠ k → (A = singleton r ↔ B = singleton r)

/-- Directly inspect a nonempty set, without evaluating any term. -/
noncomputable def view (k : Role) (A : WinnerSet Role) : PlayerView k := by
  classical
  exact if hk : k ∈ A.val then .possible
    else if h : ∃ r, A = singleton r then
      .other ⟨h.choose, fun he => hk
        ((congrArg (fun B : WinnerSet Role => k ∈ B.val) h.choose_spec).mpr he.symm)⟩
    else .impossible

end WinnerSet

namespace PlayerView

variable {Role : Type u} {Var : Type v}

/-- Canonical representatives: the observer's singleton, another singleton,
or the complement of the observer. With three roles the complement is
ambiguous, as established in the proof module. -/
noncomputable def representative (three : Fin 3 ↪ Role) (k : Role) :
    PlayerView k → WinnerSet Role
  | .possible => WinnerSet.singleton k
  | .other r => WinnerSet.singleton r.val
  | .impossible => ⟨{r | r ≠ k}, by
      have h01 := three.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
      by_cases h : three 0 = k
      · exact ⟨three 1, fun he => h01 (h.trans he.symm)⟩
      · exact ⟨three 0, h⟩⟩

/-- Interpret a term on canonical representatives and then observe its result.
The homomorphism theorem requires public syntax or idempotency; this definition
makes no assertion that arbitrary role switches preserve one player's view. -/
noncomputable def eval (three : Fin 3 ↪ Role) (k : Role)
    (t : Term Role Var) (v : Var → PlayerView k) : PlayerView k :=
  WinnerSet.view k (t.eval (fun x => representative three k (v x)))

end PlayerView
end KFOL
