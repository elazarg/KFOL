module

public import KFOL.Definitions.Public
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Set.Function
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi

/-! # Direct tests for simultaneous core interpolation

Rows prescribe allowed winner sets, singleton demands and an optional positive
membership. The peeling test uses only the input columns and deletes one
constrained row at every recursive call. It has no auxiliary clause family,
term witness or saturation operator.
-/

@[expose] public section

namespace KFOL.Core.Interpolation

universe u v w
variable {Role : Type u} {Row : Type v} {Var : Type w}

/-- Singleton values required at the specified rows. -/
def Atomic (D : Finset (Row × Role)) (x : Row → WinnerSet Role) : Prop :=
  ∀ d ∈ D, x d.1 = WinnerSet.singleton d.2

/-- One requested winner membership, or no positive request. -/
def Positive (p : Option (Row × Role)) (x : Row → WinnerSet Role) : Prop :=
  match p with
  | none => True
  | some (q, k) => k ∈ (x q).val

/-- Upper bounds at the constrained rows. -/
def Bounded (N : Finset Row) (U : Row → Set Role) (x : Row → WinnerSet Role) : Prop :=
  ∀ i ∈ N, (x i).val ⊆ U i

def Fits (N : Finset Row) (U : Row → Set Role)
    (D : Finset (Row × Role)) (p : Option (Row × Role)) (x : Row → WinnerSet Role) : Prop :=
  Bounded N U x ∧ Atomic D x ∧ Positive p x

/-- No two demands in a rainbow ask for the same owner. -/
def Rainbow (D : Finset (Row × Role)) : Prop := Set.InjOn Prod.snd (D : Set (Row × Role))

/-- The common-source condition and the two ways to retain a positive winner,
expressed for an arbitrary collection of possible input columns. -/
def ProfileCondition (G : Finset (Row × Role) → Option (Row × Role) → Prop)
    (D : Finset (Row × Role)) (p : Option (Row × Role)) : Prop :=
  (∀ S, S ⊆ D → Rainbow S → G S none) ∧
    match p with
    | none => True
    | some (q, k) => G ∅ p ∧
        ∀ d ∈ D, d.2 ≠ k → ∃ s, s ≠ d.2 ∧ G {d} (some (q, s))

variable [DecidableEq Row] [DecidableEq Role]

/-- A direct hereditary condition on the given row bounds. A boundary option
turns a constrained row into a singleton demand and removes its upper bound.
The profile condition only makes rainbow or single-demand challenges. -/
def Peels (values : Row → Var → WinnerSet Role) (U : Row → Set Role)
    (N : Finset Row) (D : Finset (Row × Role)) (p : Option (Row × Role)) : Prop :=
  let step := fun E o =>
    (∃ j, Fits N U E o (fun i => values i j)) ∨
      ∃ i, ∃ _hi : i ∈ N, ∃ r ∈ U i, Peels values U (N.erase i) (insert (i, r) E) o
  ProfileCondition step D p
termination_by N.card
decreasing_by exact Finset.card_erase_lt_of_mem _hi

/-- Recognize an exact value table by its allowed values and one positive
query per requested membership. Empty rows are rejected by the same test. -/
def Recognizes [Fintype Row] (values : Row → Var → WinnerSet Role)
    (U : Row → Set Role) : Prop :=
  Peels values U Finset.univ ∅ none ∧
    ∀ q k, k ∈ U q → Peels values U Finset.univ ∅ (some (q, k))

/-- Apply the hereditary test to the entire value table of an operation. -/
noncomputable def RecognizesOperation [Fintype Role] [Fintype Var]
    (f : (Var → WinnerSet Role) → WinnerSet Role) : Prop := by
  classical
  let _ : Fintype (WinnerSet Role) := Fintype.ofFinite (WinnerSet Role)
  exact Recognizes (fun v j => v j) (fun v => (f v).val)

end KFOL.Core.Interpolation
