module

public import KFOL.Definitions.BichainEssential
public import KFOL.Definitions.Core
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum

/-! # The operation of a quantified Boolean formula

A prenex formula with a clausal matrix gives marked rows in the four-element
bichain, and the rows give one operation on winner sets: a baseline term in
owned choices, capped at one owner. These are the definitions; the proofs are
in `KFOL/Core/BichainQuantified.lean`, `BichainRecognition.lean` and
`QuantifiedRecognition.lean`.
-/

@[expose] public section
namespace KFOL.Bichain.Quantified

/-- Variables are the stages `1, …, n`. Stage `i` is existential when `ex i`
holds. A literal `(i, s)` says that variable `i` has value `s`. -/
structure Formula where
  n : ℕ
  ex : ℕ → Bool
  cls : List (List (ℕ × Bool))

/-- Input coordinates of the rows. -/
inductive Lab where
  | ch (i : ℕ) (s : Bool)
  | rl (i : ℕ)
  | perm (i : ℕ) (s : Bool)
  | lit (i : ℕ) (s : Bool)
  | kap (c : ℕ)
  deriving DecidableEq

/-- Branch and clause vertices are on the left, relays and literal resources
on the right. The vertices `br 0 s` and `relay 0` are the starting endpoints.
Stages after `n` step past one clause each. -/
inductive Vtx where
  | br (i : ℕ) (s : Bool)
  | relay (i : ℕ)
  | res (i : ℕ) (s : Bool)
  | cl (c : ℕ)
  deriving DecidableEq

variable (F : Formula)

/-- Every literal names one of the `n` variables. -/
def Formula.WF : Prop := ∀ C ∈ F.cls, ∀ l ∈ C, 1 ≤ l.1 ∧ l.1 ≤ F.n

/-- Truth of the matrix at an assignment. -/
def Matrix (α : ℕ → Bool) : Prop := ∀ C ∈ F.cls, ∃ l ∈ C, α l.1 = l.2

/-- Truth of the last `k` quantifiers and the matrix after stage `i`. -/
def sat : ℕ → ℕ → (ℕ → Bool) → Prop
  | 0, _, α => Matrix F α
  | k + 1, i, α =>
    if F.ex (i + 1) then ∃ s, sat k (i + 1) (Function.update α (i + 1) s)
    else ∀ s, sat k (i + 1) (Function.update α (i + 1) s)

/-- The labels whose rectangle contains a left vertex. -/
def inI : Vtx → Lab → Bool
  | .br i _, .ch j _ => j == i + 1
  | .br i _, .rl j => j == i
  | .br i s, .perm j t => j == i && t == s
  | .br i _, .kap c => i == F.n + c
  | .cl c, .lit j t => decide ((j, t) ∈ F.cls.getD c [])
  | _, _ => false

/-- The labels whose rectangle contains a right vertex. -/
def inJ : Vtx → Lab → Bool
  | .relay k, .ch j t => j == k + 1 && decide (j ≤ F.n) && (t || F.ex j)
  | .relay k, .rl j => j == k + 1
  | .relay k, .lit _ _ => decide (F.n ≤ k)
  | .relay k, .kap c => k == F.n + c
  | .res i s, .perm j t => j == i && t == s
  | _, _ => false

/-- The coordinate marked by a row. -/
def mark : Vtx → Lab
  | .br i s => if i ≤ F.n then .ch i (if F.ex i then s else true) else .kap (i - F.n - 1)
  | .relay i => .rl i
  | .res i s => .lit i s
  | .cl c => .kap c

/-- The rows of the instance. -/
def IsRow : Vtx → Prop
  | .br j s => (1 ≤ j ∧ j ≤ F.n) ∨ (F.n < j ∧ j < F.n + F.cls.length ∧ s = true)
  | .relay j => 1 ≤ j ∧ (j ≤ F.n ∨ j < F.n + F.cls.length)
  | .res j _ => 1 ≤ j ∧ j ≤ F.n
  | .cl c => c < F.cls.length

instance : DecidablePred (IsRow F) := fun z => by
  cases z <;> simp only [IsRow] <;> infer_instance

/-- Vertices with indices below a bound. -/
def vertices (N : ℕ) : Finset Vtx :=
  ((Finset.range N).image fun i => Vtx.br i true) ∪
  ((Finset.range N).image fun i => Vtx.br i false) ∪
  ((Finset.range N).image Vtx.relay) ∪
  ((Finset.range N).image fun i => Vtx.res i true) ∪
  ((Finset.range N).image fun i => Vtx.res i false) ∪
  ((Finset.range N).image Vtx.cl)

/-- The finite budget of all rows. -/
def allRows : Finset Vtx := (vertices (F.n + F.cls.length + 1)).filter (IsRow F)

/-- The coordinates of the instance. -/
def IsLab : Lab → Prop
  | .ch j _ => 1 ≤ j ∧ j ≤ F.n
  | .rl j => 1 ≤ j ∧ (j ≤ F.n ∨ j < F.n + F.cls.length)
  | .perm j _ => 1 ≤ j ∧ j ≤ F.n
  | .lit j _ => 1 ≤ j ∧ j ≤ F.n
  | .kap c => c < F.cls.length ∨ c = 0

instance : DecidablePred (IsLab F) := fun e => by
  cases e <;> simp only [IsLab] <;> infer_instance

/-- Coordinates with indices below a bound. -/
def coordinates (N : ℕ) : Finset Lab :=
  ((Finset.range N).image fun i => Lab.ch i true) ∪
  ((Finset.range N).image fun i => Lab.ch i false) ∪
  ((Finset.range N).image Lab.rl) ∪
  ((Finset.range N).image fun i => Lab.perm i true) ∪
  ((Finset.range N).image fun i => Lab.perm i false) ∪
  ((Finset.range N).image fun i => Lab.lit i true) ∪
  ((Finset.range N).image fun i => Lab.lit i false) ∪
  ((Finset.range N).image Lab.kap)

/-- The finite set of coordinates. -/
def labels : Finset Lab := (coordinates (F.n + F.cls.length + 1)).filter (IsLab F)

/-- The finite coordinate type. -/
abbrev FLab : Type := {e : Lab // e ∈ labels F}

/-- A left row is true on its labels and free elsewhere; a right row is false
on its labels and free elsewhere. -/
def rows (z : Vtx) (e : FLab F) : Value :=
  if mark F z = e.val then .possible else if inI F z e.val then .c
  else if inJ F z e.val then .b else .neutral

/-- Separation of a left vertex from a right vertex. -/
def cell (a b : Vtx) : CubeQuery (FLab F) :=
  .separate (fun e => inI F a e.val) (fun e => !inJ F b e.val)

end KFOL.Bichain.Quantified

namespace KFOL.Recognition

universe u v w

variable {Role : Type u} {Var : Type v}

open WinnerSet

/-- Attach the listed inputs one at a time by the same owner. -/
def foldSel {S : Type w} (r : Role) (ι : S → Var) (y : Term Role Var) (L : List S) :
    Term Role Var :=
  L.foldl (fun acc u => .choice r acc (.var (ι u))) y

/-- The union of a listed family of terms and a base term. -/
def bigUnion {ι : Type w} (three : Fin 3 ↪ Role) (L : List ι) (f : ι → Term Role Var)
    (base : Term Role Var) : Term Role Var :=
  L.foldr (fun i acc => .choice (three 2) (.choice (three 0) (f i) acc)
    (.choice (three 1) (f i) acc)) base

variable (three : Fin 3 ↪ Role) {Z : Type w} {W : Type w} [Fintype Z] [DecidableEq Z]
  [Fintype W] (rows : Z → W → Bichain.Value) (X Y : W → Bool) (z₀ : Z)

/-- Selector inputs, a padding input, and the inputs of the rows. -/
abbrev Inp (Z W : Type w) := Z ⊕ Option W

/-- A row with the padding input false. -/
def rowP (z : Z) : Option W → Bichain.Value
  | none => .b
  | some j => rows z j

/-- An endpoint with the padding input false. -/
def endP (X : W → Bool) : Option W → Bool
  | none => false
  | some j => X j

/-- Reset to the second owner when any selector is its atom. -/
noncomputable def KX (y : Term Role (Inp Z W)) : Term Role (Inp Z W) :=
  foldSel (three 1) Sum.inl y (Finset.univ : Finset Z).toList

/-- Reset to the third owner when any selector is its atom. -/
noncomputable def KY (y : Term Role (Inp Z W)) : Term Role (Inp Z W) :=
  foldSel (three 2) Sum.inl y (Finset.univ : Finset Z).toList

/-- Reset unless the selector of `z` is the only one at the second owner. -/
noncomputable def Kz (z : Z) (y : Term Role (Inp Z W)) : Term Role (Inp Z W) :=
  foldSel (three 1) Sum.inl (.choice (three 2) y (.var (.inl z)))
    ((Finset.univ : Finset Z).erase z).toList

/-- Supplies an input when a selector is neither atom. -/
def qT (p : Z × Option W) : Term Role (Inp Z W) :=
  .choice (three 2) (.choice (three 1) (.var (.inr p.2)) (.var (.inl p.1))) (.var (.inl p.1))

/-- Supplies an input when two selectors are at the second owner and one is not. -/
def u2T (p : Z × Z × Z × Option W) : Term Role (Inp Z W) :=
  if p.1 = p.2.1 then .var (.inl p.1) else
    .choice (three 1) (.choice (three 2) (.choice (three 2) (.var (.inr p.2.2.2))
      (.var (.inl p.1))) (.var (.inl p.2.1))) (.var (.inl p.2.2.1))

/-- Supplies an input on the code of the first endpoint. -/
noncomputable def kxT (p : Option W × Option W) : Term Role (Inp Z W) :=
  if endP X p.1 = true then KX three (.var (.inr p.1))
  else if endP X p.2 = true then KX three (.choice (three 2) (.var (.inr p.1)) (.var (.inr p.2)))
  else .var (.inl z₀)

/-- Supplies an input on the code of the second endpoint. -/
noncomputable def kyT (p : Option W × Option W) : Term Role (Inp Z W) :=
  if endP Y p.1 = false then KY three (.var (.inr p.1))
  else if endP Y p.2 = false then KY three (.choice (three 1) (.var (.inr p.1)) (.var (.inr p.2)))
  else .var (.inl z₀)

/-- Supplies an input on the code of a row, unless the row blocks it. -/
noncomputable def kzT (p : Z × Option W × Option W) : Term Role (Inp Z W) :=
  if rowP rows p.1 p.2.1 ≠ .possible then Kz three p.1 (.var (.inr p.2.1))
  else if rowP rows p.1 p.2.2 = .b then
    Kz three p.1 (.choice (three 1) (.var (.inr p.2.1)) (.var (.inr p.2.2)))
  else if rowP rows p.1 p.2.2 = .c then
    Kz three p.1 (.choice (three 2) (.var (.inr p.2.1)) (.var (.inr p.2.2)))
  else .var (.inl z₀)

/-- The baseline term: every row is isolated on its own selector code. -/
noncomputable def baseline : Term Role (Inp Z W) :=
  bigUnion three (Finset.univ : Finset Z).toList (fun u => .var (.inl u)) <|
  bigUnion three (Finset.univ : Finset (Z × Option W)).toList (qT three) <|
  bigUnion three (Finset.univ : Finset (Z × Z × Z × Option W)).toList (u2T three) <|
  bigUnion three (Finset.univ : Finset (Option W × Option W)).toList (kxT three X z₀) <|
  bigUnion three (Finset.univ : Finset (Option W × Option W)).toList (kyT three Y z₀) <|
  bigUnion three (Finset.univ : Finset (Z × Option W × Option W)).toList (kzT three rows z₀) <|
  .var (.inl z₀)

open Classical in
/-- The baseline capped at the first owner on the row inputs. -/
noncomputable def target (v : Inp Z W → WinnerSet Role) : WinnerSet Role :=
  if ∀ x : Option W, v (.inr x) = singleton (three 0) then singleton (three 0)
  else (baseline three rows X Y z₀).eval v

end KFOL.Recognition

namespace KFOL.Bichain.Quantified

universe u

variable {Role : Type u} (three : Fin 3 ↪ Role) (F : Formula) (α : ℕ → Bool)

/-- The rows of the formula and two unconstrained rows. -/
abbrev RowIx : Type := Bool ⊕ {z : Vtx // z ∈ allRows F}

instance : Nontrivial (RowIx F) := ⟨⟨.inl true, .inl false, by simp⟩⟩

/-- Every row of the formula, preceded by two rows without marks. -/
def paddedRows : RowIx F → FLab F → Value
  | .inl _ => fun _ => .neutral
  | .inr z => rows F z.val

/-- The inputs of the operation: one selector for each row, one padding
input, and the coordinates of the rows. -/
abbrev Input : Type := Recognition.Inp (RowIx F) (FLab F)

/-- The operation of a formula: a baseline term capped at the first owner. -/
noncomputable def operation : (Input F → WinnerSet Role) → WinnerSet Role :=
  Recognition.target three (paddedRows F) (fun e => inI F (.br 0 (α 0)) e.val)
    (fun e => !inJ F (.relay 0) e.val) (.inl true)

end KFOL.Bichain.Quantified
