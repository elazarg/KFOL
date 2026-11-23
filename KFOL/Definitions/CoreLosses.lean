module

public import KFOL.Definitions.CoreNormalForm
public import KFOL.Definitions.QuantifiedRecognition

/-! # Losses of an operation at its sources

A loss is a list of postings of atoms at inputs. An operation has a system of
losses when a winner of the output is always supplied by an input holding it,
and an input fails to supply an observer exactly when one of its listed losses
is posted and does not name the observer. The losses of the operation of a
family of marked rows are listed explicitly.
-/

@[expose] public section

namespace KFOL.Core.Sources

universe u v
variable {Role : Type u} {Var : Type v}

/-- A loss is posted for an observer when no posting names the observer and
every posted input is the posted atom. -/
def Posted (z : List (Var × Role)) (k : Role) (v : Var → WinnerSet Role) : Prop :=
  ∀ q ∈ z, q.2 ≠ k ∧ v q.1 = WinnerSet.singleton q.2

/-- The same condition on the passive statuses away from a source. -/
def PostedAt (z : List (Var × Role)) (k : Role) (j : Var) (p : Pattern k j) : Prop :=
  ∀ q ∈ z, ∃ (hi : q.1 ≠ j) (hr : q.2 ≠ k), p ⟨q.1, hi⟩ = .atom ⟨q.2, hr⟩

/-- The sources of an operation fail exactly on the listed losses. No loss
posts at its own source or posts two atoms at one input. -/
structure LossSystem (f : (Var → WinnerSet Role) → WinnerSet Role)
    (zeros : Var → List (List (Var × Role))) : Prop where
  mem_iff : ∀ v k, k ∈ (f v).val ↔ ∃ j, k ∈ (v j).val ∧ ∀ z ∈ zeros j, ¬Posted z k v
  off_source : ∀ j, ∀ z ∈ zeros j, ∀ q ∈ z, q.1 ≠ j
  functional : ∀ j, ∀ z ∈ zeros j, ∀ q ∈ z, ∀ q' ∈ z, q.1 = q'.1 → q.2 = q'.2

/-- A guard excludes one of the postings of a loss. -/
def Meets {k : Role} {j : Var} (g : Guard k j) (z : List (Var × Role)) : Prop :=
  ∃ a ∈ g, (a.1.val, a.2.val) ∈ z

/-- A guard meets every loss that does not name the observer. -/
def MeetsAll {k : Role} {j : Var} (zeros : List (List (Var × Role))) (g : Guard k j) : Prop :=
  ∀ z ∈ zeros, (∀ q ∈ z, q.2 ≠ k) → Meets g z

end KFOL.Core.Sources

namespace KFOL.Recognition

universe u w

variable {Role : Type u} (three : Fin 3 ↪ Role) {Z : Type w} {W : Type w} [Fintype Z]
  [DecidableEq Z] [Fintype W] (rows : Z → W → Bichain.Value) (X Y : W → Bool)

/-- Every row input at the first owner: the loss of a selector. -/
noncomputable def lossCap : List (Inp Z W × Role) :=
  (Finset.univ : Finset (Option W)).toList.map fun x => (.inr x, three 0)

/-- The code of the first endpoint with the endpoint at the third owner. -/
noncomputable def lossX : List (Inp Z W × Role) :=
  ((Finset.univ : Finset Z).toList.map fun u => (.inl u, three 2)) ++
    ((Finset.univ : Finset (Option W)).toList.filter fun x => endP X x).map
      fun x => (.inr x, three 2)

/-- The code of the second endpoint with its complement at the second owner. -/
noncomputable def lossY : List (Inp Z W × Role) :=
  ((Finset.univ : Finset Z).toList.map fun u => (.inl u, three 1)) ++
    ((Finset.univ : Finset (Option W)).toList.filter fun x => !endP Y x).map
      fun x => (.inr x, three 1)

open Classical in
/-- The code of a row with the fixed inputs of the row at their atoms. -/
noncomputable def lossRow (z : Z) : List (Inp Z W × Role) :=
  ((Finset.univ : Finset Z).toList.map fun u =>
      (.inl u, if u = z then three 1 else three 2)) ++
    (((Finset.univ : Finset (Option W)).toList.filter fun x =>
      decide (rowP rows z x = .b)).map fun x => (.inr x, three 1)) ++
    (((Finset.univ : Finset (Option W)).toList.filter fun x =>
      decide (rowP rows z x = .c)).map fun x => (.inr x, three 2))

open Classical in
/-- The losses of the operation of the rows at each input. -/
noncomputable def losses : Inp Z W → List (List (Inp Z W × Role))
  | .inl _ => [lossCap three]
  | .inr x =>
    (if endP X x then [] else [lossX three X]) ++
    (if endP Y x then [lossY three Y] else []) ++
    ((Finset.univ : Finset Z).toList.filter fun z =>
      decide (rowP rows z x = .possible)).map (lossRow three rows)

end KFOL.Recognition
