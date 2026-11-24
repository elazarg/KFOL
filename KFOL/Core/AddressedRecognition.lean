module

public import KFOL.Core.AddressedTableConstruction
public import KFOL.Core.AddressedPadding
public import KFOL.Core.AddressedSourceTable

/-! # Recognition of the addressed table of a rectangle

The two padded groups have nonempty budgets, so the side envelopes are
defined even for a losing rectangle. The resulting table is a core
operation exactly when its original rectangle admits a pure separator.
-/

@[expose] public section
namespace KFOL.Core.AddressedRecognition

open AddressedRails AddressedRectangle AddressedLogicalGroups AddressedTableExtraction
open AddressedTableConstruction AddressedPadding ProfileBudgets WinnerSet Bichain
open scoped Classical
attribute [local instance] Equational.coreStructure

variable {Role Label Track Bit Row : Type*} [DecidableEq Role] {B : Book Label Track Bit}

def sideEndpoint (side : Bool) (x y : Label → Bool) : Label ⊕ Bool → Bool :=
  if side then extendEndpoint x else fun f => !(extendEndpoint y f)

theorem side_possible [Fintype Label] (three : Fin 3 ↪ Role) (R : Rows B Row)
    (S : Finset Row) (side : Bool) (x y : Label → Bool) :
    ∃ t, Good three (extendRows R) S side (sideEndpoint side x y) t := by
  apply exists_good
  · exact ⟨.inr side, by cases side <;> rfl⟩
  · intro z _ hz
    exact ⟨.inr side, (show side = R.left z from hz.symm)⟩

variable [Fintype Role] [Fintype Label]

/-- A representative word for the pointwise largest side group. Its value
is computed from the explicit budgets, with no search for this word. -/
noncomputable def group (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (side : Bool) (x y : Label → Bool) : CoreTerm Role (Label ⊕ Bool) :=
  (exists_envelope three (extendRows R) S side _ (side_possible three R S side x y)).choose

theorem group_spec (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (side : Bool) (x y : Label → Bool) :
    Envelope three (extendRows R) S side (sideEndpoint side x y) (group three R S side x y) :=
  (exists_envelope three _ _ _ _ (side_possible three R S side x y)).choose_spec.1

/-- Explicit evaluation of the group word terminates after at most one
Horn sweep per logical label. -/
theorem group_mem (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row) (side : Bool)
    (x y : Label → Bool) (v : Label ⊕ Bool → WinnerSet Role) (k : Role) :
    let r := orient three side 0
    let pool := (OneOwnerSelector.eligible r k v).toFinset
    let budgets := bounds three (extendRows R) S side
      (if side then extendEndpoint x else fun f => !(extendEndpoint y f))
    k ∈ ((group three R S side x y).realize v).val ↔
      ∃ f ∈ OneOwnerSelector.sweeps budgets r pool.card pool, k ∈ (v f).val := by
  let r := orient three side 0
  let b := bounds three (extendRows R) S side (sideEndpoint side x y)
  let D := OneOwnerSelector.eligible r k v
  let pool := D.toFinset
  have eq := OneOwnerSelector.sweeps_eq_greatest b r pool.card pool le_rfl
  change (_ : Set (Label ⊕ Bool)) = _ at eq
  have formula := (exists_envelope three _ _ _ _ (side_possible three R S side x y)).choose_spec.2 v k
  change _ ↔ ∃ f ∈ OneOwnerSelector.sweeps b r pool.card pool, k ∈ (v f).val
  have supports : (OneOwnerSelector.sweeps b r pool.card pool : Set (Label ⊕ Bool)) = greatestSupport b r D := by
    simpa only [pool, Set.coe_toFinset] using eq
  change _ ↔ ∃ f ∈ (OneOwnerSelector.sweeps b r pool.card pool : Set (Label ⊕ Bool)), k ∈ (v f).val
  rw [supports]
  exact formula

variable [Fintype Bit] [Nonempty Bit]

/-- The full table accepts one retained selector and the rails of the
original and two private tracks. Its group entries are given by group_mem. -/
noncomputable def table (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (x y : Label → Bool) (v : Option (Rail (Track ⊕ Bool) Bit) → WinnerSet Role) : WinnerSet Role :=
  AddressedTableExtraction.operation three (extendBook B) (group three R S true x y)
    (group three R S false x y) (v none) (fun i => v (some i))

variable [DecidableEq Row] [Fintype Track] [Nontrivial Bit]

/-- A pure separator of the raw rectangle exists exactly when the complete
table of its padded rail construction has a realizing core word. -/
theorem table_iff_no_cut (three : Fin 3 ↪ Role) (R : Rows B Row) (S : Finset Row)
    (x y : Label → Bool) (hx : B.Sparse {f | x f = true}) (hy : B.SparseOrFull {f | y f = false}) :
    (∃ t : CoreTerm Role (Option (Rail (Track ⊕ Bool) Bit)),
      ∀ v, t.realize v = table three R S x y v) ↔ ¬ CubeCut R.cube S (.separate x y) := by
  let R' := extendRows R
  let x' := extendEndpoint x
  let y' := extendEndpoint y
  let l := group three R S true x y
  let r := group three R S false x y
  have el : Envelope three R' S true x' l := group_spec three R S true x y
  have er : Envelope three R' S false (fun f => !(y' f)) r := group_spec three R S false x y
  constructor
  · rintro ⟨t,ht⟩ cut
    have leftWin : profile (three 0) x' l = true := by simpa using el.1.1
    have rightWin : profile (three 1) (fun f => !(y' f)) r = true := by simpa using er.1.1
    have losses (z : Row) (hz : z ∈ S) : three 2 ∉
        ((if R'.left z then l else r).realize (rawValues three R' z)).val := by
      by_cases side : R'.left z = true
      · simpa only [side, ite_true] using el.1.2 z hz side
      · simpa only [ite_eq_right side] using er.1.2 z hz (Bool.eq_false_of_not_eq_true side)
    obtain ⟨g,quiet,demand⟩ := extract_of_group_losses three (extendBook B) R' S x' y' l r leftWin rightWin
      (fun z hz => ⟨three 2,primary_ne_aux three _,losses z hz⟩) t (fun z v => ht (fun j => j.elim z v))
    apply R'.no_word_of_rectangle_cut three (cut_extendRows R cut) _ _ g quiet demand
    · convert sparse_extend B true hx using 1
      ext f; cases f <;> rfl
    · convert sparseOrFull_extend B false hy using 1
      ext f; cases f <;> rfl
  · intro noCut
    rw [cubeCut_iff] at noCut
    push Not at noCut
    obtain ⟨q,pure,quiet,fits⟩ := noCut
    let p := q.map (Sum.inl : Label → Label ⊕ Bool)
    have pPure : p.IsPure := Recognition.PureTerm.map_isPure _ _ pure
    have pQuiet (z : Row) (hz : z ∈ S) : p.eval (R'.cube z) ≠ .possible := by
      simpa only [p, R', Recognition.PureTerm.eval_map, cube_extend, extendRow] using quiet z hz
    have pFits : (CubeQuery.separate x' y').Holds p := by
      change (p.eval _ = _ ∧ p.eval _ = _)
      simpa only [p, Recognition.PureTerm.eval_map, x',y',extendEndpoint, Sum.elim_inl, CubeQuery.Holds] using fits
    obtain ⟨w,wl,wr⟩ := good_of_pure three R' S x' y' p pPure pQuiet pFits
    obtain ⟨g,gl,gr,all⟩ := pad_witness three R' S x' y' (.inr false) rfl
      (fun z _ eq => by change Sum.inr false = Sum.inl (R.mark z) at eq; cases eq) (fun _ _ side => side.symm)
      (fun _ _ side => ⟨.inr true,side.symm⟩) w wl wr
    obtain ⟨t,ht⟩ := realize_target three R' S x' y' l r g el er gl gr all
    refine ⟨t,fun v => ?_⟩
    have eta : (fun j : Option (Rail (Track ⊕ Bool) Bit) => j.elim (v none) (fun i => v (some i))) = v := by
      funext j; cases j <;> rfl
    simpa only [eta, table, l, r] using ht (v none) (fun i => v (some i))

end KFOL.Core.AddressedRecognition
