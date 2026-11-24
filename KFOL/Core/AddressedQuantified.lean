module

public import KFOL.Core.AddressedRectangle
public import KFOL.Core.BichainQuantified
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Fintype.EquivFin
public import KFOL.Core.AddressSize
public import KFOL.Core.ThreeSlotQuantified
public import KFOL.Core.AddressedPadding
public import KFOL.Core.BichainRecognition

/-! # Addressed physical observations of a quantified formula

The rows here are the vertices of the quantified-cube reduction. Literal
addresses can occupy an entire track at a final right relay. The other
side needs at most one label per track. The transport therefore applies
to the cut furnished by a false formula without changing its rows.
-/

@[expose] public section
namespace KFOL.Core.AddressedQuantified

open Bichain Bichain.Quantified AddressedRails AddressedRectangle ProfileBudgets
attribute [local instance] Equational.coreStructure

abbrev Row (F : Formula) := {z : Vtx // z ∈ allRows F}

def isLeft : Vtx → Bool
  | .br _ _ | .cl _ => true
  | .relay _ | .res _ _ => false

def posted (F : Formula) (z : Vtx) : Set (FLab F) :=
  {e | (if isLeft z then inI F z e.val else inJ F z e.val) = true}

theorem mark_valid (F : Formula) (z : Row F) : mark F z.val ∈ labels F := by
  apply mem_labels_of_isLab
  obtain ⟨v, hv⟩ := z
  have h := (mem_allRows F v).1 hv
  cases v with
  | br i s =>
    simp only [IsRow] at h
    by_cases early : i ≤ F.n
    · simp [mark, early, IsLab]
      omega
    · simp [mark, early, IsLab]
      omega
  | relay i => simpa [mark, IsLab, IsRow] using h
  | res i s => simpa [mark, IsLab, IsRow] using h
  | cl c => exact Or.inl h

def rowMark (F : Formula) (z : Row F) : FLab F := ⟨mark F z.val, mark_valid F z⟩

private theorem no_left_of_right (F : Formula) (z : Vtx) (e : Lab)
    (right : isLeft z = false) : inI F z e = false := by
  cases z <;> cases e <;> simp_all [isLeft, inI]

private theorem no_right_of_left (F : Formula) (z : Vtx) (e : Lab)
    (left : isLeft z = true) : inJ F z e = false := by
  cases z <;> cases e <;> simp_all [isLeft, inJ]

variable {Track Bit Role : Type*}

/-- The coloring conditions use literal and ordinary tracks separately.
They apply at the starting vertices as well as the vertices of rows. -/
structure Geometry (F : Formula) (B : Book (FLab F) Track Bit) : Prop where
  sparseLeft : ∀ z, isLeft z = true → B.Sparse (posted F z)
  sparseRight : ∀ z, isLeft z = false → B.SparseOrFull (posted F z)
  apart : ∀ (z : Row F) (e : FLab F), e ∈ posted F z.val → B.track e ≠ B.track (rowMark F z)

namespace Geometry

variable {F : Formula} {B : Book (FLab F) Track Bit} (G : Geometry F B)

def rectangle : Rows B (Row F) where
  left z := isLeft z.val
  mark := rowMark F
  posted z := posted F z.val
  sparseLeft z := G.sparseLeft z.val
  sparseRight z := G.sparseRight z.val
  apart := G.apart

/-- On every actual quantified row the addressed rectangle uses the original
four-state cube, including its one possible mark. -/
theorem cube_eq (z : Row F) : G.rectangle.cube z = rows F z.val := by
  classical
  funext e
  have markEq : e = rowMark F z ↔ mark F z.val = e.val := by
    constructor
    · intro eq
      exact (congrArg Subtype.val eq).symm
    · intro eq
      exact Subtype.ext eq.symm
  simp only [Rows.cube, rectangle, markEq]
  by_cases marked : mark F z.val = e.val
  · simp [marked, rows]
  · by_cases side : isLeft z.val = true
    · have missing := no_right_of_left F z.val e.val side
      simp [rows, marked, posted, side, missing]
    · have right := Bool.eq_false_of_not_eq_true side
      have missing := no_left_of_right F z.val e.val right
      simp [rows, marked, posted, right, missing]

def initialLeft (F : Formula) (α : ℕ → Bool) (e : FLab F) : Bool :=
  inI F (.br 0 (α 0)) e.val

def initialRight (F : Formula) (e : FLab F) : Bool :=
  !inJ F (.relay 0) e.val

/-- The subtype of genuine row vertices carries precisely the native QBF
cut. Changing the row type introduces no relaxation of its obligations. -/
theorem cut_iff_not_sat (hwf : F.WF) (α : ℕ → Bool) :
    CubeCut G.rectangle.cube Finset.univ (.separate (initialLeft F α) (initialRight F)) ↔
      ¬ sat F F.n 0 α := by
  classical
  rw [← Bichain.Quantified.cut_iff_not_sat F hwf α, cubeCut_iff, cubeCut_iff]
  constructor
  · intro cut t ht safe fits
    apply cut t ht _ fits
    intro z _
    simpa only [G.cube_eq] using safe z.val z.property
  · intro cut t ht safe fits
    apply cut t ht _ fits
    intro z hz
    simpa only [G.cube_eq] using safe (⟨z, hz⟩ : Row F) (Finset.mem_univ _)

variable [DecidableEq Role] [Nontrivial Bit] [Fintype Track] [Fintype Bit]

/-- Falsity of the quantified formula rules out a physical word on its rails
at all permanent probes and copies of its rows. Only the incidence coloring
of the addresses is assumed. -/
theorem no_word_of_not_sat (three : Fin 3 ↪ Role) (hwf : F.WF) (α : ℕ → Bool)
    (no : ¬ sat F F.n 0 α) :
    ∀ t : CoreTerm Role (Rail Track Bit),
      (G.rectangle.encoding three).Quiet Finset.univ t →
        ¬ (G.rectangle.encoding three).Demands (initialLeft F α) (initialRight F) t := by
  classical
  apply G.rectangle.no_word_of_rectangle_cut three ((G.cut_iff_not_sat hwf α).mpr no)
  · exact G.sparseLeft (.br 0 (α 0)) rfl
  · simpa [posted, isLeft, initialRight] using G.sparseRight (.relay 0) rfl

omit [Nontrivial Bit] [Fintype Track] [Fintype Bit] in
/-- The logical separator obtained from a true formula still works when the
two private labels are added: relabel its variables into the original summand. -/
theorem padded_separator_of_sat (hwf : F.WF) (α : ℕ → Bool) (yes : sat F F.n 0 α) :
    let R := AddressedPadding.extendRows G.rectangle
    let x := AddressedPadding.extendEndpoint (initialLeft F α)
    let y := AddressedPadding.extendEndpoint (initialRight F)
    ∃ q : Bichain.Term (FLab F ⊕ Bool), q.IsPure ∧
      (∀ z ∈ (Finset.univ : Finset (Row F)), q.eval (R.cube z) ≠ .possible) ∧
      (CubeQuery.separate x y).Holds q := by
  classical
  obtain ⟨q, pure, quiet, fit⟩ := (sat_iff_separator F hwf α).mp yes
  refine ⟨q.map Sum.inl, Recognition.PureTerm.map_isPure _ _ pure, ?_, ?_⟩
  · intro z _
    rw [Recognition.PureTerm.eval_map, AddressedPadding.cube_extend]
    simpa only [AddressedPadding.extendRow, G.cube_eq] using quiet z.val z.property
  · obtain ⟨left, right⟩ := fit
    exact ⟨(Recognition.PureTerm.eval_map _ _ _).trans left,
           (Recognition.PureTerm.eval_map _ _ _).trans right⟩

/-- The actual QBF cut also obstructs all words after the two private tracks
and their static probes have been added. -/
theorem padded_no_word_of_not_sat (three : Fin 3 ↪ Role) (hwf : F.WF) (α : ℕ → Bool)
    (no : ¬ sat F F.n 0 α) :
    let R := AddressedPadding.extendRows G.rectangle
    let x := AddressedPadding.extendEndpoint (initialLeft F α)
    let y := AddressedPadding.extendEndpoint (initialRight F)
    ∀ t : CoreTerm Role (Rail (Track ⊕ Bool) Bit), (R.encoding three).Quiet Finset.univ t →
      ¬ (R.encoding three).Demands x y t := by
  classical
  apply (AddressedPadding.extendRows G.rectangle).no_word_of_rectangle_cut three
    (AddressedPadding.cut_extendRows G.rectangle ((G.cut_iff_not_sat hwf α).mpr no))
  · have eq : {f | AddressedPadding.extendEndpoint (initialLeft F α) f = true} =
        AddressedPadding.extendSet (posted F (.br 0 (α 0))) true := by
      ext f
      cases f <;> rfl
    rw [eq]
    exact AddressedPadding.sparse_extend B _ (G.sparseLeft _ rfl)
  · have eq : {f | AddressedPadding.extendEndpoint (initialRight F) f = false} =
        AddressedPadding.extendSet (posted F (.relay 0)) false := by
      ext f
      cases f with
      | inl f => simp [AddressedPadding.extendEndpoint, AddressedPadding.extendSet, initialRight, posted, isLeft]
      | inr b => rfl
    rw [eq]
    exact AddressedPadding.sparseOrFull_extend B _ (G.sparseRight _ rfl)

end Geometry


/-- Three literal slots suffice for clauses of width at most three after
introducing copies. The remaining nine tracks are independent of the formula. -/
inductive Palette (C : Type*) where
  | branch (parity : Fin 2) (sign : Bool)
  | relay (parity : Fin 2)
  | permanent
  | literal (slot : C)
  | clause (parity : Fin 2)
  deriving DecidableEq, Fintype

def parity (i : ℕ) : Fin 2 := ⟨i % 2, Nat.mod_lt _ (by decide)⟩

def paint {C : Type*} (slot : ℕ → C) : Lab → Palette C
  | .ch i s => .branch (parity i) s
  | .rl i => .relay (parity i)
  | .perm _ _ => .permanent
  | .lit i _ => .literal (slot i)
  | .kap i => .clause (parity i)

/-- Distinct signed literals from one clause have distinct slots. -/
def SeparatedClauses {C : Type*} (F : Formula) (slot : ℕ → C) : Prop :=
  ∀ c, ∀ p ∈ F.cls.getD c [], ∀ q ∈ F.cls.getD c [], slot p.1 = slot q.1 → p = q

variable {C : Type*}

private theorem left_unique {F : Formula} {slot : ℕ → C} (sep : SeparatedClauses F slot)
    {z : Vtx} {f h : Lab} (hf : inI F z f = true) (hh : inI F z h = true)
    (same : paint slot f = paint slot h) : f = h := by
  cases z <;> cases f <;> cases h <;> simp_all [inI, paint]
  rename_i c j s k t
  have eq := sep c (j, s) hf (k, t) hh same
  exact Prod.mk.inj eq

private def Wild (F : Formula) {C : Type*} : Vtx → Palette C → Prop
  | .relay k, .literal _ => F.n ≤ k
  | _, _ => False

private theorem right_unique {F : Formula} {slot : ℕ → C} {z : Vtx} {f h : Lab}
    (hf : inJ F z f = true) (hh : inJ F z h = true)
    (narrow : ¬ Wild F z (paint slot f)) (same : paint slot f = paint slot h) : f = h := by
  cases z <;> cases f <;> cases h <;> simp_all [inJ, paint, Wild]

private theorem all_posted {F : Formula} {slot : ℕ → C} {z : Vtx} {f : Lab}
    (full : Wild F z (paint slot f)) : inJ F z f = true := by
  cases z <;> cases f <;> simp_all [inJ, paint, Wild]

private theorem mark_apart {F : Formula} {slot : ℕ → C} (z : Vtx) (hz : IsRow F z)
    (f : Lab) (hf : (if isLeft z then inI F z f else inJ F z f) = true) :
    paint slot f ≠ paint slot (mark F z) := by
  cases z with
  | br i s =>
    by_cases early : i ≤ F.n
    · simp only [mark, ite_eq_left early]
      cases f <;> simp_all [IsRow, isLeft, inI, paint, parity, Fin.ext_iff]
      omega
    · simp only [mark, ite_eq_right early]
      cases f <;> simp [paint, parity, Fin.ext_iff]
      simp [isLeft, inI] at hf
      omega
  | relay i =>
    cases f <;> simp_all [IsRow, mark, isLeft, inJ, paint, parity, Fin.ext_iff]
    omega
  | res i s => cases f <;> simp_all [mark, isLeft, inJ, paint]
  | cl i => cases f <;> simp_all [mark, isLeft, inI, paint]

/-- Numeric label indices use one of eight tags and a stage or clause
number. They give a computable injection whose codomain is linear in the
number of variables and clauses. -/
def serial : Lab → ℕ
  | .ch i s => 8 * i + (if s then 1 else 0)
  | .rl i => 8 * i + 2
  | .perm i s => 8 * i + (if s then 4 else 3)
  | .lit i s => 8 * i + (if s then 6 else 5)
  | .kap i => 8 * i + 7

theorem serial_injective : Function.Injective serial := by
  intro f h same
  cases f <;> cases h <;> simp only [serial] at same
  all_goals (try split_ifs at same) <;> simp_all <;> omega

def labelBound (F : Formula) := 8 * (F.n + F.cls.length + 1)

theorem serial_lt (F : Formula) (e : Lab) (valid : IsLab F e) :
    serial e < labelBound F := by
  cases e <;> simp [IsLab, serial, labelBound] at * <;> (try split) <;> omega

def labelIndex (F : Formula) : FLab F ↪ Fin (labelBound F) where
  toFun e := ⟨serial e.val, serial_lt F e.val (Finset.mem_filter.mp e.property).2⟩
  inj' _ _ h := Subtype.ext (serial_injective (congrArg Fin.val h))

def formulaBook (F : Formula) (slot : ℕ → C) :
    Book (FLab F) (Palette C) (Fin (AddressSize.width (labelBound F))) :=
  AddressSize.book (labelIndex F) (fun e => paint slot e.val)

/-- In the quantified rectangles, only the late right relays need a full
track. All other incidence conditions follow from the concrete painting. -/
theorem slot_geometry {F : Formula} {slot : ℕ → C} (sep : SeparatedClauses F slot)
    : Geometry F (formulaBook F slot) := by
  classical
  constructor
  · intro z side f hf h hh same
    apply Subtype.ext
    exact left_unique sep (by simpa [posted, side] using hf)
      (by simpa [posted, side] using hh) same
  · intro z side g
    by_cases full : Wild F z g
    · right
      intro f track
      apply (show inJ F z f.val = true → f ∈ posted F z by simp [posted, side])
      apply all_posted (slot := slot)
      exact (show paint slot f.val = g from track) ▸ full
    · left
      intro f hf h hh fg hg
      apply Subtype.ext
      apply right_unique (F := F) (slot := slot) (z := z)
        (by simpa [posted, side] using hf) (by simpa [posted, side] using hh)
      · rwa [show paint slot f.val = g from fg]
      · exact fg.trans hg.symm
  · intro z f hf
    exact mark_apart z.val ((mem_allRows F _).mp z.property) f.val hf



theorem track_card : Fintype.card (Palette (Fin 3)) = 12 := by decide

/-- The compiled address rail count before adding the private labels. -/
theorem physical_arity (F : Formula) :
    Fintype.card (Rail (Palette (Fin 3)) (Fin (AddressSize.width (labelBound F)))) =
      24 * AddressSize.width (labelBound F) := by
  simp [Rail, Fintype.card_prod, track_card]
  omega

theorem translated_geometry (F : Formula) (wf : F.WF) (short : ∀ q ∈ F.cls, q.length ≤ 3) :
    Geometry (ThreeSlot.translate F) (formulaBook (ThreeSlot.translate F) (ThreeSlot.slot F)) :=
  slot_geometry (ThreeSlot.getD_slot_unique F wf short)

/-- Falsity of a width-three quantified formula excludes a physical word on
twelve tracks, with an explicitly computed rail word for each logical label. -/
theorem no_word_on_logarithmic_rails [DecidableEq Role] (three : Fin 3 ↪ Role)
    (F : Formula) (wf : F.WF) (short : ∀ q ∈ F.cls, q.length ≤ 3)
    (α : ℕ → Bool) (no : ¬ sat F F.n 0 α) :
    let T := ThreeSlot.translate F
    let G := translated_geometry F wf short
    ∀ t : CoreTerm Role (Rail (Palette (Fin 3)) (Fin (AddressSize.width (labelBound T)))),
      (G.rectangle.encoding three).Quiet Finset.univ t →
        ¬ (G.rectangle.encoding three).Demands (Geometry.initialLeft T α)
          (Geometry.initialRight T) t :=
  (translated_geometry F wf short).no_word_of_not_sat three (ThreeSlot.wf_translate F wf) α
    (fun yes => no ((ThreeSlot.sat_translate_iff F wf α).mp yes))

/-- With the two private tracks and the selector, the single candidate table
uses 28 rails per digit and one more input. -/
theorem table_arity (F : Formula) :
    Fintype.card (Option (Rail (Palette (Fin 3) ⊕ Bool) (Fin (AddressSize.width (labelBound F))))) =
      1 + 28 * AddressSize.width (labelBound F) := by
  simp [Rail, Fintype.card_prod, Fintype.card_sum, track_card]
  omega

end KFOL.Core.AddressedQuantified
