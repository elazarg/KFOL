module

public import KFOL.Complexity.AddressedIncidence
public import KFOL.Complexity.AddressedPointCorrectness
public import KFOL.Core.ExplicitTableReduction

/-! # Correctness of the numbered incidence lists -/

@[expose] public section
namespace KFOL.Complexity.AddressedIncidence

open Bichain Bichain.Quantified Recognition.Lists Core Core.AddressedQuantified Core.AddressedRails
open Core.AddressedRectangle Core.AddressedPadding Core.AddressedRecognition AddressedEnvelope
open scoped Classical

theorem exAt_input (u : ExplicitTableReduction.Input) (i : ℕ) :
    (ThreeCNF.fromTQBFCNF u).ex i = exAt (formulaOf u).n i := by
  have le : (formulaOf u).n ≤ (ThreeCNF.translate (formulaOf u)).n := Nat.le_add_right _ _
  by_cases early : i ≤ (formulaOf u).n
  · change (if i ≤ (ThreeCNF.translate (formulaOf u)).n then (ThreeCNF.translate (formulaOf u)).ex i else true) = _
    rw [ite_eq_left (early.trans le)]
    simp [ThreeCNF.translate,early,exAt,exB_iff _ _ early,formulaOf_ex]
  · simp [ThreeCNF.fromTQBFCNF, ThreeSlot.translate, ThreeCNF.translate, exAt, early]

@[simp] theorem serialT_tupL (e : Lab) : serialT (tupL e) = serial e := by
  cases e with
  | ch _ s | perm _ s | lit _ s => cases s <;> rfl
  | rl => rfl
  | kap => rfl

@[simp] theorem leftT_tupV (z : Vtx) : leftT (tupV z) = isLeft z := by cases z <;> rfl

theorem markCode_tup (F : Formula) (old : ℕ) (ex : ∀ i, F.ex i = exAt old i) (z : Vtx) :
    markCode old F.n (tupV z) = tupL (mark F z) := by
  cases z with
  | br i s =>
    by_cases hi : i ≤ F.n
    · simp only [tupV, markCode, mark, beq_self_eq_true, ite_true, hi, ex]
      by_cases h : exAt old i = true <;> simp [h,tupL]
    · simp [tupV, markCode, mark, hi, tupL]
  | relay => rfl
  | res => rfl
  | cl => rfl

theorem rightT_tup (F : Formula) (old : ℕ) (ex : ∀ i, F.ex i = exAt old i)
    (z : Vtx) (e : Lab) : rightT old F.n (tupV z) (tupL e) = inJ F z e := by
  rw [Bool.eq_iff_iff]
  cases z with
  | br i s => cases e <;> simp only [tupV,tupL] <;> simp [rightT,inJ]
  | relay i =>
    cases e with
    | ch j t => cases t <;> simp only [tupV,tupL] <;> simp [rightT,inJ,ex]
    | rl j => simp only [tupV,tupL]; simp [rightT,inJ]
    | perm j t => simp only [tupV,tupL]; simp [rightT,inJ]
    | lit j t => simp only [tupV,tupL]; simp [rightT,inJ]
    | kap c => simp only [tupV,tupL]; simp [rightT,inJ]
  | res i s => cases e <;> simp only [tupV,tupL] <;> simp [rightT,inJ,toNat_eq_iff]
  | cl c => cases e <;> simp only [tupV,tupL] <;> simp [rightT,inJ]

def ids (F : Formula) : (FLab F ⊕ Bool) ↪ ℕ where
  toFun := Sum.elim (fun e => 2 + serial e.val) Bool.toNat
  inj' := by
    rintro (a | a) (b | b) eq
    · exact congrArg Sum.inl (Subtype.ext (serial_injective (Nat.add_left_cancel eq)))
    · change 2 + serial a.val = b.toNat at eq
      have := b.toNat_le
      omega
    · change a.toNat = 2 + serial b.val at eq
      have := a.toNat_le
      omega
    · exact congrArg Sum.inr ((toNat_eq_iff _ _).mp eq)

def nativePost (F : Formula) (side : Bool) (z : Vtx) : FLab F ⊕ Bool → Bool :=
  Sum.elim (fun e => if side then inI F z e.val else inJ F z e.val) (fun b => b == side)

theorem postings_iff (F : Formula) (old : ℕ) (ex : ∀ i, F.ex i = exAt old i)
    (side : Bool) (z : Vtx) (f : FLab F ⊕ Bool) :
    ids F f ∈ postings old F.n (numCls F) side (tupV z) ↔ nativePost F side z f = true := by
  let test := fun e => if side then inIB F.n (numCls F) (tupV z) e else rightT old F.n (tupV z) e
  have hit (e : Lab) : test (tupL e) = if side then inI F z e else inJ F z e := by
    simp only [test, inIB_tup, rightT_tup F old ex]
  have ls (p : Tup) : p ∈ labsT F.n (numCls F).length ↔ ∃ e : FLab F, tupL e.val = p := by
    rw [show (numCls F).length = F.cls.length from List.length_map _, mem_labsT]
    exact ⟨fun ⟨f,h,e⟩ => ⟨⟨f,h⟩,e⟩,fun ⟨f,e⟩ => ⟨_,f.property,e⟩⟩
  change ids F f ∈ side.toNat :: (((labsT F.n (numCls F).length).filter test).map (fun e => 2 + serialT e)) ↔ _
  simp only [List.mem_cons, List.mem_map, List.mem_filter, ls]
  cases f with
  | inl f =>
    have ne : 2 + serial f.val ≠ side.toNat := by have := side.toNat_le; omega
    change (2 + serial f.val = _ ∨ _) ↔ _
    rw [or_iff_right ne]
    constructor
    · rintro ⟨_,⟨⟨e,rfl⟩,he⟩,eq⟩
      have same : e.val = f.val := serial_injective (Nat.add_left_cancel ((serialT_tupL _).symm ▸ eq))
      simpa only [nativePost, Sum.elim_inl, ←same] using (hit e.val ▸ he)
    · intro present
      exact ⟨tupL f.val, ⟨⟨f,rfl⟩,(hit f.val).symm ▸ present⟩,by simp only [serialT_tupL]; rfl⟩
  | inr b =>
    change (b.toNat = side.toNat ∨ _) ↔ (b == side) = true
    simp only [toNat_eq_iff, beq_iff_eq, or_iff_left_iff_imp]
    rintro ⟨p,_,eq⟩
    change 2 + serialT p = b.toNat at eq
    have := b.toNat_le
    omega

/-- The emitted endpoint and losses present the padded native rectangle. -/
theorem rowData_correct (F : Formula) (old : ℕ) (ex : ∀ i, F.ex i = exAt old i)
    {Track Bit : Type*} {B : Book (FLab F) Track Bit} (G : Geometry F B) (side : Bool) :
    RowPresentation (ids F) (extendRows G.rectangle) Finset.univ side
      (sideEndpoint side (Geometry.initialLeft F (fun _ => false)) (Geometry.initialRight F))
      (rowData old F.n (numCls F) side) := by
  let mk := fun p : Tup => (toBin (nameT (markCode old F.n p)), postings old F.n (numCls F) side p)
  have rows (p : Tup) : p ∈ rowsT F.n (numCls F).length ↔ ∃ z : Row F, tupV z.val = p := by
    rw [show (numCls F).length = F.cls.length from List.length_map _, mem_rowsT]
    exact ⟨fun ⟨f,h,e⟩ => ⟨⟨f,h⟩,e⟩,fun ⟨f,e⟩ => ⟨_,f.property,e⟩⟩
  have rowMatch (z : Row F) (h : isLeft z.val = side) :
      RowMatches (ids F) (extendRows G.rectangle) z (mk (tupV z.val)) := by
    constructor
    · change 2 + serialT (markCode old F.n (tupV z.val)) = 2 + serial (mark F z.val)
      rw [markCode_tup F old ex, serialT_tupL]
    · intro f
      rw [show (mk (tupV z.val)).2 = _ from rfl, postings_iff F old ex]
      cases f with
      | inl e =>
        change (if side then inI F z.val e.val else inJ F z.val e.val) = true ↔
          (if isLeft z.val then inI F z.val e.val else inJ F z.val e.val) = true
        rw [h]
      | inr b =>
        change (b == side) = true ↔ b = isLeft z.val
        simp [h]
  have enc (pr : Entry) : pr ∈ (rowData old F.n (numCls F) side).2 ↔
      ∃ z : Row F, isLeft z.val = side ∧ mk (tupV z.val) = pr := by
    change pr ∈ ((rowsT F.n (numCls F).length).filter fun z => leftT z == side).map mk ↔ _
    simp only [List.mem_map,List.mem_filter,rows,beq_iff_eq]
    constructor
    · rintro ⟨_,⟨⟨z,rfl⟩,eq⟩,rfl⟩
      exact ⟨z, leftT_tupV _ ▸ eq,rfl⟩
    · rintro ⟨z,eq,rfl⟩
      exact ⟨_, ⟨⟨z,rfl⟩,(leftT_tupV _).symm ▸ eq⟩,rfl⟩
  constructor
  · intro f
    cases side
    · change ids F f ∈ postings old F.n (numCls F) false (tupV (.relay 0)) ↔ _
      rw [postings_iff F old ex]
      cases f <;> simp [nativePost,sideEndpoint,extendEndpoint,Geometry.initialRight]
    · change ids F f ∈ postings old F.n (numCls F) true (tupV (.br 0 false)) ↔ _
      rw [postings_iff F old ex]
      cases f <;> simp [nativePost,sideEndpoint,extendEndpoint,Geometry.initialLeft]
  · intro pr mem
    obtain ⟨z,h,rfl⟩ := (enc pr).mp mem
    exact ⟨z, Finset.mem_univ _, h, rowMatch z h⟩
  · intro z _ h
    exact ⟨_,(enc _).mpr ⟨z,h,rfl⟩,rowMatch z h⟩

/-- Ordinary triangle and rectangle tracks, followed by the two private tracks. -/
def rankT : Palette (Fin 3) ⊕ Bool → ℕ
  | .inl (.branch p s) => 2 * p.val + s.toNat
  | .inl (.relay p) => 4 + p.val
  | .inl .permanent => 6
  | .inl (.literal j) => 7 + j.val
  | .inl (.clause p) => 10 + p.val
  | .inr b => 12 + b.toNat

theorem rank_bound : ∀ g, rankT g < 14 := by decide
theorem rank_bijective : Function.Bijective (fun g => (⟨rankT g,rank_bound g⟩ : Fin 14)) := by
  constructor <;> decide

/-- Physical track numbering used by the emitted address vectors. -/
noncomputable def trackEquiv : (Palette (Fin 3) ⊕ Bool) ≃ Fin 14 := Equiv.ofBijective _ rank_bijective

@[simp] theorem trackEquiv_val (g : Palette (Fin 3) ⊕ Bool) : (trackEquiv g).val = rankT g := rfl

theorem trackT_tup (T : Formula) (e : Lab) :
    trackT T.n (tupL e) = rankT (.inl (paint (ThreeSlot.slot T) e)) := by
  cases e with
  | ch => rfl
  | rl => rfl
  | perm => rfl
  | kap => rfl
  | lit i s =>
    change 7 + (if i ≤ T.n then 0 else if i ≤ 2*T.n then 1 else 2) = 7 + (ThreeSlot.slot T i).val
    unfold ThreeSlot.slot
    split_ifs <;> rfl

abbrev BookOf (T : Formula) :=
  extendBook (formulaBook (ThreeSlot.translate T) (ThreeSlot.slot T))

def railIndex {d : ℕ} (u : Rail (Palette (Fin 3) ⊕ Bool) (Fin d)) : ℕ :=
  pos d (rankT u.1) u.2.1.val u.2.2.toNat

def serialOf (F : Formula) : FLab F ⊕ Bool → ℕ := Sum.elim (fun e => serial e.val) (fun _ => 0)

def record (T : Formula) (f : FLab (ThreeSlot.translate T) ⊕ Bool) : Entry :=
  let F := ThreeSlot.translate T
  (ids F f, code (AddressSize.width (labelBound F)) (rankT ((BookOf T).track f)) (serialOf F f))

theorem record_mem (T : Formula) (p : Entry) :
    let F := ThreeSlot.translate T
    p ∈ addresses T.n F.n F.cls.length ↔ ∃ f, record T f = p := by
  let F := ThreeSlot.translate T
  have labs (e : Tup) : e ∈ labsT F.n F.cls.length ↔ ∃ f : FLab F, tupL f.val = e := by
    rw [mem_labsT]
    exact ⟨fun ⟨f,h,e⟩ => ⟨⟨f,h⟩,e⟩,fun ⟨f,e⟩ => ⟨_,f.property,e⟩⟩
  have ordinary (f : FLab F) :
      (toBin (nameT (tupL f.val)), code (AddressSize.width (labelBound F))
        (trackT T.n (tupL f.val)) (serialT (tupL f.val))) = record T (.inl f) := by
    simp only [toBin, nameT, serialT_tupL, trackT_tup]
    rfl
  change p ∈ [_,_] ++ (labsT F.n F.cls.length).map _ ↔ _
  simp only [List.mem_append,List.mem_cons,List.mem_nil_iff,or_false,List.mem_map,labs]
  constructor
  · rintro ((rfl | rfl) | ⟨_,⟨f,rfl⟩,rfl⟩)
    · exact ⟨.inr false,rfl⟩
    · exact ⟨.inr true,rfl⟩
    · exact ⟨.inl f,(ordinary f).symm⟩
  · rintro ⟨(f | b),rfl⟩
    · exact Or.inr ⟨_,⟨f,rfl⟩,ordinary f⟩
    · cases b; exact Or.inl (Or.inl rfl); exact Or.inl (Or.inr rfl)

theorem record_positions (T : Formula) (f : FLab (ThreeSlot.translate T) ⊕ Bool) (j : ℕ) :
    j ∈ (record T f).2 ↔ ∃ i, railIndex ((BookOf T).rail f i) = j := by
  let F := ThreeSlot.translate T
  let d := AddressSize.width (labelBound F)
  have digits (i : Fin d) : (BookOf T).digit f i = (serialOf F f).testBit i.val := by
    cases f with
    | inl e => rfl
    | inr b => simp [BookOf,extendBook,serialOf]
  change j ∈ (List.range d).map _ ↔ _
  simp only [List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,h⟩
    exact ⟨⟨i,hi⟩,by simpa only [railIndex,Book.rail,digits,toBin] using h⟩
  · rintro ⟨i,h⟩
    exact ⟨i.val,i.isLt,by simpa only [railIndex,Book.rail,digits,toBin] using h⟩

/-- The physical lookup lists present the native address book on all padded
logical labels, in the numbered menu-tuple coordinates. -/
theorem codes_correct (T : Formula) :
    let F := ThreeSlot.translate T
    AddressedPoint.CodePresentation (ids F) (BookOf T) railIndex (addresses T.n F.n F.cls.length) := by
  constructor
  · intro p hp
    obtain ⟨f,rfl⟩ := (record_mem T p).mp hp
    exact ⟨f,rfl,record_positions T f⟩
  · intro f
    exact ⟨record T f,(record_mem T _).mpr ⟨f,rfl⟩,rfl⟩

end KFOL.Complexity.AddressedIncidence
