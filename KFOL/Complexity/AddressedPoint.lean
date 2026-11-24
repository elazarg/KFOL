module

public import KFOL.Complexity.AddressedEnvelope
public import KFOL.Complexity.AddressTableOutput

/-! # Computing a complete addressed table

Each logical name comes with the physical positions in its address.
Position zero is the selector. All identifiers in the interface are
binary. Each output is the increasing list of its winning roles. -/

@[expose] public section
namespace KFOL.Complexity.AddressedPoint

open Turing.MultiTapeTM ComputableInPolyTime AddressedEnvelope

abbrev Menus := List Names
abbrev Codes := List Entry
abbrev Layout := Codes × (RowData × RowData)
abbrev Input := Layout × Menus

abbrev menusEncoding := encList namesEncoding
abbrev codesEncoding := encList entryEncoding
abbrev layoutEncoding := encPair codesEncoding (encPair rowEncoding rowEncoding)
abbrev pointEncoding := encPair layoutEncoding menusEncoding

def helper (c : ℕ) (v : Menus) (address : Names) : Names :=
  let vals := address.map fun j => v.getD j []
  if vals.any (FullSparseEvaluation.singletonB c) then [c] else vals.flatten

def logical (c : ℕ) (codes : Codes) (v : Menus) : List Entry :=
  codes.map fun p => (p.1, helper c v p.2)

def group (k r : ℕ) (rows : RowData) (vals : List Entry) : Names :=
  (List.range k).filter fun j => evaluate ((r,j),rows,vals)

def baseline (a b : ℕ) (z left right : Names) : Names :=
  (z ++ FullSparseEvaluation.choice b z left) ++ (z ++ FullSparseEvaluation.choice a z right)

def normalize (k : ℕ) (value : Names) : Names :=
  (List.range k).filter fun j => member j value

def point (k a b c : ℕ) (layout : Layout) (v : Menus) : Names :=
  let vals := logical c layout.1 v
  if vals.all (fun p => FullSparseEvaluation.singletonB c p.2) then [c]
  else normalize k (baseline a b (v.getD 0 []) (group k a layout.2.1 vals) (group k b layout.2.2 vals))

variable {X : Type} {input : X ↪ List Bool}

private theorem lookup_poly {v : X → Menus} {i : X → ℕ}
    (hv : ComputableInPolyTime v input menusEncoding) (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun x => (v x).getD (i x) []) input namesEncoding :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encA := namesEncoding)
    (encL := menusEncoding) [] hv.tidy hi.tidy)

theorem helper_poly (c : ℕ) {v : X → Menus} {address : X → Names}
    (hv : ComputableInPolyTime v input menusEncoding) (ha : ComputableInPolyTime address input namesEncoding) :
    ComputableInPolyTime (fun x => helper c (v x) (address x)) input namesEncoding := by
  have vals := mapWithInput (f := fun x j => (v x).getD j []) ha
    (lookup_poly (hv.comp (fst input encNat)) (snd input encNat))
  have hit := anyWithInput (test := fun (_ : X) m => FullSparseEvaluation.singletonB c m) vals
    (FullSparseEvaluation.singleton_polyTime.comp ((const c).prod (snd input namesEncoding)))
  exact hit.ite (const [c]) ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.flatten encNat)).comp vals)

theorem logical_poly (c : ℕ) {codes : X → Codes} {v : X → Menus}
    (hc : ComputableInPolyTime codes input codesEncoding) (hv : ComputableInPolyTime v input menusEncoding) :
    ComputableInPolyTime (fun x => logical c (codes x) (v x)) input codesEncoding := by
  apply mapWithInput (f := fun x (p : Entry) => (p.1, helper c (v x) p.2)) hc
  exact ((fst encNat namesEncoding).comp (snd input entryEncoding)).prod
    (helper_poly c (hv.comp (fst input entryEncoding)) ((snd encNat namesEncoding).comp (snd input entryEncoding)))

theorem group_poly (k r : ℕ) {rows : X → RowData} {vals : X → List Entry}
    (hr : ComputableInPolyTime rows input rowEncoding) (hv : ComputableInPolyTime vals input codesEncoding) :
    ComputableInPolyTime (fun x => group k r (rows x) (vals x)) input namesEncoding := by
  apply filterWithInput (test := fun x j => evaluate ((r,j),rows x,vals x)) (const (List.range k))
  exact evaluate_polyTime.comp (((const r).prod (snd input encNat)).prod
    ((hr.prod hv).comp (fst input encNat)))

theorem baseline_poly (a b : ℕ) {z left right : X → Names}
    (hz : ComputableInPolyTime z input namesEncoding) (hl : ComputableInPolyTime left input namesEncoding)
    (hr : ComputableInPolyTime right input namesEncoding) :
    ComputableInPolyTime (fun x => baseline a b (z x) (left x) (right x)) input namesEncoding := by
  exact listAppend' (listAppend' hz (FullSparseEvaluation.choice_polyTime.comp ((const b).prod (hz.prod hl))))
    (listAppend' hz (FullSparseEvaluation.choice_polyTime.comp ((const a).prod (hz.prod hr))))

theorem normalize_poly (k : ℕ) {v : X → Names} (hv : ComputableInPolyTime v input namesEncoding) :
    ComputableInPolyTime (fun x => normalize k (v x)) input namesEncoding := by
  apply filterWithInput (test := fun x j => member j (v x)) (const (List.range k))
  exact member_polyTime.comp ((snd input encNat).prod (hv.comp (fst input encNat)))

theorem point_poly (k a b c : ℕ) {layout : X → Layout} {v : X → Menus}
    (hp : ComputableInPolyTime layout input layoutEncoding) (hv : ComputableInPolyTime v input menusEncoding) :
    ComputableInPolyTime (fun x => point k a b c (layout x) (v x)) input namesEncoding := by
  have vals := logical_poly c hp.fst' hv
  have hit := allWithInput (test := fun (_ : X) (p : Entry) => FullSparseEvaluation.singletonB c p.2) vals
    (FullSparseEvaluation.singleton_polyTime.comp ((const c).prod ((snd encNat namesEncoding).comp
      (snd input entryEncoding))))
  exact hit.ite (const [c]) (normalize_poly k (baseline_poly a b (lookup_poly hv (const 0))
    (group_poly k a hp.snd'.fst' vals) (group_poly k b hp.snd'.snd' vals)))

/-- Enumerate all points with the exact output ordering of AddressTableOutput. -/
theorem table_poly (k a b c q : ℕ) {n : X → ℕ} {layout : X → Layout}
    (hn : ComputableInPolyTime n input encUnary) (hp : ComputableInPolyTime layout input layoutEncoding) :
    ComputableInPolyTime (AddressTableOutput.table k q n (fun x v => point k a b c (layout x) v))
      input (encList namesEncoding) :=
  AddressTableOutput.table_binary_poly k q hn (point_poly k a b c (hp.comp (fst _ _)) (snd _ _))

end KFOL.Complexity.AddressedPoint
