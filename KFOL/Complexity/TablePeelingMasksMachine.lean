module

public import KFOL.Complexity.TablePeelingMasks

/-! # Multitape polynomial-time checks for one round of the exact-split game -/

@[expose] public section
namespace KFOL.Complexity.TablePeelingMasks

open Turing.MultiTapeTM ComputableInPolyTime TablePeeling TablePeelingGame AddressedEnvelope
open FullSparseEvaluation

variable {X : Type} {e : X ↪ List Bool}

private theorem row_poly {x : X → TablePeeling.Input} {i : X → ℕ}
    (hx : ComputableInPolyTime x e TablePeeling.inputEncoding) (hi : ComputableInPolyTime i e encUnary) :
    ComputableInPolyTime (fun a => (x a).2.getD (i a) ([],[])) e TablePeeling.rowEncoding :=
  (listGetD (encA := TablePeeling.rowEncoding) (encL := encList TablePeeling.rowEncoding) ([],[])).comp
    (hx.snd'.prod hi)

private theorem row_count_poly {x : X → TablePeeling.Input} (hx : ComputableInPolyTime x e TablePeeling.inputEncoding) :
    ComputableInPolyTime (fun a => (x a).2.length) e encUnary :=
  (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length TablePeeling.rowEncoding)).comp hx.snd'

private theorem bit_poly {xs : X → List Bool} {j : X → ℕ}
    (hx : ComputableInPolyTime xs e (encList encBool)) (hj : ComputableInPolyTime j e encUnary) :
    ComputableInPolyTime (fun a => (xs a).getD (j a) false) e encBool :=
  (listGetD (encA := encBool) (encL := encList encBool) false).comp (hx.prod hj)

theorem owner_poly (K : ℕ) {m : X → Move} (hm : ComputableInPolyTime m e moveEncoding) :
    ComputableInPolyTime (fun a => ownerId K (m a)) e encNat := by
  have names := filterWithInput (test := fun a j => (m a).1.getD j false) (const (List.range K))
    (bit_poly (hm.fst'.comp (fst e encUnary)) (snd e encUnary))
  exact unary_to_binary.comp ((headD (encA := encUnary) (encL := encList encUnary) 0).comp names)

theorem child_poly (K : ℕ) {m : X → Move} {s : X → Bool} {i k : X → ℕ}
    (hm : ComputableInPolyTime m e moveEncoding) (hs : ComputableInPolyTime s e encBool)
    (hi : ComputableInPolyTime i e encUnary) (hk : ComputableInPolyTime k e encUnary) :
    ComputableInPolyTime (fun a => childBit K (m a) (s a) (i a) (k a)) e encBool := by
  have dir : ComputableInPolyTime (fun a => (s a).toNat) e encUnary := by
    have alt : ComputableInPolyTime (fun a => if s a then 1 else 0) e encUnary := hs.ite (const 1) (const 0)
    apply alt.of_enc_eq
    intro a
    cases s a <;> rfl
  exact bit_poly hm.fst' (unary_add' (unary_add' (const K)
    (unary_mul' (const 2) (unary_add' (unary_mul' hi (const K)) hk))) dir)

theorem goal_poly (K : ℕ) {x : X → TablePeeling.Input} {p : X → Previous} {i k : X → ℕ}
    (hx : ComputableInPolyTime x e TablePeeling.inputEncoding) (hp : ComputableInPolyTime p e prevEncoding)
    (hi : ComputableInPolyTime i e encUnary) (hk : ComputableInPolyTime k e encUnary) :
    ComputableInPolyTime (fun a => goalBit K (x a) (p a) (i a) (k a)) e encBool := by
  let pre := fst e moveEncoding
  let move := snd e moveEncoding
  exact hp.optionElimWithInput (body := fun a m => childBit K m (m.2.getD 0 false) (i a) (k a))
    (member_polyTime.comp ((unary_to_binary.comp hk).prod (row_poly hx hi).snd'))
    (child_poly K move (bit_poly move.snd' (const 0)) (hi.comp pre) (hk.comp pre))

private theorem fits_poly (K : ℕ) {bit : X → ℕ → Bool} {v : X → Names}
    (hb : ComputableInPolyTime (fun p : X × ℕ => bit p.1 p.2) (encPair e encUnary) encBool)
    (hv : ComputableInPolyTime v e namesEncoding) :
    ComputableInPolyTime (fun x => fits K (bit x) (v x)) e encBool := by
  have active := anyWithInput (test := bit) (const (List.range K)) hb
  have win := member_polyTime.comp ((unary_to_binary.comp (snd e encUnary)).prod (hv.comp (fst e encUnary)))
  have same := allWithInput (test := fun x r => decide (bit x r = member r (v x))) (const (List.range K))
    (decide_eq' hb win)
  exact bool_or.comp ((bool_not.comp active).prod same)

private theorem fits_child_poly (K : ℕ) (side : Bool) {m : X → Move} {i : X → ℕ} {v : X → Names}
    (hm : ComputableInPolyTime m e moveEncoding) (hi : ComputableInPolyTime i e encUnary)
    (hv : ComputableInPolyTime v e namesEncoding) :
    ComputableInPolyTime (fun a => fits K (childBit K (m a) side (i a)) (v a)) e encBool :=
  fits_poly K (child_poly K (hm.comp (fst e encUnary)) (const side)
    (hi.comp (fst e encUnary)) (snd e encUnary)) hv

private theorem fits_goal_poly (K : ℕ) {x : X → TablePeeling.Input} {p : X → Previous}
    {i : X → ℕ} {v : X → Names} (hx : ComputableInPolyTime x e TablePeeling.inputEncoding)
    (hp : ComputableInPolyTime p e prevEncoding) (hi : ComputableInPolyTime i e encUnary)
    (hv : ComputableInPolyTime v e namesEncoding) :
    ComputableInPolyTime (fun a => fits K (goalBit K (x a) (p a) (i a)) (v a)) e encBool :=
  fits_poly K (goal_poly K (hx.comp (fst e encUnary)) (hp.comp (fst e encUnary))
    (hi.comp (fst e encUnary)) (snd e encUnary)) hv

private theorem row_gate_poly (K : ℕ) {x : X → TablePeeling.Input} {p : X → Previous} {m : X → Move}
    {i : X → ℕ} {a b : X → Names} (hx : ComputableInPolyTime x e TablePeeling.inputEncoding)
    (hp : ComputableInPolyTime p e prevEncoding) (hm : ComputableInPolyTime m e moveEncoding)
    (hi : ComputableInPolyTime i e encUnary) (ha : ComputableInPolyTime a e namesEncoding)
    (hb : ComputableInPolyTime b e namesEncoding) :
    ComputableInPolyTime (fun s =>
      !(fits K (childBit K (m s) false (i s)) (a s) && fits K (childBit K (m s) true (i s)) (b s)) ||
        fits K (goalBit K (x s) (p s) (i s)) (choice (ownerId K (m s)) (a s) (b s))) e encBool := by
  have both := bool_and' (fits_child_poly K false hm hi ha) (fits_child_poly K true hm hi hb)
  exact bool_or.comp ((bool_not.comp both).prod
    (fits_goal_poly K hx hp hi (choice_polyTime.comp ((owner_poly K hm).prod (ha.prod hb)))))

/-- Fixed K permits a scan of every pair of nonempty menus per input row. -/
theorem gate_poly (K : ℕ) :
    ComputableInPolyTime (fun a : TablePeeling.Input × Previous × Move => gate K a.1 a.2.1 a.2.2)
      (stepEncoding TablePeeling.inputEncoding) encBool := by
  let start := stepEncoding TablePeeling.inputEncoding
  let indexed := encPair start encUnary
  let left := encPair indexed namesEncoding
  let pre := fst start encUnary
  let pre' := fst indexed namesEncoding
  let pre'' := fst left namesEncoding
  let orig := (pre.comp pre').comp pre''
  let i := ((snd start encUnary).comp pre').comp pre''
  let a := (snd indexed namesEncoding).comp pre''
  let b := snd left namesEncoding
  have checkRow := row_gate_poly K orig.fst' orig.snd'.fst' orig.snd'.snd' i a b
  unfold gate
  apply allWithInput (ComputableInPolyTime.range.comp (row_count_poly (fst _ _)))
  apply allWithInput (const (allMenus K))
  exact allWithInput (const (allMenus K)) checkRow

private theorem normalize_poly (K : ℕ) {xs : X → Names} (hx : ComputableInPolyTime xs e namesEncoding) :
    ComputableInPolyTime (fun a => normalize K (xs a)) e namesEncoding := by
  have ys := filterWithInput (test := fun a r => member r (xs a)) (const (List.range K))
    (member_polyTime.comp ((snd e encNat).prod (hx.comp (fst e encNat))))
  have empty := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := encNat))).comp ys
  exact empty.ite (const (List.range K)) ys

theorem endTest_poly (K : ℕ) : ComputableInPolyTime
    (fun a : TablePeeling.Input × Previous => endTest K a.1 a.2) (endEncoding TablePeeling.inputEncoding) encBool := by
  let start := endEncoding TablePeeling.inputEncoding
  let indexed := encPair start encUnary
  let pre := fst start encUnary
  let pre' := fst indexed encUnary
  let orig := pre.comp pre'
  let j := (snd start encUnary).comp pre'
  let i := snd indexed encUnary
  have row := row_poly orig.fst' i
  have read := (listGetD (encA := namesEncoding) (encL := AddressedPoint.menusEncoding) []).comp (row.fst'.prod j)
  unfold endTest
  apply anyWithInput (ComputableInPolyTime.range.comp ((fst _ _).comp (fst _ _)))
  apply allWithInput (ComputableInPolyTime.range.comp (row_count_poly pre.fst'))
  exact fits_goal_poly K orig.fst' orig.snd' i (normalize_poly K read)

end KFOL.Complexity.TablePeelingMasks
