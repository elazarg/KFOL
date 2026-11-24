module

public import KFOL.Complexity.TablePeelingMasksMachine

/-! # Multitape polynomial-time checks for variable-width roles and projections -/

@[expose] public section
namespace KFOL.Complexity.TablePeelingUniform

open Turing.MultiTapeTM ComputableInPolyTime TablePeeling TablePeelingGame AddressedEnvelope
open FullSparseEvaluation TablePeelingMasks

variable {X : Type} {e : X ↪ List Bool}

theorem row_poly {x : X → TablePeeling.Input} {i : X → ℕ}
    (hx : ComputableInPolyTime x e TablePeeling.inputEncoding) (hi : ComputableInPolyTime i e encUnary) :
    ComputableInPolyTime (fun a => (x a).2.getD (i a) ([],[])) e TablePeeling.rowEncoding :=
  (listGetD (encA := TablePeeling.rowEncoding) (encL := encList TablePeeling.rowEncoding) ([],[])).comp
    (hx.snd'.prod hi)

theorem row_count_poly {x : X → TablePeeling.Input} (hx : ComputableInPolyTime x e TablePeeling.inputEncoding) :
    ComputableInPolyTime (fun a => (x a).2.length) e encUnary :=
  (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.length TablePeeling.rowEncoding)).comp hx.snd'

theorem bit_poly {xs : X → List Bool} {j : X → ℕ}
    (hx : ComputableInPolyTime xs e (encList encBool)) (hj : ComputableInPolyTime j e encUnary) :
    ComputableInPolyTime (fun a => (xs a).getD (j a) false) e encBool :=
  (listGetD (encA := encBool) (encL := encList encBool) false).comp (hx.prod hj)

theorem owner_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) {m : X → Move} (hm : ComputableInPolyTime m e moveEncoding) :
    ComputableInPolyTime (fun a => ownerId (K a) (m a)) e encNat := by
  have names := filterWithInput (test := fun a j => (m a).1.getD j false) (ComputableInPolyTime.range.comp hK)
    (bit_poly (hm.fst'.comp (fst e encUnary)) (snd e encUnary))
  exact unary_to_binary.comp ((headD (encA := encUnary) (encL := encList encUnary) 0).comp names)

theorem child_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) {m : X → Move} {s : X → Bool} {i k : X → ℕ}
    (hm : ComputableInPolyTime m e moveEncoding) (hs : ComputableInPolyTime s e encBool)
    (hi : ComputableInPolyTime i e encUnary) (hk : ComputableInPolyTime k e encUnary) :
    ComputableInPolyTime (fun a => childBit (K a) (m a) (s a) (i a) (k a)) e encBool := by
  have dir : ComputableInPolyTime (fun a => (s a).toNat) e encUnary := by
    have alt : ComputableInPolyTime (fun a => if s a then 1 else 0) e encUnary := hs.ite (const 1) (const 0)
    apply alt.of_enc_eq
    intro a
    cases s a <;> rfl
  exact bit_poly hm.fst' (unary_add' (unary_add' hK
    (unary_mul' (const 2) (unary_add' (unary_mul' hi hK) hk))) dir)

theorem goal_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) {x : X → TablePeeling.Input} {p : X → Previous} {i k : X → ℕ}
    (hx : ComputableInPolyTime x e TablePeeling.inputEncoding) (hp : ComputableInPolyTime p e prevEncoding)
    (hi : ComputableInPolyTime i e encUnary) (hk : ComputableInPolyTime k e encUnary) :
    ComputableInPolyTime (fun a => goalBit (K a) (x a) (p a) (i a) (k a)) e encBool := by
  let pre := fst e moveEncoding
  let move := snd e moveEncoding
  exact hp.optionElimWithInput (body := fun a m => childBit (K a) m (m.2.getD 0 false) (i a) (k a))
    (member_polyTime.comp ((unary_to_binary.comp hk).prod (row_poly hx hi).snd'))
    (child_poly (hK.comp pre) move (bit_poly move.snd' (const 0)) (hi.comp pre) (hk.comp pre))

theorem fits_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) {bit : X → ℕ → Bool} {v : X → Names}
    (hb : ComputableInPolyTime (fun p : X × ℕ => bit p.1 p.2) (encPair e encUnary) encBool)
    (hv : ComputableInPolyTime v e namesEncoding) :
    ComputableInPolyTime (fun x => fits (K x) (bit x) (v x)) e encBool := by
  have active := anyWithInput (test := bit) (ComputableInPolyTime.range.comp hK) hb
  have win := member_polyTime.comp ((unary_to_binary.comp (snd e encUnary)).prod (hv.comp (fst e encUnary)))
  have same := allWithInput (test := fun x r => decide (bit x r = member r (v x))) (ComputableInPolyTime.range.comp hK)
    (decide_eq' hb win)
  exact bool_or.comp ((bool_not.comp active).prod same)

theorem fits_child_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) (side : Bool) {m : X → Move} {i : X → ℕ} {v : X → Names}
    (hm : ComputableInPolyTime m e moveEncoding) (hi : ComputableInPolyTime i e encUnary)
    (hv : ComputableInPolyTime v e namesEncoding) :
    ComputableInPolyTime (fun a => fits (K a) (childBit (K a) (m a) side (i a)) (v a)) e encBool :=
  fits_poly hK (child_poly (hK.comp (fst e encUnary)) (hm.comp (fst e encUnary)) (const side)
    (hi.comp (fst e encUnary)) (snd e encUnary)) hv

theorem fits_goal_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) {x : X → TablePeeling.Input} {p : X → Previous}
    {i : X → ℕ} {v : X → Names} (hx : ComputableInPolyTime x e TablePeeling.inputEncoding)
    (hp : ComputableInPolyTime p e prevEncoding) (hi : ComputableInPolyTime i e encUnary)
    (hv : ComputableInPolyTime v e namesEncoding) :
    ComputableInPolyTime (fun a => fits (K a) (goalBit (K a) (x a) (p a) (i a)) (v a)) e encBool :=
  fits_poly hK (goal_poly (hK.comp (fst e encUnary)) (hx.comp (fst e encUnary)) (hp.comp (fst e encUnary))
    (hi.comp (fst e encUnary)) (snd e encUnary)) hv

theorem rangeBinary_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) :
    ComputableInPolyTime (fun a => List.range (K a)) e namesEncoding := by
  have convert : ComputableInPolyTime (fun i : ℕ => i) encUnary encNat := unary_to_binary
  have named : ComputableInPolyTime (fun s : List ℕ => s) (encList encUnary) namesEncoding := by
    rw [show (fun s : List ℕ => s) = List.map (fun i : ℕ => i) by funext s; exact (List.map_id' s).symm]
    exact ComputableInPolyTime.map convert
  exact named.comp (ComputableInPolyTime.range.comp hK)

theorem normalize_poly {K : X → ℕ} (hK : ComputableInPolyTime K e encUnary) {xs : X → Names} (hx : ComputableInPolyTime xs e namesEncoding) :
    ComputableInPolyTime (fun a => normalize (K a) (xs a)) e namesEncoding := by
  have ys := filterWithInput (test := fun a r => member r (xs a)) (rangeBinary_poly hK)
    (member_polyTime.comp ((snd e encNat).prod (hx.comp (fst e encNat))))
  have empty := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := encNat))).comp ys
  exact empty.ite (rangeBinary_poly hK) ys

theorem endTest_poly {K : X → ℕ} {x : X → TablePeeling.Input} {p : X → Previous}
    (hK : ComputableInPolyTime K e encUnary) (hx : ComputableInPolyTime x e TablePeeling.inputEncoding)
    (hp : ComputableInPolyTime p e prevEncoding) :
    ComputableInPolyTime (fun a => endTest (K a) (x a) (p a)) e encBool := by
  let indexed := encPair e encUnary
  let pre := fst e encUnary
  let pre' := fst indexed encUnary
  let orig := pre.comp pre'
  let j := (snd e encUnary).comp pre'
  let i := snd indexed encUnary
  have row := row_poly (hx.comp orig) i
  have read := (listGetD (encA := namesEncoding) (encL := AddressedPoint.menusEncoding) []).comp (row.fst'.prod j)
  unfold endTest
  apply anyWithInput (ComputableInPolyTime.range.comp hx.fst')
  apply allWithInput (ComputableInPolyTime.range.comp (row_count_poly (hx.comp pre)))
  exact fits_goal_poly (hK.comp orig) (hx.comp orig) (hp.comp orig) i (normalize_poly (hK.comp orig) read)

end KFOL.Complexity.TablePeelingUniform
