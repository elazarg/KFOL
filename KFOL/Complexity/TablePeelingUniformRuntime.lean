module

public import KFOL.Complexity.TablePeelingUniformGate
public import KFOL.Complexity.TablePeelingUniformMasks
public import KFOL.Complexity.TablePeelingUniformInput

/-! # A uniform polynomial-time verifier for the split at a table row -/

@[expose] public section
namespace KFOL.Complexity.TablePeelingUniform

open Turing.MultiTapeTM ComputableInPolyTime TablePeelingGame TablePeelingUniformGate
open TablePeelingMasks AddressedEnvelope FullSparseEvaluation

variable {X : Type} {e : X ↪ List Bool}

private theorem rowMenu_poly {k : X → ℕ} (hK : ComputableInPolyTime k e encUnary)
    {f : X → ℕ → Bool}
    (test : ComputableInPolyTime (fun p : X × ℕ => f p.1 p.2) (encPair e encUnary) encBool) :
    ComputableInPolyTime (fun x => rowMenu (k x) (f x)) e namesEncoding := by
  have raw := filterWithInput (test := f) (ComputableInPolyTime.range.comp hK) test
  have recode := (ComputableInPolyTime.map unary_to_binary).comp raw
  apply recode.of_enc_eq
  intro x
  simp only [Function.comp_apply, List.map_id', rowMenu]

private theorem rowGate_poly {k r : X → ℕ} {P L R : X → ℕ → Bool}
    (hK : ComputableInPolyTime k e encUnary) (hr : ComputableInPolyTime r e encNat)
    (hp : ComputableInPolyTime (fun p : X × ℕ => P p.1 p.2) (encPair e encUnary) encBool)
    (hl : ComputableInPolyTime (fun p : X × ℕ => L p.1 p.2) (encPair e encUnary) encBool)
    (hu : ComputableInPolyTime (fun p : X × ℕ => R p.1 p.2) (encPair e encUnary) encBool) :
    ComputableInPolyTime (fun x => rowGate (k x) (r x) (P x) (L x) (R x)) e encBool := by
  let empty := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty (encA := encNat) (encL := namesEncoding))
  have parent := rowMenu_poly hK hp
  have left := rowMenu_poly hK hl
  have right := rowMenu_poly hK hu
  have absorbs := bool_or.comp ((singleton_polyTime.comp (hr.prod left)).prod (singleton_polyTime.comp (hr.prod right)))
  have both := bool_and' (bool_not.comp (empty.comp left)) (bool_not.comp (empty.comp right))
  exact bool_or.comp ((empty.comp parent).prod (absorbs.ite (fits_poly hK hp (cons' hr (const [])))
    (bool_and' both (fits_poly hK hp (listAppend' left right)))))

theorem gateFast_poly : ComputableInPolyTime (fun a : Instance × Previous × Move =>
    gateFast a.1.1 a.1.2 a.2.1 a.2.2) (stepEncoding encoding) encBool := by
  let start := stepEncoding encoding
  let indexed := encPair start encUnary
  let pre := fst start encUnary
  let k := ((fst encUnary TablePeeling.inputEncoding).comp (fst encoding (encPair prevEncoding moveEncoding))).comp pre
  let vars := ((snd encUnary TablePeeling.inputEncoding).comp (fst encoding (encPair prevEncoding moveEncoding))).comp pre
  let prev := ((fst prevEncoding moveEncoding).comp (snd encoding (encPair prevEncoding moveEncoding))).comp pre
  let cur := ((snd prevEncoding moveEncoding).comp (snd encoding (encPair prevEncoding moveEncoding))).comp pre
  let idx := snd start encUnary
  let outer := fst indexed encUnary
  let role := snd indexed encUnary
  unfold gateFast
  apply allWithInput (ComputableInPolyTime.range.comp (row_count_poly (snd' (fst encoding (encPair prevEncoding moveEncoding)))))
  apply rowGate_poly k (owner_poly k cur)
  · exact goal_poly (k.comp outer) (vars.comp outer) (prev.comp outer) (idx.comp outer) role
  · exact child_poly (k.comp outer) (cur.comp outer) (const false) (idx.comp outer) role
  · exact child_poly (k.comp outer) (cur.comp outer) (const true) (idx.comp outer) role

theorem uniform_end_poly : ComputableInPolyTime (fun a : Instance × Previous =>
    endTest a.1.1 a.1.2 a.2) (endEncoding encoding) encBool := by
  let input := fst encoding prevEncoding
  exact TablePeelingUniform.endTest_poly input.fst' input.snd' (snd encoding prevEncoding)

end KFOL.Complexity.TablePeelingUniform
