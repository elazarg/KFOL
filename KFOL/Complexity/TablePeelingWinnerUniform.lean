module

public import KFOL.Complexity.TablePeelingUniform

/-! # Uniformly listing the interpolation rows of a winner table

The role count and arity are unary. On every input the scan stops at the
supplied list length. The length required by the declared arity is computed
in binary, which also bounds the cost of rejecting malformed tables.
-/

@[expose] public section
namespace KFOL.Complexity.TablePeelingWinnerUniform

open Turing.MultiTapeTM ComputableInPolyTime AddressTableOutput AddressedPoint
open TablePeeling

abbrev Instance := ℕ × TableInput
abbrev encoding := encPair encUnary tableEncoding
abbrev destEncoding := encPair encUnary inputEncoding

variable {X : Type} {e : X ↪ List Bool}

private theorem base_poly {k : X → ℕ} (hk : ComputableInPolyTime k e encUnary) :
    ComputableInPolyTime (fun x => 2 ^ k x - 1) e encNat :=
  binary_sub' (binary_pow' (const 2) hk) (const 1)

private theorem mask_poly {k i j : X → ℕ} (hk : ComputableInPolyTime k e encUnary)
    (hi : ComputableInPolyTime i e encUnary) (hj : ComputableInPolyTime j e encUnary) :
    ComputableInPolyTime (fun x => mask (k x) (i x) (j x)) e encNat := by
  apply ComputableInPolyTime.of_tidy
  have base := (base_poly hk).tidy
  apply ComputableTidilyInPolyTime.binary_add'
  · apply ComputableTidilyInPolyTime.binary_mod' _ base
    apply ComputableTidilyInPolyTime.binary_div' (unary_to_binary.comp hi).tidy
    exact ComputableTidilyInPolyTime.binary_pow' base hj.tidy
  · exact .const 1

private theorem menu_poly {k i j : X → ℕ} (hk : ComputableInPolyTime k e encUnary)
    (hi : ComputableInPolyTime i e encUnary) (hj : ComputableInPolyTime j e encUnary) :
    ComputableInPolyTime (fun x => menu (k x) (i x) (j x)) e (encList encUnary) := by
  apply filterWithInput (ComputableInPolyTime.range.comp hk)
  exact .of_tidy (ComputableTidilyInPolyTime.binary_testBit ((mask_poly hk hi hj).comp (fst _ _)).tidy
    (snd e encUnary).tidy)

private theorem bin_menu : ComputableInPolyTime (fun m : List ℕ => m) (encList encUnary)
    AddressedEnvelope.namesEncoding := by
  rw [show (fun m : List ℕ => m) = List.map (fun r : ℕ => r) by funext m; exact (List.map_id' m).symm]
  exact ComputableInPolyTime.map unary_to_binary

theorem tuple_poly {k d i : X → ℕ} (hk : ComputableInPolyTime k e encUnary)
    (hd : ComputableInPolyTime d e encUnary) (hi : ComputableInPolyTime i e encUnary) :
    ComputableInPolyTime (fun x => tuple (k x) (d x) (i x)) e menusEncoding :=
  mapWithInput (f := fun x j => menu (k x) (i x) j) (ComputableInPolyTime.range.comp hd)
    (bin_menu.comp (menu_poly (hk.comp (fst _ _)) (hi.comp (fst _ _)) (snd _ _)))

theorem valid_poly {k : X → ℕ} {p : X → TableInput} (hk : ComputableInPolyTime k e encUnary)
    (hp : ComputableInPolyTime p e tableEncoding) :
    ComputableInPolyTime (fun x => TablePeeling.valid (k x) (p x)) e encBool := by
  have size := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.length AddressedEnvelope.namesEncoding)).comp hp.snd'
  have same := decide_eq' (unary_to_binary.comp size) (binary_pow' (base_poly hk) hp.fst')
  have test : ComputableInPolyTime (fun a : X × List ℕ => a.2.all (fun r => decide (r < k a.1)))
      (encPair e AddressedEnvelope.namesEncoding) encBool := by
    apply allWithInput (snd _ _)
    exact binary_lt' (snd _ _) ((unary_to_binary.comp hk).comp ((fst _ _).comp (fst _ _)))
  exact bool_and' same (allWithInput (test := fun x m => m.all (fun r => decide (r < k x))) hp.snd' test)

theorem expand_poly {k : X → ℕ} {p : X → TableInput} (hk : ComputableInPolyTime k e encUnary)
    (hp : ComputableInPolyTime p e tableEncoding) :
    ComputableInPolyTime (fun x => TablePeeling.expand (k x) (p x)) e inputEncoding := by
  let data := hp.snd'
  have size := (ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.length AddressedEnvelope.namesEncoding)).comp data
  have listings := mapWithInput (f := fun x i => (tuple (k x) (p x).1 i, (p x).2.getD i []))
    (ComputableInPolyTime.range.comp size)
    ((tuple_poly (hk.comp (fst _ _)) (hp.fst'.comp (fst _ _)) (snd e encUnary)).prod
      ((listGetD (encA := AddressedEnvelope.namesEncoding) (encL := menusEncoding) []).comp
        ((data.comp (fst _ _)).prod (snd e encUnary))))
  exact (valid_poly hk hp).ite (hp.fst'.prod listings) (const (0,[]))

def language : Set Instance := {p | 3 ≤ p.1 ∧ RawAccepts p.1 p.2}

theorem reducible :
    Cslib.Complexity.PolyTimeReducible encoding destEncoding language
      {p : ℕ × TablePeeling.Input | ∃ h : 3 ≤ p.1, Accepts (show 0 < p.1 by omega) p.2} := by
  let f (p : Instance) := (p.1, TablePeeling.expand p.1 p.2)
  refine ⟨f,(fst encUnary tableEncoding).prod (expand_poly (fst ..) (snd ..)),?_⟩
  intro p
  change (3 ≤ p.1 ∧ RawAccepts p.1 p.2) ↔ ∃ h : 3 ≤ p.1, Accepts (show 0 < p.1 by omega) (expand p.1 p.2)
  exact ⟨fun ⟨h,yes⟩ => ⟨h,(expand_iff (k := p.1) (by omega) _).mpr yes⟩,
    fun ⟨h,yes⟩ => ⟨h,(expand_iff (k := p.1) (by omega) _).mp yes⟩⟩

/-- Giving the owner count in unary preserves PSPACE-completeness of
recognition from a winner table. Hardness already holds at three owners. -/
theorem complete : Cslib.Complexity.PSPACEComplete encoding language := by
  refine ⟨reducible.mem_PSPACE TablePeelingUniform.mem_PSPACE, ?_⟩
  apply (ExplicitTableHardness.pspaceHard (Function.Embedding.refl (Fin 3))).trans
  refine ⟨fun x => (3,x), (const 3).prod id', fun x => ?_⟩
  exact ⟨fun h => ⟨Nat.le_refl 3,h⟩, And.right⟩

end KFOL.Complexity.TablePeelingWinnerUniform
