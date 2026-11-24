module

public import KFOL.Complexity.TablePeelingUniformRuntime

/-! # Uniform polynomial-space interpolation

The machine reads the owner count in unary and the identifier of each owner
in a menu in binary. It scans the roles for a local split and uses a
quartic-length alternating transcript for an entire interpolation test.
-/

@[expose] public section
namespace KFOL.Complexity.TablePeelingUniform

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity TablePeelingClock TablePeelingUniformGate
open TablePeelingGame TablePeelingMasks

theorem mem_PSPACE : language ∈ PSPACE encoding := by
  let yes := fun x : Instance => initialOk x.1 x.2 = true
  have game := TablePeelingGame.mem_PSPACE (step := fun x : Instance => gateFast x.1 x.2)
    (ending := fun x : Instance => endTest x.1 x.2) uWidth_poly uRounds_poly
    gateFast_poly uniform_end_poly uniformClock uniform_bound
  convert inter_mem_PSPACE (P_subset_PSPACE start_P) game using 1
  ext x
  change (∃ h : 3 ≤ x.1, TablePeeling.Accepts _ x.2) ↔
    (3 ≤ x.1 ∧ yes x) ∧ Wins (gateFast x.1 x.2) (endTest x.1 x.2) _ _ none
  by_cases enough : 3 ≤ x.1
  · let three : Fin 3 ↪ Fin x.1 := Fin.castLEEmb enough
    have same : gateFast x.1 x.2 = gate x.1 x.2 := by
      funext p m
      exact Bool.eq_iff_iff.mpr (gateFast_iff three x.2 p m)
    rw [same]
    have character := TablePeelingSemantics.accepts_iff_wins (by omega : 0 < x.1) x.2
    exact ⟨fun ⟨_,ht⟩ => ⟨⟨enough,(character.mp ht).1⟩,(character.mp ht).2⟩,
      fun ⟨⟨_,start⟩,win⟩ => ⟨enough,character.mpr ⟨start,win⟩⟩⟩
  · simp [enough]

/-- In uniform interpolation the fixed three-owner sublanguage already
contains the quantified-formula reduction. -/
theorem pspaceComplete : PSPACEComplete encoding language := by
  have hard := (ExplicitTableHardness.pspaceHard (Function.Embedding.refl (Fin 3))).trans
    (TablePeeling.raw_reducible (by decide : 0 < 3))
  apply And.intro mem_PSPACE (hard.trans _)
  refine ⟨fun x => (3,x), (const 3).prod id', fun x => ?_⟩
  exact ⟨fun h => ⟨Nat.le_refl 3,h⟩, fun ⟨_,h⟩ => h⟩

end KFOL.Complexity.TablePeelingUniform
