module

public import KFOL.Complexity.TablePeelingSpace

/-! # Interpolation instances with the owner count in the input -/

@[expose] public section
namespace KFOL.Complexity.TablePeelingUniform

open Turing.MultiTapeTM ComputableInPolyTime TablePeeling TablePeelingClock AddressedEnvelope

abbrev Instance := ℕ × TablePeeling.Input
abbrev encoding := encPair encUnary TablePeeling.inputEncoding

def language : Set Instance := {x | ∃ h : 3 ≤ x.1, Accepts (by omega : 0 < x.1) x.2}

theorem uWidth_poly : ComputableInPolyTime (fun x : Instance => blockWidth x.1 x.2) encoding encUnary := by
  have count := (length_list TablePeeling.rowEncoding).comp ((snd _ _).comp (snd encUnary TablePeeling.inputEncoding))
  let k := fst encUnary TablePeeling.inputEncoding
  exact unary_add' k (unary_mul' (unary_mul' (const 2) count) k)

theorem uRounds_poly : ComputableInPolyTime (fun x : Instance => rounds x.1 x.2) encoding encUnary := by
  have count := (length_list TablePeeling.rowEncoding).comp ((snd _ _).comp (snd encUnary TablePeeling.inputEncoding))
  exact unary_mul' count (fst encUnary TablePeeling.inputEncoding)

private theorem initial_poly : ComputableInPolyTime (fun x : Instance => initialOk x.1 x.2) encoding encBool := by
  let k := fst encUnary TablePeeling.inputEncoding
  let rows := (snd _ _).comp (snd encUnary TablePeeling.inputEncoding)
  let ext := encPair encoding TablePeeling.rowEncoding
  apply allWithInput rows
  apply anyWithInput (encA := encUnary) (ComputableInPolyTime.range.comp (k.comp (fst _ _)))
  have out := (snd AddressedPoint.menusEncoding namesEncoding).comp (snd encoding TablePeeling.rowEncoding)
  exact member_polyTime.comp ((unary_to_binary.comp (snd ext encUnary)).prod (out.comp (fst ext encUnary)))

theorem start_P : {x : Instance | 3 ≤ x.1 ∧ initialOk x.1 x.2 = true} ∈ Cslib.Complexity.P encoding := by
  have cut : ComputableInPolyTime (fun x : Instance => decide (3 ≤ x.1)) encoding encBool := by fun_prop
  exact ⟨_,bool_and' cut initial_poly,fun x => by simp⟩

/-- The complete bit transcript is quartic in the combined unary owner
count and length of the encoded sample. -/
noncomputable def uniformClock : Polynomial ℕ := 6 * (Polynomial.X + 1)^4

theorem uniform_bound (x : Instance) : 2 * blockWidth x.1 x.2 * rounds x.1 x.2 ≤
    uniformClock.eval (encoding x).length := by
  let n := (encoding x).length
  have hK : x.1 ≤ n := by
    have := length_le_encPair_left encUnary TablePeeling.inputEncoding x
    simpa only [encUnary_apply,List.length_replicate] using this
  have hu : (TablePeeling.inputEncoding x.2).length ≤ n :=
    length_le_encPair_right encUnary TablePeeling.inputEncoding x
  have h := clock_bound x.1 x.2
  simp only [clock,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] at h
  calc
    _ ≤ _ := h
    _ ≤ 6*(n+1)*(n+1)*(n+1)^2 := by
      gcongr <;> omega
    _ = _ := by simp [uniformClock,n]; ring

end KFOL.Complexity.TablePeelingUniform
