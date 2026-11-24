module

public import KFOL.Complexity.TablePeelingFrontend
public import Complexity.Computability.Complexity.Classes.Space.Closure

/-! # Clocks and the initial output test for the exact interpolation game -/

@[expose] public section
namespace KFOL.Complexity.TablePeelingClock

open Turing.MultiTapeTM ComputableInPolyTime TablePeeling Cslib.Complexity

/-- The owner header, then one bit of each of the two child masks for
every row and every role. -/
def blockWidth (K : ℕ) (x : Input) : ℕ := K + 2*x.2.length*K

def rounds (K : ℕ) (x : Input) : ℕ := x.2.length*K

/-- A required empty output is impossible, whereas an empty internal
mask is a free row in the split certificate. -/
def initialOk (K : ℕ) (x : Input) : Bool :=
  x.2.all (fun row => (List.range K).any (fun k => AddressedEnvelope.member k row.2))

theorem initialOk_iff (K : ℕ) (x : Input) :
    initialOk K x = true ↔ ∀ i, (bounds K x i).Nonempty := by
  simp only [initialOk,List.all_eq_true,List.any_eq_true,List.mem_range,AddressedEnvelope.member_iff]
  constructor
  · intro h i
    obtain ⟨r,hr,hit⟩ := h _ (List.getElem_mem i.isLt)
    exact ⟨⟨r,hr⟩,hit⟩
  · intro h row hit
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hit
    obtain ⟨r,good⟩ := h ⟨i,hi⟩
    exact ⟨r.val,r.isLt,good⟩

theorem initialOk_poly (K : ℕ) : ComputableInPolyTime (initialOk K) inputEncoding encBool := by
  apply allWithInput (snd encUnary (encList rowEncoding))
  apply anyWithInput (encA := encNat) (const (List.range K))
  let q := encPair inputEncoding rowEncoding
  have out := (snd AddressedPoint.menusEncoding AddressedEnvelope.namesEncoding).comp
    (snd inputEncoding rowEncoding)
  exact AddressedEnvelope.member_polyTime.comp ((snd q encNat).prod (out.comp (fst q encNat)))

theorem width_poly (K : ℕ) : ComputableInPolyTime (blockWidth K) inputEncoding encUnary := by
  have rows := (length_list rowEncoding).comp (snd encUnary (encList rowEncoding))
  exact unary_add.comp ((const K).prod
    (unary_mul.comp ((unary_mul.comp ((const 2).prod rows)).prod (const K))))

theorem rounds_poly (K : ℕ) : ComputableInPolyTime (rounds K) inputEncoding encUnary := by
  exact unary_mul.comp (((length_list rowEncoding).comp (snd encUnary (encList rowEncoding))).prod (const K))

noncomputable def clock (K : ℕ) : Polynomial ℕ := Polynomial.C (6*K*K) * (Polynomial.X + 1)^2

theorem clock_bound (K : ℕ) (x : Input) : 2 * blockWidth K x * rounds K x ≤ (clock K).eval (inputEncoding x).length := by
  let n := (inputEncoding x).length
  have rows : x.2.length ≤ n := (length_le_length_encList rowEncoding x.2).trans
    (length_le_encPair_right encUnary (encList rowEncoding) x)
  have row : x.2.length ≤ n+1 := by omega
  have half : K + 2*x.2.length*K ≤ (3*(n+1))*K := by
    calc K + 2*x.2.length*K = (1+2*x.2.length)*K := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  calc
    2 * blockWidth K x * rounds K x ≤ 2 * ((3*(n+1))*K) * ((n+1)*K) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 half) (Nat.mul_le_mul_right K row)
    _ = (clock K).eval (inputEncoding x).length := by simp [clock,n]; ring

end KFOL.Complexity.TablePeelingClock
