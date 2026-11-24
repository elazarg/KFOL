module

public import Complexity.Computability.Complexity.Classes.Space.GeneralizedGeography.Membership
public import Complexity.Computability.Complexity.Classes.Alternation.Savitch
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! # Explicit polynomial-length games on consecutive blocks

A prover writes a certificate for a gate and the universal player selects a
child. Verifying a play needs only consecutive rounds: the previous gate
and child determine the current requested rows. This avoids an iteration
whose work space depends on a growing accumulator.
-/

@[expose] public section
namespace KFOL.Complexity.TablePeelingGame

open Cslib.Complexity Cslib.Complexity.GeneralizedGeography Turing.MultiTapeTM ComputableInPolyTime

abbrev Move := List Bool × List Bool
abbrev Previous := Option Move
abbrev moveEncoding := encPair (encList encBool) (encList encBool)
abbrev prevEncoding := encOption moveEncoding

/-- The two nonoverlapping blocks give all certificate bits to the prover
and all challenge bits to the opponent. -/
def roundMove (B : ℕ) (z : List Bool) : Move :=
  (moverBits B true z, moverBits B false (z.drop (2*B)))

def atRound (B : ℕ) (z : List Bool) (i : ℕ) : Move := roundMove B (z.drop (4*B*i))

def previous (B : ℕ) (z : List Bool) (i : ℕ) : Previous :=
  if i = 0 then none else some (atRound B z (i-1))

def prior (initial : Previous) (B : ℕ) (z : List Bool) (i : ℕ) : Previous :=
  if i = 0 then initial else previous B z i

/-- All local transitions and the final accepting position. -/
def check (step : Previous → Move → Bool) (ending : Previous → Bool)
    (B R : ℕ) (initial : Previous) (z : List Bool) : Bool :=
  ((List.range R).all fun i => step (prior initial B z i) (atRound B z i)) &&
    ending (prior initial B z R)

def Wins (step : Previous → Move → Bool) (ending : Previous → Bool) (B : ℕ) : ℕ → Previous → Prop
  | 0, p => ending p = true
  | r+1, p => ∃ a : List Bool, a.length = B ∧ ∀ b : List Bool, b.length = B →
    step p (a,b) = true ∧ Wins step ending B r (some (a,b))

private theorem move_shift (B : ℕ) (z : List Bool) (i : ℕ) :
    atRound B z (i+1) = atRound B (z.drop (4*B)) i := by
  simp only [atRound,List.drop_drop]
  rw [Nat.mul_succ, Nat.add_comm]

private theorem from_shift (p : Previous) (B : ℕ) (z : List Bool) (i : ℕ) :
    prior p B z (i+1) = prior (some (roundMove B z)) B (z.drop (4*B)) i := by
  cases i with
  | zero => simp [prior,previous,atRound]
  | succ i => simp [prior,previous,move_shift]

private theorem check_succ (step : Previous → Move → Bool) (ending : Previous → Bool)
    (B R : ℕ) (p : Previous) (z : List Bool) :
    check step ending B (R+1) p z = (step p (roundMove B z) &&
      check step ending B R (some (roundMove B z)) (z.drop (4*B))) := by
  simp only [check,List.range_succ_eq_map,List.all_cons,List.all_map,Function.comp_def,
    from_shift,move_shift,Bool.and_assoc]
  simp [atRound,prior]

/-- The exact alternating bit game evaluates the bounded block game. -/
theorem alternation_check (step : Previous → Move → Bool) (ending : Previous → Bool)
    (B R : ℕ) (p : Previous) :
    Alternation true (List.replicate (4*B*R) 1) (fun z => check step ending B R p z = true)
      ↔ Wins step ending B R p := by
  induction R generalizing p with
  | zero => simp [Wins,check,prior]
  | succ r ih =>
    rw [show 4*B*(r+1) = 2*B + (2*B + 4*B*r) by ring, List.replicate_add, List.replicate_add]
    let after := fun (a b rest : List Bool) =>
      step p (a,b) = true ∧ check step ending B r (some (a,b)) rest = true
    let choose := fun a (rest : List Bool) => after a (moverBits B false rest) (rest.drop (2*B))
    have first (z : List Bool) : check step ending B (r+1) p z = true ↔
        choose (moverBits B true z) (z.drop (2*B)) := by
      simp only [choose,after,check_succ,Bool.and_eq_true,roundMove,List.drop_drop]
      rw [show 2*B+2*B = 4*B by ring]
    rw [alternation_congr first, alternation_moverBits_true (F := choose)]
    unfold Wins
    apply exists_congr
    intro a
    apply and_congr_right
    intro _
    rw [show choose a = (fun rest => after a (moverBits B false rest) (rest.drop (2*B))) from rfl,
      alternation_moverBits_false (F := after a)]
    unfold after
    refine forall_congr' fun b => forall_congr' fun _ => ?_
    by_cases valid : step p (a,b) = true
    · simpa only [valid,true_and] using ih (some (a,b))
    · simp [Bool.eq_false_of_not_eq_true valid,alternation_const]

private theorem mover_take (B : ℕ) (side : Bool) (z : List Bool) (limit : ℕ) (h : 2*B ≤ limit) :
    moverBits B side (z.take limit) = moverBits B side z := by
  apply List.map_congr_left
  intro j hj
  have := List.mem_range.mp hj
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_take_of_lt (by split <;> omega)]

theorem atRound_take (B R i : ℕ) (hi : i < R) (z : List Bool) :
    atRound B (z.take (4*B*R)) i = atRound B z i := by
  have bound : 4*B*i+4*B ≤ 4*B*R := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hi
  simp only [atRound,roundMove,List.drop_take,List.drop_drop]
  rw [mover_take _ _ _ _ (by omega), mover_take _ _ _ _ (by omega)]

theorem check_take (step : Previous → Move → Bool) (ending : Previous → Bool)
    (B R : ℕ) (p : Previous) (z : List Bool) :
    check step ending B R p (z.take (4*B*R)) = check step ending B R p z := by
  have pre (i : ℕ) (hi : i ≤ R) : prior p B (z.take (4*B*R)) i = prior p B z i := by
    by_cases zero : i = 0
    · simp [prior,zero]
    · simp only [prior,previous,ite_eq_right zero, atRound_take B R (i-1) (by omega)]
  unfold check
  rw [pre _ le_rfl]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [pre i hi.le,atRound_take B R i hi]

variable {X : Type} {enc : X ↪ List Bool}

theorem roundMove_poly {B : X → ℕ} {z : X → List Bool} (hB : ComputableInPolyTime B enc encUnary)
    (hz : ComputableInPolyTime z enc encBits) :
    ComputableInPolyTime (fun x => roundMove (B x) (z x)) enc moveEncoding := by
  exact (computableInPolyTime_moverBits hB (.const true) hz).prod
    (computableInPolyTime_moverBits hB (.const false)
      (bitsDropWithInput hz (unary_mul.comp ((const 2).prod hB))))

@[fun_prop] theorem atRound_poly {B i : X → ℕ} {z : X → List Bool}
    (hB : ComputableInPolyTime B enc encUnary) (hz : ComputableInPolyTime z enc encBits)
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => atRound (B x) (z x) (i x)) enc moveEncoding := by
  apply roundMove_poly hB
  apply bitsDropWithInput hz
  fun_prop

@[fun_prop] theorem previous_poly {B i : X → ℕ} {z : X → List Bool}
    (hB : ComputableInPolyTime B enc encUnary) (hz : ComputableInPolyTime z enc encBits)
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun x => previous (B x) (z x) (i x)) enc prevEncoding := by
  unfold previous
  fun_prop

abbrev stepEncoding (e : X ↪ List Bool) := encPair e (encPair prevEncoding moveEncoding)
abbrev endEncoding (e : X ↪ List Bool) := encPair e prevEncoding

def verifier (step : X → Previous → Move → Bool) (ending : X → Previous → Bool)
    (B R : X → ℕ) (x : X × List Bool) := check (step x.1) (ending x.1) (B x.1) (R x.1) none x.2

/-- The transcript verifier is polynomial time whenever testing a local
transition, checking the terminal position, and listing the clocks are. -/
theorem verifier_poly {step : X → Previous → Move → Bool} {ending : X → Previous → Bool}
    {B R : X → ℕ} (hB : ComputableInPolyTime B enc encUnary) (hR : ComputableInPolyTime R enc encUnary)
    (hs : ComputableInPolyTime (fun x : X × Previous × Move => step x.1 x.2.1 x.2.2) (stepEncoding enc) encBool)
    (he : ComputableInPolyTime (fun x : X × Previous => ending x.1 x.2) (endEncoding enc) encBool) :
    ComputableInPolyTime (verifier step ending B R) (encPair enc encBits) encBool := by
  have same (b i : ℕ) (z : List Bool) : prior none b z i = previous b z i := by
    by_cases zero : i = 0 <;> simp [prior,previous,zero]
  unfold verifier check
  simp only [same]
  have arg := fst enc encBits
  have trace := snd enc encBits
  have all : ComputableInPolyTime (fun x : X × List Bool => (List.range (R x.1)).all fun i =>
      step x.1 (previous (B x.1) x.2 i) (atRound (B x.1) x.2 i)) (encPair enc encBits) encBool := by
    apply allWithInput (range.comp (hR.comp arg))
    let e := encPair (encPair enc encBits) encUnary
    have inp : ComputableInPolyTime (fun p : (X × List Bool) × ℕ => p.1.1) e enc := by fun_prop
    have bits : ComputableInPolyTime (fun p : (X × List Bool) × ℕ => p.1.2) e encBits := by fun_prop
    have i := snd (encPair enc encBits) encUnary
    exact hs.comp (inp.prod ((previous_poly (hB.comp inp) bits i).prod (atRound_poly (hB.comp inp) bits i)))
  exact bool_and.comp (all.prod (he.comp (arg.prod (previous_poly (hB.comp arg) trace (hR.comp arg)))))

/-- Polynomially many local rounds of polynomially many bits give a
polynomial-space recognition procedure for the winning predicate. -/
theorem mem_PSPACE {step : X → Previous → Move → Bool} {ending : X → Previous → Bool}
    {B R : X → ℕ} (hB : ComputableInPolyTime B enc encUnary) (hR : ComputableInPolyTime R enc encUnary)
    (hs : ComputableInPolyTime (fun x : X × Previous × Move => step x.1 x.2.1 x.2.2) (stepEncoding enc) encBool)
    (he : ComputableInPolyTime (fun x : X × Previous => ending x.1 x.2) (endEncoding enc) encBool)
    (clock : Polynomial ℕ) (bound : ∀ x, 2 * B x * R x ≤ clock.eval (enc x).length) :
    {x | Wins (step x) (ending x) (B x) (R x) none} ∈ PSPACE enc := by
  apply IsGameVerifier.mem_PSPACE (V := verifier step ending B R) (p := clock) (verifier_poly hB hR hs he)
  intro x
  have h : 4 * B x * R x ≤ 2 * clock.eval (enc x).length := by
    rw [show 4 * B x * R x = 2 * (2 * B x * R x) by ring]
    exact Nat.mul_le_mul_left _ (bound x)
  rw [← Nat.add_sub_cancel' h, List.replicate_add]
  rw [alternation_append_iff (fun z => by
    simp only [sum_replicate_one,verifier,check_take])]
  exact (alternation_check _ _ _ _ _).symm

end KFOL.Complexity.TablePeelingGame
