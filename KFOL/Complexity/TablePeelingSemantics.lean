module

public import KFOL.Complexity.TablePeelingBlocks
public import KFOL.Complexity.TablePeelingClock
public import KFOL.Complexity.TablePeelingMasks

/-! # The finite split game decides exact interpolation

The prover's bit block can request every owner and every pair of goals.
The opponent's first bit selects one child. The initial nonempty-output
test distinguishes an impossible empty output from an unconstrained child.
-/

@[expose] public section
namespace KFOL.Complexity.TablePeelingSemantics

open TablePeelingGame TablePeelingMasks TablePeelingClock TablePeelingBlocks TablePeeling Core.ExactSplit
attribute [local instance] Equational.coreStructure

private theorem packed_goal {K n : ℕ} (r : Fin K) (L R : Goal (Fin n) (Fin K)) (reply : List Bool) (b : Bool) :
    toGoal K n (childBit K (pack r L R,reply) b) = (if b then R else L) := by
  apply Finset.ext
  intro p
  have entry : p ∈ toGoal K n (childBit K (pack r L R,reply) b) ↔
      childBit K (pack r L R,reply) b p.1.val p.2.val = true := by simp [toGoal]
  rw [entry]
  change (pack r L R).getD _ false = true ↔ _
  rw [pack_child r L R b p.1 p.2,decide_eq_true_eq]

private theorem previous_goal (K : ℕ) (x : TablePeeling.Input) (move : Move) :
    toGoal K x.2.length (goalBit K x (some move)) =
      toGoal K x.2.length (childBit K move (move.2.getD 0 false)) := rfl

private theorem reply_first (B : ℕ) (positive : 0 < B) (b : Bool) :
    (List.replicate B b).getD 0 false = b := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simp [List.replicate_succ]

/-- The concrete block game and abstract table splits have the same winning
positions, including positions with malformed guesses in their history. -/
theorem wins_iff_plays {K : ℕ} (hk : 0 < K) (x : TablePeeling.Input) (d : ℕ) (p : Previous) :
    Wins (gate K x) (endTest K x) (blockWidth K x) d p ↔
      Plays (values hk x) d (toGoal K x.2.length (goalBit K x p)) := by
  let : Nonempty (Fin K) := ⟨⟨0,hk⟩⟩
  let B := blockWidth K x
  have pos : 0 < B := by dsimp [B,blockWidth]; omega
  induction d generalizing p with
  | zero => exact endTest_iff hk x p
  | succ d ih =>
    rw [plays_succ_iff]
    constructor
    · rintro ⟨a,_,all⟩
      let reply := fun b : Bool => List.replicate B b
      have len (b : Bool) : (reply b).length = B := List.length_replicate
      have first (b : Bool) : (reply b).getD 0 false = b := reply_first B pos b
      let m : Move := (a,reply false)
      obtain ⟨valid,l⟩ := all m.2 (len false)
      obtain ⟨_,r⟩ := all (reply true) (len true)
      refine ⟨⟨ownerId K m,owner_lt hk m⟩,_,_,(gate_iff hk x p m).mp valid,?_,?_⟩
      · have left := (ih (some m)).mp l
        rwa [previous_goal,show m.2.getD 0 false = false from first false] at left
      · have right := (ih (some (a,reply true))).mp r
        rw [previous_goal,show (a,reply true).2.getD 0 false = true from first true] at right
        exact right
    · rintro ⟨r,L,R,valid,left,right⟩
      let a := pack r L R
      refine ⟨a,pack_length r L R,fun b _ => ?_⟩
      let m : Move := (a,b)
      have owner : (⟨ownerId K m,owner_lt hk m⟩ : Fin K) = r := Fin.ext (header_select r L R)
      have lgoal : toGoal K x.2.length (childBit K m false) = L := packed_goal r L R b false
      have rgoal : toGoal K x.2.length (childBit K m true) = R := packed_goal r L R b true
      constructor
      · apply (gate_iff hk x p m).mpr
        rwa [owner,lgoal,rgoal]
      · apply (ih (some m)).mpr
        rw [previous_goal]
        by_cases bit : m.2.getD 0 false = true
        · rwa [bit,rgoal]
        · rwa [Bool.eq_false_of_not_eq_true bit,lgoal]

private theorem initial_fiber (K : ℕ) (x : TablePeeling.Input) (i : Fin x.2.length) :
    fiber (toGoal K x.2.length (goalBit K x none)) i = bounds K x i := by
  ext r
  simp [fiber,toGoal,goalBit,bounds,allowed]

/-- Exact interpolation reduces to the conjunction of the explicit initial
row-validity test and the polynomial-duration local game. -/
theorem accepts_iff_wins {K : ℕ} (hk : 0 < K) (x : TablePeeling.Input) :
    Accepts hk x ↔ initialOk K x = true ∧
      Wins (gate K x) (endTest K x) (blockWidth K x) (rounds K x) none := by
  let G := toGoal K x.2.length (goalBit K x none)
  have bound : G.card ≤ rounds K x := by
    simpa [rounds] using Finset.card_le_univ G
  rw [initialOk_iff,wins_iff_plays hk,plays_iff_word _ _ G bound]
  constructor
  · rintro ⟨t,ht⟩
    refine ⟨fun i => (ht i) ▸ (t.realize (values hk x i)).property,t,fun i _ => ?_⟩
    exact (ht i).trans (initial_fiber K x i).symm
  · rintro ⟨valid,t,word⟩
    refine ⟨t,fun i => ?_⟩
    exact ((word i) ((initial_fiber K x i).symm ▸ valid i)).trans (initial_fiber K x i)

end KFOL.Complexity.TablePeelingSemantics
