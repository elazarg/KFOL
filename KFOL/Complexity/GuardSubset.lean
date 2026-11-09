module

public import KFOL.Algorithms.GuardWords
public import KFOL.Complexity.Language

/-! # A machine-certified prerequisite subset test on membership words -/

@[expose] public section

namespace KFOL.Complexity.GuardSubset

open Algorithms.GuardWords
open _root_.Complexity _root_.Complexity.Cobham

private theorem caseBit_value (x yes no : List Bool) :
    caseBit₀ x yes no = (bif x.headD false then yes else no) := by
  cases x with
  | nil => rfl
  | cons b x => cases b <;> rfl

private theorem andBit_value (x y : List Bool) :
    andBit x y = [x.headD false && y.headD false] := by
  simp only [andBit, caseBit_value]
  cases x.headD false <;> cases y.headD false <;> rfl

private theorem orBit_value (x y : List Bool) :
    orBit x y = [x.headD false || y.headD false] := by
  simp only [orBit, caseBit_value]
  cases x.headD false <;> cases y.headD false <;> rfl

private theorem notBit_value (x : List Bool) : notBit x = [!x.headD false] := by
  simp only [notBit, caseBit_value]
  cases x.headD false <;> rfl

private theorem bitAt_value (r x : List Bool) : bitAt r x = [readBit x r.length] := by
  rw [bitAt, caseBit_value]
  have he : (x.drop r.length).headD false = readBit x r.length := by
    simp only [List.headD_eq_head?_getD, List.head?_drop, readBit]
  rw [he]
  cases readBit x r.length <;> rfl

private def stepFn (v : Fin 4 → List Bool) : List Bool :=
  subsetStep (v 0) (v 1) (v 2) (v 3)

private theorem stepFn_cobham : Cobham stepFn := by
  have h : Cobham (fun v : Fin 4 → List Bool => andBit (v 1)
      (orBit (notBit (bitAt (v 0) (v 2))) (bitAt (v 0) (v 3)))) :=
    Cobham.andFn (.proj 1)
    (Cobham.orFn (Cobham.notFn (Cobham.comp₂ bitAtFn (.proj 0) (.proj 2)))
      (Cobham.comp₂ bitAtFn (.proj 0) (.proj 3)))
  exact h.of_eq (fun v => by
    simp only [bitAt_value, notBit_value, orBit_value, andBit_value, List.headD_cons]
    rfl)

private theorem rec_eq (r : List Bool) (v : Fin 2 → List Bool) :
    recNotation (fun _ : Fin 2 → List Bool => [true]) stepFn stepFn r v =
      subsetScan r (v 0) (v 1) := by
  induction r with
  | nil => rfl
  | cons b r ih =>
    simp only [recNotation_cons, Bool.cond_self, stepFn, Fin.cons_zero]
    rw [ih]
    rfl

/-- A single bounded recursion visits each input position once. Its state is
always one bit, so the Cobham length bound is the constant one-bit word. -/
theorem subsetScan_cobham : Cobham fun v : Fin 2 → List Bool =>
    subsetScan (v 0) (v 0) (v 1) := by
  have hrec : Cobham fun v : Fin 3 → List Bool =>
      recNotation (fun _ : Fin 2 → List Bool => [true]) stepFn stepFn (v 0) (Fin.tail v) :=
    Cobham.boundedRec (Cobham.const [true]) stepFn_cobham stepFn_cobham
      (Cobham.const [true]) (fun r v => by rw [rec_eq, subsetScan_length]; rfl)
  have hparams : ∀ i : Fin 3,
      Cobham (fun v : Fin 2 → List Bool => if i = 2 then v 1 else v 0) := by
    intro i
    by_cases hi : i = 2
    · simp only [hi, ite_true]; exact .proj 1
    · simp only [hi, ite_false]; exact .proj 0
  exact (Cobham.comp hrec hparams).of_eq (fun v => by rw [rec_eq]; rfl)

/-- The actual independently defined word test belongs to Cobham's class. -/
theorem subsetFn_cobham : Cobham subsetFn := by
  have h := Cobham.andFn (lenEqFlag_mem (.proj 0) (.proj 1)) subsetScan_cobham
  exact h.of_eq (fun v => by
    have hlen : lenEqFlag (v 0) (v 1) = [decide ((v 0).length = (v 1).length)] := by
      rcases lenEqFlag_flag (v 0) (v 1) with he | he
      · have hp := (lenEqFlag_eq_true_iff _ _).mp he
        simpa only [hp, decide_true] using he
      · rw [he]
        have hn : (v 0).length ≠ (v 1).length := by
          intro hh
          have ht := (lenEqFlag_eq_true_iff _ _).mpr hh
          rw [he] at ht
          cases ht
        simp [hn]
    rw [andBit_value, hlen]
    rfl)

/-- Polynomial time in the imported Turing-machine model, uniformly in word
width. No theorem about the complete table algorithms is claimed here. -/
theorem subsetFn_mem_FPn : FPn subsetFn := cobham_iff_FPn.mp subsetFn_cobham

end KFOL.Complexity.GuardSubset
