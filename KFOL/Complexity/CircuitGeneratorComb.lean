module

public import KFOL.Complexity.CircuitGeneratorRecords
public import KFOL.Reductions.Circuits.Builder
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! Static cache positions for right combs, with exact transport of the original shared builder and native polynomial runtime. -/

@[expose] public section
namespace KFOL.Complexity.CircuitGenerator
open Turing.MultiTapeTM ComputableInPolyTime
open CircuitMachine

abbrev Gates := List (RawGate Reset.Symbol)
noncomputable abbrev gatesEncoding := encList gateEncoding

/-- The last cache reference after emitting a fixed number of new gates. -/
def lastRef (base offset count : ℕ) : ℕ :=
  if count = 0 then base else offset + count - 1

/-- Right-comb nodes in their original topological emission order. All indices
are positions in the existing cache, including when an operand is reused. -/
def combNodes (refs : List ℕ) (base offset : ℕ) : Gates :=
  (refs.reverse.zipIdx offset).map fun p =>
    resetGate p.1 (if p.2 = offset then base else p.2 - 1)

@[simp] theorem combNodes_nil (base offset : ℕ) : combNodes [] base offset = [] := rfl
@[simp] theorem length_combNodes (refs : List ℕ) (base offset : ℕ) :
    (combNodes refs base offset).length = refs.length := by simp [combNodes]

theorem combNodes_cons (head : ℕ) (refs : List ℕ) (base offset : ℕ) :
    combNodes (head :: refs) base offset = combNodes refs base offset ++
      [resetGate head (lastRef base offset refs.length)] := by
  simp only [combNodes, List.reverse_cons, List.zipIdx_append, List.map_append,
    List.length_reverse, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil]
  congr 2
  simp only [lastRef]
  split_ifs <;> congr 1 <;> omega

/-- Exact transport of the original shared right-comb builder. -/
theorem view_buildRightComb (refs : List ℕ) (base : ℕ)
    (gates : List (Circuit.Gate Reset.Symbol ℕ)) :
    (Circuit.buildRightComb refs base gates).gates.map viewGate =
      gates.map viewGate ++ combNodes refs base gates.length ∧
    (Circuit.buildRightComb refs base gates).output = lastRef base gates.length refs.length := by
  induction refs with
  | nil => simp [Circuit.buildRightComb, lastRef]
  | cons head refs ih =>
    constructor
    · simp only [Circuit.buildRightComb, Circuit.emit, List.map_append,
        List.map_cons, List.map_nil, view_reset, ih.1, ih.2, combNodes_cons, List.append_assoc]
    · simp only [Circuit.buildRightComb, Circuit.output_emit, Circuit.length_buildRightComb,
        List.length_cons, lastRef, Nat.add_one_ne_zero, ite_false]
      omega

noncomputable abbrev combEncoding := encPair (encList encNat) (encPair encNat encNat)

@[fun_prop] theorem lastRef_polyTime : ComputableInPolyTime
    (fun p : ℕ × (ℕ × ℕ) => lastRef p.1 p.2.1 p.2.2)
    (encPair encNat (encPair encNat encNat)) encNat := by
  have hb : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => p.1)
      (encPair encNat (encPair encNat encNat)) encNat := by fun_prop
  have ho : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => p.2.1)
      (encPair encNat (encPair encNat encNat)) encNat := by fun_prop
  have hn : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ) => p.2.2)
      (encPair encNat (encPair encNat encNat)) encNat := by fun_prop
  simpa only [lastRef, decide_eq_true_eq, Function.comp_def] using
    (decide_eq' hn (const 0)).ite hb (binary_sub' (binary_add.comp (ho.prod hn)) (const 1))

@[fun_prop] theorem combNodes_polyTime : ComputableInPolyTime
    (fun p : List ℕ × (ℕ × ℕ) => combNodes p.1 p.2.1 p.2.2)
    combEncoding gatesEncoding := by
  have hr := (fst (encList encNat) (encPair encNat encNat)).listReverseWithInput
  have hz := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.zipIdx encNat)).comp hr
  have hoff : ComputableInPolyTime
      (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) => p.1.2.2)
      (encPair combEncoding (encPair encNat encUnary)) encNat := by fun_prop
  have hbase : ComputableInPolyTime
      (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) => p.1.2.1)
      (encPair combEncoding (encPair encNat encUnary)) encNat := by fun_prop
  have hidx : ComputableInPolyTime
      (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) => p.2.2)
      (encPair combEncoding (encPair encNat encUnary)) encNat := by
    exact unary_to_binary.comp (by fun_prop)
  have href : ComputableInPolyTime
      (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) => p.2.1)
      (encPair combEncoding (encPair encNat encUnary)) encNat := by fun_prop
  have hright := (decide_eq' hidx (const 0)).ite hbase
    (binary_sub' (binary_add.comp (hoff.prod hidx)) (const 1))
  have hnode : ComputableInPolyTime
      (fun p : (List ℕ × (ℕ × ℕ)) × (ℕ × ℕ) =>
        resetGate p.2.1 (if p.2.2 = 0 then p.1.2.1 else p.1.2.2 + p.2.2 - 1))
      (encPair combEncoding (encPair encNat encUnary)) gateEncoding := by
    simpa only [decide_eq_true_eq, Function.comp_def] using
      resetGate_polyTime.comp (href.prod hright)
  have h := mapWithInput (f := fun (p : List ℕ × (ℕ × ℕ)) (item : ℕ × ℕ) =>
    resetGate item.1 (if item.2 = 0 then p.2.1 else p.2.2 + item.2 - 1)) hz hnode
  convert h using 1
  funext p
  rw [combNodes, List.zipIdx_eq_map_add]
  simp only [List.map_map, Function.comp_def]
  congr 1
  funext item
  split_ifs <;> congr 1 <;> omega
end KFOL.Complexity.CircuitGenerator
