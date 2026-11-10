module
public import KFOL.Complexity.CircuitGeneratorReferences
public import KFOL.Complexity.CircuitCodec
/-! The complete native generator for the original sparse-CNF reset DAG, followed by its exact original shared-graph word encoder. -/

@[expose] public section
namespace KFOL.Complexity.CircuitGenerator
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.Reductions
open Circuit.ResetCNF
open CircuitMachine
open ResetUnionReduction (cnfEncoding)

@[fun_prop] theorem baseline_gates_polyTime : ComputableInPolyTime
    (fun φ => (baselineBuild φ).gates.map viewGate) cnfEncoding gatesEncoding := by
  have hlength := (lengthBinary_polyTime gateEncoding).comp inputs_polyTime
  have hnodes := combNodes_polyTime.comp (railRefs_polyTime.prod ((const 0).prod hlength))
  have h := listAppend' inputs_polyTime hnodes
  convert h using 1
  funext φ
  simpa only [baselineBuild, Function.comp_def, List.length_map] using (view_buildRightComb (railRefs φ) 0 (inputs φ)).1

@[fun_prop] theorem baseline_output_polyTime : ComputableInPolyTime
    (fun φ => (baselineBuild φ).output) cnfEncoding encNat := by
  have hgates := (lengthBinary_polyTime gateEncoding).comp inputs_polyTime
  have hrefs := (lengthBinary_polyTime encNat).comp railRefs_polyTime
  have h := lastRef_polyTime.comp ((const 0).prod (hgates.prod hrefs))
  convert h using 1
  funext φ
  simpa only [baselineBuild, Function.comp_def, List.length_map] using (view_buildRightComb (railRefs φ) 0 (inputs φ)).2

@[fun_prop] theorem right_gates_polyTime : ComputableInPolyTime
    (fun φ => (rightBuild φ).gates.map viewGate) cnfEncoding gatesEncoding := by
  have hlength := (lengthBinary_polyTime gateEncoding).comp baseline_gates_polyTime
  have hnodes := consistencyNodes_polyTime.comp
    (pairs_polyTime.prod ((const 1).prod (baseline_output_polyTime.prod hlength)))
  have h := listAppend' baseline_gates_polyTime hnodes
  convert h using 1
  funext φ
  simpa only [rightBuild, Function.comp_def, List.length_map] using
    (view_buildConsistency (pairs φ) 1 (baselineBuild φ).output (baselineBuild φ).gates).1

@[fun_prop] theorem right_output_polyTime : ComputableInPolyTime
    (fun φ => (rightBuild φ).output) cnfEncoding encNat := by
  have hlength := (lengthBinary_polyTime gateEncoding).comp baseline_gates_polyTime
  have hcount := (lengthBinary_polyTime (encPair encNat encNat)).comp pairs_polyTime
  have h := lastRef_polyTime.comp (baseline_output_polyTime.prod
    (hlength.prod (binary_mul' (const 3) hcount)))
  convert h using 1
  funext φ
  simpa only [rightBuild, Function.comp_def, List.length_map] using
    (view_buildConsistency (pairs φ) 1 (baselineBuild φ).output (baselineBuild φ).gates).2

@[fun_prop] theorem left_gates_polyTime : ComputableInPolyTime
    (fun φ => (leftBuild φ).gates.map viewGate) cnfEncoding gatesEncoding := by
  have hlength := (lengthBinary_polyTime gateEncoding).comp right_gates_polyTime
  have hnodes := cnfNodes_polyTime.comp
    (clauseRefs_polyTime.prod ((const 1).prod ((const 0).prod hlength)))
  have h := listAppend' right_gates_polyTime hnodes
  convert h using 1
  funext φ
  simpa only [leftBuild, Function.comp_def, List.length_map] using
    (view_buildCNF (clauseRefs φ) 1 0 (rightBuild φ).gates).1

@[fun_prop] theorem left_output_polyTime : ComputableInPolyTime
    (fun φ => (leftBuild φ).output) cnfEncoding encNat := by
  have hlength := (lengthBinary_polyTime gateEncoding).comp right_gates_polyTime
  have h := prefixOutput_polyTime.comp
    (clauseRefs_polyTime.prod ((const 1).prod ((const 0).prod hlength)))
  convert h using 1
  funext φ
  simpa only [leftBuild, Function.comp_def, List.length_map] using
    (view_buildCNF (clauseRefs φ) 1 0 (rightBuild φ).gates).2

/-- The original sparse CNF produces its original shared DAG in native
polynomial time, retaining every cache edge and all binary source names. -/
@[fun_prop] theorem reduction_polyTime : ComputableInPolyTime
    (fun φ => view (equation φ)) cnfEncoding equationEncoding := by
  have hlast := resetGate_polyTime.comp (left_output_polyTime.prod right_output_polyTime)
  have hgates := listAppend' left_gates_polyTime (cons' hlast (const []))
  have hlength := (lengthBinary_polyTime gateEncoding).comp left_gates_polyTime
  have h := hgates.prod (hlength.prod right_output_polyTime)
  convert h using 1
  funext φ
  simp only [view, equation, Circuit.emit, List.map_append, List.map_cons, List.map_nil,
    view_reset, List.length_map, Function.comp_def]

/-- Exact original DAG word output. This is a native-machine resource theorem,
not merely an abstract size bound or the polynomial-time generation of a tree
obtained by expanding the circuit. -/
@[fun_prop] theorem encoded_reduction_polyTime : ComputableInPolyTime
    (fun φ => Circuit.Code.encode Reset.Symbol (equation φ)) cnfEncoding encBits := by
  have h := CircuitMachine.encodeData_polyTime.comp reduction_polyTime
  simpa only [Function.comp_def, CircuitMachine.encodeData_view] using h
end KFOL.Complexity.CircuitGenerator
