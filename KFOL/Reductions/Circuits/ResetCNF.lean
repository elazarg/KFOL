module

public import KFOL.Reductions.Circuits.Builder
public import KFOL.Reductions.RawFolds
public import KFOL.Reset.Chain
public import Mathlib.Data.List.GetD

/-! Actual sparse-input native reset DAG for the CNF reduction. There is one
shared gate list; all clause occurrences of the preceding output are refs. -/

@[expose] public section

namespace KFOL.Circuit.ResetCNF

open KFOL.Reductions

private theorem literalName_mem_inputNames (formula : CNF) (i : ℕ)
    (hi : i ∈ ResetUnion.support formula) (sign : Bool) : ResetUnion.literalName (i, sign) ∈ inputNames formula := by
  apply List.mem_cons_of_mem
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨i, hi, ?_⟩
  cases sign <;> simp

theorem literalRef_lt (formula : CNF) (i : ℕ) (hi : i ∈ ResetUnion.support formula) (sign : Bool) :
    literalRef formula (i, sign) < (inputs formula).length := by
  rw [inputs, List.length_map]
  exact List.idxOf_lt_length_iff.mpr (literalName_mem_inputNames formula i hi sign)

@[simp] theorem length_pairs (formula : CNF) : (pairs formula).length = (ResetUnion.support formula).length := by
  simp [pairs]

@[simp] theorem length_railRefs (formula : CNF) : (railRefs formula).length = 2 * (ResetUnion.support formula).length := by
  have h (ps : List (ℕ × ℕ)) : (ps.flatMap (fun p => [p.1, p.2])).length = 2 * ps.length := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega
  rw [railRefs, h, length_pairs]

@[simp] theorem length_inputs (formula : CNF) : (inputs formula).length = 2 + 2 * (ResetUnion.support formula).length := by
  have h (indices : List ℕ) : (indices.flatMap (fun i =>
      [ResetUnion.literalName (i, true), ResetUnion.literalName (i, false)])).length = 2 * indices.length := by
    induction indices with
    | nil => rfl
    | cons i indices ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega
  simp only [inputs, inputNames, List.length_map, List.length_cons, h]
  omega

@[simp] theorem length_clauseRefs_flatten (formula : CNF) : (clauseRefs formula).flatten.length = formula.flatten.length := by
  rw [clauseRefs, ← List.map_flatten, List.length_map]

private theorem inputs_valid (formula : CNF) : ValidFrom 0 (inputs formula) := by
  have h (position : ℕ) (names : List ℕ) : ValidFrom position (names.map (Gate.input (σ := Reset.Symbol))) := by
    induction names generalizing position with
    | nil => trivial
    | cons j names ih => exact ⟨trivial, ih _⟩
  exact h _ _

private theorem refs_lt (formula : CNF) : ∀ ref ∈ railRefs formula, ref < (inputs formula).length := by
  intro ref hr
  obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  rcases List.mem_cons.mp hr with rfl | hr
  · exact literalRef_lt formula i hi true
  · have he := List.mem_singleton.mp hr
    subst ref
    exact literalRef_lt formula i hi false

private theorem baseline_valid (formula : CNF) :
    ValidFrom 0 (baselineBuild formula).gates ∧ (baselineBuild formula).output < (baselineBuild formula).gates.length := by
  apply valid_buildRightComb _ _ _ (inputs_valid formula)
  · rw [length_inputs]; omega
  · exact refs_lt formula

private theorem right_valid (formula : CNF) :
    ValidFrom 0 (rightBuild formula).gates ∧ (rightBuild formula).output < (rightBuild formula).gates.length := by
  obtain ⟨hW, hWout⟩ := baseline_valid formula
  have hlen : (inputs formula).length ≤ (baselineBuild formula).gates.length := by
    rw [baselineBuild, length_buildRightComb]
    omega
  apply valid_buildConsistency _ _ _ _ hW
  · have hi : 1 < (inputs formula).length := by rw [length_inputs]; omega
    exact lt_of_lt_of_le hi hlen
  · exact hWout
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact ⟨lt_of_lt_of_le (literalRef_lt formula i hi true) hlen,
      lt_of_lt_of_le (literalRef_lt formula i hi false) hlen⟩

private theorem left_valid (formula : CNF) :
    ValidFrom 0 (leftBuild formula).gates ∧ (leftBuild formula).output < (leftBuild formula).gates.length := by
  obtain ⟨hR, _⟩ := right_valid formula
  have hlen : (inputs formula).length ≤ (rightBuild formula).gates.length := by
    rw [rightBuild, length_buildConsistency, baselineBuild, length_buildRightComb]
    omega
  apply valid_buildCNF _ _ _ _ hR
  · have hi : 1 < (inputs formula).length := by rw [length_inputs]; omega
    exact lt_of_lt_of_le hi hlen
  · have hi : 0 < (inputs formula).length := by rw [length_inputs]; omega
    exact lt_of_lt_of_le hi hlen
  · intro c hc ref hr
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hc
    obtain ⟨literal, hl, rfl⟩ := List.mem_map.mp hr
    exact lt_of_lt_of_le (literalRef_lt formula literal.1
      (ResetUnion.literal_mem_support formula C hC literal hl) literal.2) hlen

/- All generated references are strict-prefix refs, and both outputs are
actual gates, for every CNF including empty clauses and empty conjunctions. -/
theorem equation_wellFormed (formula : CNF) : (equation formula).WellFormed := by
  obtain ⟨hA, hAout⟩ := left_valid formula
  obtain ⟨_, hRout⟩ := right_valid formula
  have hlen : (rightBuild formula).gates.length ≤ (leftBuild formula).gates.length := by
    rw [leftBuild, length_buildCNF]
    omega
  have hright : (rightBuild formula).output < (leftBuild formula).gates.length := lt_of_lt_of_le hRout hlen
  constructor
  · apply validFrom_emit _ _ hA
    exact (validAt_reset _ _ _).mpr ⟨hAout, hright⟩
  · constructor
    · change (leftBuild formula).gates.length < ((leftBuild formula).gates ++ [_]).length
      simp
    · change (rightBuild formula).output < ((leftBuild formula).gates ++ [_]).length
      simp only [List.length_append, List.length_singleton]
      omega

/- Exact original DAG node count:2+2N input nodes and5N+2L+1 reset nodes. -/
theorem equation_gate_count (formula : CNF) :
    (equation formula).gates.length = 7 * (ResetUnion.support formula).length + 2 * formula.flatten.length + 3 := by
  change (emit (leftBuild formula).gates _).gates.length = _
  rw [length_emit, leftBuild, length_buildCNF, rightBuild, length_buildConsistency,
    baselineBuild, length_buildRightComb, length_inputs, length_pairs, length_railRefs, length_clauseRefs_flatten]
  omega


private theorem lookup_append {M : Type*} (cache suffix : List M) (i : ℕ) (value : M)
    (h : cache[i]? = some value) : (cache ++ suffix)[i]? = some value := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

theorem runFrom_inputs {M : Type*} [(Equational.language Reset.Symbol).Structure M]
    (valuation : ℕ → M) (names : List ℕ) (cache : List M) :
    runFrom valuation (names.map (Gate.input (σ := Reset.Symbol))) cache = some (cache ++ names.map valuation) := by
  induction names generalizing cache with
  | nil => simp [runFrom]
  | cons j names ih =>
    change runFrom valuation (names.map Gate.input) (cache ++ [valuation j]) = _
    simpa only [List.map_cons, List.append_assoc, List.cons_append, List.nil_append] using ih (cache ++ [valuation j])

/- Proof-level interpretation of an initial sparse input index. No default
is used by the independent graph evaluator. -/
private theorem input_lookup {M : Type*} (valuation : ℕ → M) (formula : CNF) (ref : ℕ)
    (h : ref < (inputs formula).length) :
    ((inputNames formula).map valuation)[ref]? = some (inputValue valuation formula ref) := by
  have h' : ref < ((inputNames formula).map valuation).length := by
    simpa only [inputs, List.length_map] using h
  simp only [List.getElem?_eq_getElem h', inputValue, List.getD_eq_getElem _ _ h']

@[simp] theorem inputValue_literalRef {M : Type*} (valuation : ℕ → M) (formula : CNF)
    (i : ℕ) (hi : i ∈ ResetUnion.support formula) (sign : Bool) :
    inputValue valuation formula (literalRef formula (i, sign)) = valuation (ResetUnion.literalName (i, sign)) := by
  have h : literalRef formula (i, sign) < (inputNames formula).length := by
    simpa only [inputs, List.length_map] using literalRef_lt formula i hi sign
  unfold inputValue
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using h), List.getElem_map]
  exact congrArg valuation (List.getElem_idxOf h)

/- The three independent value expressions appearing in the report. -/
theorem eval_equation {M : Type*} [(Equational.language Reset.Symbol).Structure M]
    (valuation : ℕ → M) (formula : CNF) :
    (equation formula).eval valuation =
      some (Reset.operation M (leftValue valuation formula) (rightValue valuation formula), rightValue valuation formula) := by
  let cache := (inputNames formula).map valuation
  have hlength : cache.length = (inputs formula).length := by simp [cache, inputs]
  have hrun : runFrom valuation (inputs formula) [] = some cache := by
    simpa only [inputs, List.nil_append] using runFrom_inputs valuation (inputNames formula) []
  have hroot : cache[0]? = some (valuation 0) := rfl
  have hmarker : cache[1]? = some (valuation 1) := rfl
  obtain ⟨ws, hwcount, hwrun, hwout⟩ := eval_buildRightComb valuation (railRefs formula) 0
    (inputs formula) cache (inputValue valuation formula) (valuation 0) hlength hrun hroot
      (fun ref hr => input_lookup valuation formula ref (refs_lt formula ref hr))
  have hwlen : (cache ++ ws).length = (baselineBuild formula).gates.length := by
    rw [List.length_append, hlength, hwcount, baselineBuild, length_buildRightComb]
  obtain ⟨rs, hrcount, hrrun, hrout⟩ := eval_buildConsistency valuation (pairs formula) 1
    (baselineBuild formula).output (baselineBuild formula).gates (cache ++ ws) (inputValue valuation formula)
    (valuation 1) (baselineValue valuation formula) hwlen hwrun (lookup_append _ _ _ _ hmarker) hwout (by
      intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
      exact ⟨lookup_append _ _ _ _ (input_lookup valuation formula _ (literalRef_lt formula i hi true)),
        lookup_append _ _ _ _ (input_lookup valuation formula _ (literalRef_lt formula i hi false))⟩)
  have hrlen : ((cache ++ ws) ++ rs).length = (rightBuild formula).gates.length := by
    rw [List.length_append, hwlen, hrcount, rightBuild, length_buildConsistency]
  obtain ⟨as, hacount, harun, haout⟩ := eval_buildCNF valuation (clauseRefs formula) 1 0
    (rightBuild formula).gates ((cache ++ ws) ++ rs) (inputValue valuation formula)
    (valuation 1) (valuation 0) hrlen hrrun (lookup_append _ _ _ _ (lookup_append _ _ _ _ hmarker))
    (lookup_append _ _ _ _ (lookup_append _ _ _ _ hroot)) (by
      intro clause hc ref href
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hc
      obtain ⟨literal, hl, rfl⟩ := List.mem_map.mp href
      exact lookup_append _ _ _ _ (lookup_append _ _ _ _ (input_lookup valuation formula _
        (literalRef_lt formula literal.1 (ResetUnion.literal_mem_support formula C hC literal hl) literal.2))))
  have halen : (((cache ++ ws) ++ rs) ++ as).length = (leftBuild formula).gates.length := by
    rw [List.length_append, hrlen, hacount, leftBuild, length_buildCNF]
  have hrout' := lookup_append _ as _ _ hrout
  have hfinal := eval_reset_of_getElem? valuation (((cache ++ ws) ++ rs) ++ as)
    (leftBuild formula).output (rightBuild formula).output
    (leftValue valuation formula) (rightValue valuation formula) haout hrout'
  have hemit := runFrom_emit valuation (leftBuild formula).gates
    (Gate.reset (leftBuild formula).output (rightBuild formula).output)
    (((cache ++ ws) ++ rs) ++ as)
    (Reset.operation M (leftValue valuation formula) (rightValue valuation formula)) harun hfinal
  unfold Equation.eval
  rw [show (equation formula).gates = (emit (leftBuild formula).gates
    (Gate.reset (leftBuild formula).output (rightBuild formula).output)).gates from rfl, hemit]
  change (do
    let left ← (((((cache ++ ws) ++ rs) ++ as) ++ [Reset.operation M (leftValue valuation formula) (rightValue valuation formula)])[(leftBuild formula).gates.length]?)
    let right ← (((((cache ++ ws) ++ rs) ++ as) ++ [Reset.operation M (leftValue valuation formula) (rightValue valuation formula)])[(rightBuild formula).output]?)
    pure (left, right)) = _
  have hleft : (((((cache ++ ws) ++ rs) ++ as) ++
      [Reset.operation M (leftValue valuation formula) (rightValue valuation formula)])[(leftBuild formula).gates.length]?) =
      some (Reset.operation M (leftValue valuation formula) (rightValue valuation formula)) := by
    rw [← halen, List.getElem?_append_right (by omega), Nat.sub_self]
    rfl
  have hright : (((((cache ++ ws) ++ rs) ++ as) ++
      [Reset.operation M (leftValue valuation formula) (rightValue valuation formula)])[(rightBuild formula).output]?) =
      some (rightValue valuation formula) := lookup_append _ _ _ _ hrout'
  rw [hleft, hright]
  rfl


/- Exact reset-gate count of the original DAG, without unfolding shared
continuations into trees. -/
theorem equation_reset_gate_count (formula : CNF) :
    operationCount (equation formula).gates =
      5 * (ResetUnion.support formula).length + 2 * formula.flatten.length + 1 := by
  have hinput : operationCount (inputs formula) = 0 := by
    have h (names : List ℕ) : operationCount (names.map (Gate.input (σ := Reset.Symbol))) = 0 := by
      induction names with
      | nil => rfl
      | cons j names ih => simp_all [operationCount]
    exact h _
  change operationCount (emit (leftBuild formula).gates _).gates = _
  rw [operationCount_emit_reset, leftBuild, operationCount_buildCNF, rightBuild, operationCount_buildConsistency,
    baselineBuild, operationCount_buildRightComb, hinput, length_pairs, length_railRefs, length_clauseRefs_flatten]
  omega

end KFOL.Circuit.ResetCNF
