module
public import KFOL.Complexity.CircuitGeneratorComb
/-! Forward blocks and reverse comb blocks reproduce the original clause and consistency builders, including every repeated cache edge. -/

@[expose] public section
namespace KFOL.Complexity.CircuitGenerator
open CircuitMachine

/-- Positions of a fixed block, independent of the sizes of source names. -/
def slots (count offset stride : ℕ) : List ℕ :=
  (List.range count).map (fun i => offset + stride * i)

@[simp] theorem slots_zero (offset stride : ℕ) : slots 0 offset stride = [] := rfl
@[simp] theorem length_slots (count offset stride : ℕ) : (slots count offset stride).length = count := by
  simp [slots]

theorem slots_succ (count offset stride : ℕ) :
    slots (count + 1) offset stride = offset :: slots count (offset + stride) stride := by
  simp only [slots, List.range_succ_eq_map, List.map_cons, Nat.mul_zero, Nat.add_zero, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  dsimp only [Function.comp_def]
  simp only [Nat.mul_succ]
  omega

/-- One retained reset per literal; each reuses the same predecessor reference. -/
def retainedNodes (refs : List ℕ) (previous : ℕ) : Gates :=
  refs.map (resetGate previous)

/-- The two forward nodes for each consistency pair. -/
def branchNodes (pairs : List (ℕ × ℕ)) (marker offset : ℕ) : Gates :=
  pairs.zipIdx.flatMap fun p =>
    [resetGate marker p.1.1, resetGate (offset + 2 * p.2) p.1.2]

@[simp] theorem branchNodes_nil (marker offset : ℕ) : branchNodes [] marker offset = [] := rfl

theorem branchNodes_cons (pair : ℕ × ℕ) (pairs : List (ℕ × ℕ)) (marker offset : ℕ) :
    branchNodes (pair :: pairs) marker offset =
      [resetGate marker pair.1, resetGate offset pair.2] ++ branchNodes pairs marker (offset + 2) := by
  simp only [branchNodes, List.zipIdx_cons', List.flatMap_cons, List.flatMap_map,
    Nat.mul_zero, Nat.add_zero]
  congr 1
  congr 1
  funext p
  dsimp only [Prod.map, Function.comp_def, id_eq]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm]

/-- Exact new gates for an original clause, with the forward block followed by
its reverse comb block. -/
def clauseNodes (refs : List ℕ) (previous root offset : ℕ) : Gates :=
  retainedNodes refs previous ++
    combNodes (slots refs.length offset 1) root (offset + refs.length)

/-- Exact new gates for consistency, with the two-node forward blocks followed
by the reverse comb block. -/
def consistencyNodes (pairs : List (ℕ × ℕ)) (marker base offset : ℕ) : Gates :=
  branchNodes pairs marker offset ++
    combNodes (slots pairs.length (offset + 1) 2) base (offset + 2 * pairs.length)

@[simp] theorem length_clauseNodes (refs : List ℕ) (previous root offset : ℕ) :
    (clauseNodes refs previous root offset).length = 2 * refs.length := by
  simp [clauseNodes, retainedNodes]; omega

@[simp] theorem length_branchNodes (pairs : List (ℕ × ℕ)) (marker offset : ℕ) :
    (branchNodes pairs marker offset).length = 2 * pairs.length := by
  induction pairs generalizing offset with
  | nil => simp
  | cons pair pairs ih => rw [branchNodes_cons]; simp only [List.length_append, List.length_cons,
      List.length_nil, ih]; omega

@[simp] theorem length_consistencyNodes (pairs : List (ℕ × ℕ)) (marker base offset : ℕ) :
    (consistencyNodes pairs marker base offset).length = 3 * pairs.length := by
  simp [consistencyNodes]; omega

/-- All source cache edges, including the repeated predecessor, are preserved. -/
theorem view_buildClause (refs : List ℕ) (previous root : ℕ)
    (gates : List (Circuit.Gate Reset.Symbol ℕ)) :
    (Circuit.buildClause refs previous root gates).gates.map viewGate =
      gates.map viewGate ++ clauseNodes refs previous root gates.length ∧
    (Circuit.buildClause refs previous root gates).output = lastRef root gates.length (2 * refs.length) := by
  induction refs generalizing gates with
  | nil => simp [Circuit.buildClause, clauseNodes, retainedNodes, lastRef]
  | cons head refs ih =>
    let retained := Circuit.emit gates (Circuit.Gate.reset previous head)
    have ht := ih retained.gates
    have hc : gates.length + (refs.length + 1) = retained.gates.length + refs.length := by
      simp only [retained, Circuit.length_emit]; omega
    have hs : slots (refs.length + 1) gates.length 1 =
        gates.length :: slots refs.length retained.gates.length 1 := by
      rw [slots_succ]
      simp only [retained, Circuit.length_emit]
    have ho : lastRef root (retained.gates.length + refs.length) refs.length =
        lastRef root retained.gates.length (2 * refs.length) := by
      dsimp only [lastRef]
      simp only [retained, Circuit.length_emit]
      split_ifs <;> omega
    constructor
    · change (Circuit.emit (Circuit.buildClause refs previous root retained.gates).gates
        (Circuit.Gate.reset retained.output (Circuit.buildClause refs previous root retained.gates).output)).gates.map viewGate = _
      simp only [Circuit.emit, List.map_append, List.map_cons, List.map_nil, view_reset, ht.1, ht.2]
      have hm : retained.gates.map viewGate = gates.map viewGate ++ [resetGate previous head] := by
        simp [retained, Circuit.emit]
      rw [hm]
      simp only [retained, Circuit.output_emit]
      change ((gates.map viewGate ++ [resetGate previous head]) ++
        clauseNodes refs previous root retained.gates.length) ++
        [resetGate gates.length (lastRef root retained.gates.length (2 * refs.length))] = _
      simp only [clauseNodes, List.length_cons, hs, combNodes_cons, length_slots, hc, ho,
        retainedNodes, List.map_cons, List.append_assoc, List.cons_append, List.nil_append]
    · change (Circuit.buildClause refs previous root retained.gates).gates.length = _
      rw [Circuit.length_buildClause]
      rw [show retained.gates.length = gates.length + 1 by simp [retained]]
      change gates.length + 1 + 2 * refs.length = lastRef root gates.length (2 * (refs.length + 1))
      rw [lastRef, ite_eq_right (by omega)]
      omega

theorem view_buildConsistency (pairs : List (ℕ × ℕ)) (marker base : ℕ)
    (gates : List (Circuit.Gate Reset.Symbol ℕ)) :
    (Circuit.buildConsistency pairs marker base gates).gates.map viewGate =
      gates.map viewGate ++ consistencyNodes pairs marker base gates.length ∧
    (Circuit.buildConsistency pairs marker base gates).output = lastRef base gates.length (3 * pairs.length) := by
  induction pairs generalizing gates with
  | nil => simp [Circuit.buildConsistency, consistencyNodes, lastRef]
  | cons pair pairs ih =>
    let positive := Circuit.emit gates (Circuit.Gate.reset marker pair.1)
    let negative := Circuit.emit positive.gates (Circuit.Gate.reset positive.output pair.2)
    have hn : negative.gates.length = gates.length + 2 := by simp [negative, positive, Nat.add_assoc]
    have ht := ih negative.gates
    have hc : gates.length + 2 * (pairs.length + 1) = negative.gates.length + 2 * pairs.length := by omega
    have hs : slots (pairs.length + 1) (gates.length + 1) 2 =
        (gates.length + 1) :: slots pairs.length (negative.gates.length + 1) 2 := by
      rw [slots_succ, hn]
    have ho : lastRef base (negative.gates.length + 2 * pairs.length) pairs.length =
        lastRef base negative.gates.length (3 * pairs.length) := by
      dsimp only [lastRef]
      split_ifs <;> omega
    rw [hn] at ho
    constructor
    · change (Circuit.emit (Circuit.buildConsistency pairs marker base negative.gates).gates
        (Circuit.Gate.reset negative.output (Circuit.buildConsistency pairs marker base negative.gates).output)).gates.map viewGate = _
      simp only [Circuit.emit, List.map_append, List.map_cons, List.map_nil, view_reset, ht.1, ht.2]
      have hm : negative.gates.map viewGate =
          (gates.map viewGate ++ [resetGate marker pair.1]) ++ [resetGate gates.length pair.2] := by
        simp [negative, positive, Circuit.emit]
      rw [hm]
      have hout : negative.output = gates.length + 1 := by simp [negative, positive]
      rw [hout]
      change (((gates.map viewGate ++ [resetGate marker pair.1]) ++
        [resetGate gates.length pair.2]) ++ consistencyNodes pairs marker base negative.gates.length) ++
        [resetGate (gates.length + 1) (lastRef base negative.gates.length (3 * pairs.length))] = _
      simp only [consistencyNodes, List.length_cons, hs, combNodes_cons, length_slots, hc, ho,
        branchNodes_cons, hn, List.append_assoc, List.cons_append, List.nil_append]
    · change (Circuit.buildConsistency pairs marker base negative.gates).gates.length = _
      rw [Circuit.length_buildConsistency, hn]
      change gates.length + 2 + 3 * pairs.length = lastRef base gates.length (3 * (pairs.length + 1))
      rw [lastRef, ite_eq_right (by omega)]
      omega
end KFOL.Complexity.CircuitGenerator
