module

public import KFOL.Reductions.Circuits.Basic

/-! Native topological gate builders. Every result returns a cache reference,
so a previous circuit output can be reused without copying its graph. -/

@[expose] public section

namespace KFOL.Circuit

universe u v w

@[simp] theorem length_emit {σ : ℕ → Type u} {Var : Type v} (gates : List (Gate σ Var)) (gate : Gate σ Var) :
    (emit gates gate).gates.length = gates.length + 1 := by simp [emit]

@[simp] theorem output_emit {σ : ℕ → Type u} {Var : Type v} (gates : List (Gate σ Var)) (gate : Gate σ Var) :
    (emit gates gate).output = gates.length := rfl

@[simp] theorem validAt_reset {Var : Type v} (position left right : ℕ) :
    (Gate.reset left right : Gate Reset.Symbol Var).ValidAt position ↔ left < position ∧ right < position := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨hl, hr⟩ i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact hl
    · exact hr

theorem validFrom_emit {σ : ℕ → Type u} {Var : Type v} (gates : List (Gate σ Var)) (gate : Gate σ Var)
    (hgates : ValidFrom 0 gates) (hgate : gate.ValidAt gates.length) : ValidFrom 0 (emit gates gate).gates := by
  rw [emit, validFrom_append]
  simp only [Nat.zero_add]
  exact ⟨hgates, hgate, trivial⟩

theorem runFrom_emit {σ : ℕ → Type u} {Var : Type v} {M : Type w}
    [(Equational.language σ).Structure M] (valuation : Var → M) (gates : List (Gate σ Var))
    (gate : Gate σ Var) (cache : List M) (value : M)
    (hrun : runFrom valuation gates [] = some cache) (heval : gate.eval valuation cache = some value) :
    runFrom valuation (emit gates gate).gates [] = some (cache ++ [value]) := by
  rw [emit, runFrom_append, hrun]
  change runFrom valuation [gate] cache = some (cache ++ [value])
  rw [runFrom, heval]
  rfl

@[simp] theorem length_buildRightComb {Var : Type v} (refs : List ℕ) (base : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    (buildRightComb refs base gates).gates.length = gates.length + refs.length := by
  induction refs with
  | nil => simp [buildRightComb]
  | cons head refs ih =>
    rw [buildRightComb, length_emit, ih, List.length_cons]
    omega

/- Reference validity is proved independently of all model values. -/
theorem valid_buildRightComb {Var : Type v} (refs : List ℕ) (base : ℕ)
    (gates : List (Gate Reset.Symbol Var)) (hgates : ValidFrom 0 gates) (hbase : base < gates.length)
    (hrefs : ∀ ref ∈ refs, ref < gates.length) :
    ValidFrom 0 (buildRightComb refs base gates).gates ∧
      (buildRightComb refs base gates).output < (buildRightComb refs base gates).gates.length := by
  induction refs with
  | nil => exact ⟨hgates, hbase⟩
  | cons head refs ih =>
    have hhead := hrefs head (List.mem_cons_self ..)
    obtain ⟨htail, hout⟩ := ih (fun ref hr => hrefs ref (List.mem_cons_of_mem _ hr))
    change ValidFrom 0 (emit (buildRightComb refs base gates).gates
      (Gate.reset head (buildRightComb refs base gates).output)).gates ∧ _
    constructor
    · apply validFrom_emit _ _ htail
      apply (validAt_reset _ _ _).mpr
      refine ⟨?_, hout⟩
      rw [length_buildRightComb]
      omega
    · simp only [buildRightComb, output_emit, length_emit]
      omega

end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- Reset gate semantics uses safe optional cache reads; two successful
reads imply its independent strict-prefix check. -/
theorem eval_reset_of_getElem? {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] (valuation : Var → M)
    (cache : List M) (left right : ℕ) (leftValue rightValue : M)
    (hl : cache[left]? = some leftValue) (hr : cache[right]? = some rightValue) :
    (Gate.reset left right : Gate Reset.Symbol Var).eval valuation cache =
      some (Reset.operation M leftValue rightValue) := by
  obtain ⟨hleft, hleftValue⟩ := List.getElem?_eq_some_iff.mp hl
  obtain ⟨hright, hrightValue⟩ := List.getElem?_eq_some_iff.mp hr
  have hrefs : ∀ i : Fin 2, (if i = 0 then left else right) < cache.length :=
    (validAt_reset (Var := Var) cache.length left right).mpr ⟨hleft, hright⟩
  have hmap (args : Fin 2 → M) :
      FirstOrder.Language.Structure.funMap (L := Equational.language Reset.Symbol) Reset.Symbol.reset args =
        Reset.operation M (args 0) (args 1) := by
    unfold Reset.operation
    congr 1
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> rfl
  simp only [Gate.reset, Gate.eval, dite_eq_left hrefs]
  rw [hmap]
  change some (Reset.operation M (cache[left]'hleft) (cache[right]'hright)) = _
  rw [hleftValue, hrightValue]

/- Complete semantic receipt for a shared right-comb build. Original cache
entries are retained as an exact prefix; one new cache value is added per
new original gate. The theorem holds in every reset-signature algebra. -/
theorem eval_buildRightComb {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] (valuation : Var → M)
    (refs : List ℕ) (base : ℕ) (gates : List (Gate Reset.Symbol Var))
    (cache : List M) (values : ℕ → M) (baseValue : M)
    (hlength : cache.length = gates.length) (hrun : runFrom valuation gates [] = some cache)
    (hbase : cache[base]? = some baseValue)
    (hrefs : ∀ ref ∈ refs, cache[ref]? = some (values ref)) :
    ∃ suffix : List M, suffix.length = refs.length ∧
      runFrom valuation (buildRightComb refs base gates).gates [] = some (cache ++ suffix) ∧
      (cache ++ suffix)[(buildRightComb refs base gates).output]? =
        some ((refs.map values).foldr (Reset.operation M) baseValue) := by
  induction refs with
  | nil => exact ⟨[], rfl, by simpa only [buildRightComb, List.append_nil] using hrun,
      by simpa only [buildRightComb, List.append_nil, List.map_nil, List.foldr_nil] using hbase⟩
  | cons head refs ih =>
    obtain ⟨suffix, hcount, htailRun, htailOut⟩ := ih
      (fun ref hr => hrefs ref (List.mem_cons_of_mem _ hr))
    have hhead := hrefs head (List.mem_cons_self ..)
    have hheadBound := (List.getElem?_eq_some_iff.mp hhead).1
    have hhead' : (cache ++ suffix)[head]? = some (values head) := by
      rw [List.getElem?_append_left hheadBound]
      exact hhead
    have htailLength : (cache ++ suffix).length = (buildRightComb refs base gates).gates.length := by
      rw [List.length_append, hlength, hcount, length_buildRightComb]
    let value := Reset.operation M (values head) ((refs.map values).foldr (Reset.operation M) baseValue)
    have heval := eval_reset_of_getElem? valuation (cache ++ suffix) head
      (buildRightComb refs base gates).output (values head)
      ((refs.map values).foldr (Reset.operation M) baseValue) hhead' htailOut
    have hemit := runFrom_emit valuation (buildRightComb refs base gates).gates
      (Gate.reset head (buildRightComb refs base gates).output) (cache ++ suffix) value htailRun heval
    refine ⟨suffix ++ [value], ?_, ?_, ?_⟩
    · simp only [List.length_append, hcount, List.length_cons, List.length_nil]
    · simpa only [buildRightComb, List.append_assoc] using hemit
    · change (cache ++ (suffix ++ [value]))[(emit (buildRightComb refs base gates).gates
        (Gate.reset head (buildRightComb refs base gates).output)).output]? = some value
      rw [← List.append_assoc, output_emit, ← htailLength,
        List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl

end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- One clause stage. Every retained-literal gate points to the same previous
CNF output index, rather than copying that output's subgraph. -/
@[simp] theorem length_buildClause {Var : Type v} (refs : List ℕ) (previous root : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    (buildClause refs previous root gates).gates.length = gates.length + 2 * refs.length := by
  induction refs generalizing gates with
  | nil => simp [buildClause]
  | cons head refs ih =>
    rw [buildClause, length_emit, ih, length_emit, List.length_cons]
    omega

theorem valid_buildClause {Var : Type v} (refs : List ℕ) (previous root : ℕ)
    (gates : List (Gate Reset.Symbol Var)) (hgates : ValidFrom 0 gates)
    (hprevious : previous < gates.length) (hroot : root < gates.length)
    (hrefs : ∀ ref ∈ refs, ref < gates.length) :
    ValidFrom 0 (buildClause refs previous root gates).gates ∧
      (buildClause refs previous root gates).output < (buildClause refs previous root gates).gates.length := by
  induction refs generalizing gates with
  | nil => exact ⟨hgates, hroot⟩
  | cons head refs ih =>
    have hhead := hrefs head (List.mem_cons_self ..)
    let retained := emit gates (Gate.reset previous head)
    have hretained : ValidFrom 0 retained.gates := validFrom_emit _ _ hgates
      ((validAt_reset _ _ _).mpr ⟨hprevious, hhead⟩)
    have hlength : retained.gates.length = gates.length + 1 := length_emit _ _
    obtain ⟨htail, hout⟩ := ih retained.gates hretained (by omega) (by omega)
      (fun ref hr => by have h := hrefs ref (List.mem_cons_of_mem _ hr); omega)
    constructor
    · apply validFrom_emit _ _ htail
      apply (validAt_reset _ _ _).mpr
      refine ⟨?_, hout⟩
      change gates.length < (buildClause refs previous root retained.gates).gates.length
      rw [length_buildClause, hlength]
      omega
    · simp only [buildClause, output_emit, length_emit]
      omega

private theorem lookup_append_of_some {M : Type w} (cache suffix : List M) (i : ℕ) (value : M)
    (hi : cache[i]? = some value) : (cache ++ suffix)[i]? = some value := by
  obtain ⟨hbound, _⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.getElem?_append_left hbound]
  exact hi

/- The exact semantic clause recurrence for shared circuits. The previous
CNF value occurs as a reference at every literal gate, while the cache prefix
and every original graph node are preserved. -/
theorem eval_buildClause {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] (valuation : Var → M)
    (refs : List ℕ) (previous root : ℕ) (gates : List (Gate Reset.Symbol Var))
    (cache : List M) (values : ℕ → M) (previousValue rootValue : M)
    (hlength : cache.length = gates.length) (hrun : runFrom valuation gates [] = some cache)
    (hprevious : cache[previous]? = some previousValue) (hroot : cache[root]? = some rootValue)
    (hrefs : ∀ ref ∈ refs, cache[ref]? = some (values ref)) :
    ∃ suffix : List M, suffix.length = 2 * refs.length ∧
      runFrom valuation (buildClause refs previous root gates).gates [] = some (cache ++ suffix) ∧
      (cache ++ suffix)[(buildClause refs previous root gates).output]? =
        some (((refs.map values).map (Reset.operation M previousValue)).foldr (Reset.operation M) rootValue) := by
  induction refs generalizing gates cache with
  | nil => exact ⟨[], rfl, by simpa only [buildClause, List.append_nil] using hrun,
      by simpa only [buildClause, List.append_nil, List.map_nil, List.foldr_nil] using hroot⟩
  | cons head refs ih =>
    let retained := emit gates (Gate.reset previous head)
    let retainedValue := Reset.operation M previousValue (values head)
    have hhead := hrefs head (List.mem_cons_self ..)
    have hretainedEval := eval_reset_of_getElem? valuation cache previous head previousValue (values head) hprevious hhead
    have hretainedRun : runFrom valuation retained.gates [] = some (cache ++ [retainedValue]) :=
      runFrom_emit valuation gates _ cache retainedValue hrun hretainedEval
    have hretainedLength : (cache ++ [retainedValue]).length = retained.gates.length := by
      simp only [List.length_append, List.length_singleton, hlength, retained, length_emit]
    obtain ⟨suffix, hcount, htailRun, htailOut⟩ := ih retained.gates (cache ++ [retainedValue])
      hretainedLength hretainedRun (lookup_append_of_some _ _ _ _ hprevious)
      (lookup_append_of_some _ _ _ _ hroot)
      (fun ref hr => lookup_append_of_some _ _ _ _ (hrefs ref (List.mem_cons_of_mem _ hr)))
    have hretainedOut : (cache ++ [retainedValue])[retained.output]? = some retainedValue := by
      change (cache ++ [retainedValue])[gates.length]? = some retainedValue
      rw [← hlength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have hhead' : ((cache ++ [retainedValue]) ++ suffix)[retained.output]? = some retainedValue :=
      lookup_append_of_some _ _ _ _ hretainedOut
    have htailLength : ((cache ++ [retainedValue]) ++ suffix).length =
        (buildClause refs previous root retained.gates).gates.length := by
      rw [List.length_append, hretainedLength, hcount, length_buildClause]
    let value := Reset.operation M retainedValue
      (((refs.map values).map (Reset.operation M previousValue)).foldr (Reset.operation M) rootValue)
    have heval := eval_reset_of_getElem? valuation ((cache ++ [retainedValue]) ++ suffix)
      retained.output (buildClause refs previous root retained.gates).output retainedValue
      (((refs.map values).map (Reset.operation M previousValue)).foldr (Reset.operation M) rootValue) hhead' htailOut
    have hemit := runFrom_emit valuation (buildClause refs previous root retained.gates).gates
      (Gate.reset retained.output (buildClause refs previous root retained.gates).output)
      ((cache ++ [retainedValue]) ++ suffix) value htailRun heval
    refine ⟨retainedValue :: (suffix ++ [value]), ?_, ?_, ?_⟩
    · simp only [List.length_cons, List.length_append, List.length_nil, hcount]
      omega
    · simpa only [buildClause, retained, List.append_assoc, List.cons_append, List.nil_append] using hemit
    · change (cache ++ retainedValue :: (suffix ++ [value]))[(emit
        (buildClause refs previous root retained.gates).gates
        (Gate.reset retained.output (buildClause refs previous root retained.gates).output)).output]? = some value
      have he : cache ++ retainedValue :: (suffix ++ [value]) =
          (((cache ++ [retainedValue]) ++ suffix) ++ [value]) := by
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [he, output_emit, ← htailLength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl

end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- Successive clauses retain exactly one reference to each previous output.
An empty clause returns the original root reference without emitting gates. -/
@[simp] theorem length_buildCNF {Var : Type v} (clauses : List (List ℕ)) (previous root : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    (buildCNF clauses previous root gates).gates.length = gates.length + 2 * clauses.flatten.length := by
  induction clauses generalizing previous gates with
  | nil => simp [buildCNF]
  | cons clause clauses ih =>
    rw [buildCNF, ih, length_buildClause]
    simp only [List.flatten_cons, List.length_append]
    omega

theorem valid_buildCNF {Var : Type v} (clauses : List (List ℕ)) (previous root : ℕ)
    (gates : List (Gate Reset.Symbol Var)) (hgates : ValidFrom 0 gates)
    (hprevious : previous < gates.length) (hroot : root < gates.length)
    (hrefs : ∀ clause ∈ clauses, ∀ ref ∈ clause, ref < gates.length) :
    ValidFrom 0 (buildCNF clauses previous root gates).gates ∧
      (buildCNF clauses previous root gates).output < (buildCNF clauses previous root gates).gates.length := by
  induction clauses generalizing previous gates with
  | nil => exact ⟨hgates, hprevious⟩
  | cons clause clauses ih =>
    obtain ⟨hhead, hout⟩ := valid_buildClause clause previous root gates hgates hprevious hroot
      (hrefs clause (List.mem_cons_self ..))
    have hlength : gates.length ≤ (buildClause clause previous root gates).gates.length := by
      rw [length_buildClause]
      omega
    exact ih _ _ hhead hout (lt_of_lt_of_le hroot hlength)
      (fun c hc ref hr => lt_of_lt_of_le (hrefs c (List.mem_cons_of_mem _ hc) ref hr) hlength)

/- Exact cached semantics of the complete clause circuit, in an arbitrary
reset-signature algebra. This is a graph theorem, not an unconnected value
certificate: its conclusion evaluates the actual constructed gate list. -/
theorem eval_buildCNF {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] (valuation : Var → M)
    (clauses : List (List ℕ)) (previous root : ℕ) (gates : List (Gate Reset.Symbol Var))
    (cache : List M) (values : ℕ → M) (previousValue rootValue : M)
    (hlength : cache.length = gates.length) (hrun : runFrom valuation gates [] = some cache)
    (hprevious : cache[previous]? = some previousValue) (hroot : cache[root]? = some rootValue)
    (hrefs : ∀ clause ∈ clauses, ∀ ref ∈ clause, cache[ref]? = some (values ref)) :
    ∃ suffix : List M, suffix.length = 2 * clauses.flatten.length ∧
      runFrom valuation (buildCNF clauses previous root gates).gates [] = some (cache ++ suffix) ∧
      (cache ++ suffix)[(buildCNF clauses previous root gates).output]? =
        some (((clauses.map (fun clause => clause.map values))).foldl
          (fun prior clause => (clause.map (Reset.operation M prior)).foldr (Reset.operation M) rootValue) previousValue) := by
  induction clauses generalizing previous gates cache previousValue with
  | nil => exact ⟨[], rfl, by simpa only [buildCNF, List.append_nil] using hrun,
      by simpa only [buildCNF, List.append_nil, List.map_nil, List.foldl_nil] using hprevious⟩
  | cons clause clauses ih =>
    obtain ⟨headSuffix, hheadCount, hheadRun, hheadOut⟩ := eval_buildClause valuation clause previous root
      gates cache values previousValue rootValue hlength hrun hprevious hroot (hrefs clause (List.mem_cons_self ..))
    have hheadLength : (cache ++ headSuffix).length = (buildClause clause previous root gates).gates.length := by
      rw [List.length_append, hlength, hheadCount, length_buildClause]
    obtain ⟨tailSuffix, htailCount, htailRun, htailOut⟩ := ih
      (buildClause clause previous root gates).output (buildClause clause previous root gates).gates
      (cache ++ headSuffix) _ hheadLength hheadRun hheadOut (lookup_append_of_some _ _ _ _ hroot)
      (fun c hc ref hr => lookup_append_of_some _ _ _ _ (hrefs c (List.mem_cons_of_mem _ hc) ref hr))
    refine ⟨headSuffix ++ tailSuffix, ?_, ?_, ?_⟩
    · simp only [List.length_append, hheadCount, htailCount, List.flatten_cons]
      omega
    · simpa only [buildCNF, List.append_assoc] using htailRun
    · simpa only [buildCNF, List.append_assoc, List.map_cons, List.foldl_cons] using htailOut

end KFOL.Circuit

namespace KFOL.Circuit

universe v w

/- Right comb of the inconsistent-rail branches `(c reset p) reset n`.
The cached marker and both literal inputs are reused by index. -/
@[simp] theorem length_buildConsistency {Var : Type v} (pairs : List (ℕ × ℕ)) (marker base : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    (buildConsistency pairs marker base gates).gates.length = gates.length + 3 * pairs.length := by
  induction pairs generalizing gates with
  | nil => simp [buildConsistency]
  | cons pair pairs ih =>
    rw [buildConsistency, length_emit, ih, length_emit, length_emit, List.length_cons]
    omega

theorem valid_buildConsistency {Var : Type v} (pairs : List (ℕ × ℕ)) (marker base : ℕ)
    (gates : List (Gate Reset.Symbol Var)) (hgates : ValidFrom 0 gates)
    (hmarker : marker < gates.length) (hbase : base < gates.length)
    (hpairs : ∀ pair ∈ pairs, pair.1 < gates.length ∧ pair.2 < gates.length) :
    ValidFrom 0 (buildConsistency pairs marker base gates).gates ∧
      (buildConsistency pairs marker base gates).output < (buildConsistency pairs marker base gates).gates.length := by
  induction pairs generalizing gates with
  | nil => exact ⟨hgates, hbase⟩
  | cons pair pairs ih =>
    have hpair := hpairs pair (List.mem_cons_self ..)
    let positive := emit gates (Gate.reset marker pair.1)
    let negative := emit positive.gates (Gate.reset positive.output pair.2)
    have hpvalid : ValidFrom 0 positive.gates := validFrom_emit _ _ hgates
      ((validAt_reset _ _ _).mpr ⟨hmarker, hpair.1⟩)
    have hplen : positive.gates.length = gates.length + 1 := length_emit _ _
    have hpout : positive.output = gates.length := rfl
    have hnvalid : ValidFrom 0 negative.gates := validFrom_emit _ _ hpvalid
      ((validAt_reset _ _ _).mpr ⟨by omega, by omega⟩)
    have hnlen : negative.gates.length = gates.length + 2 := by rw [length_emit, hplen]
    obtain ⟨htail, hout⟩ := ih negative.gates hnvalid (by omega) (by omega)
      (fun p hp => by have h := hpairs p (List.mem_cons_of_mem _ hp); constructor <;> omega)
    constructor
    · apply validFrom_emit _ _ htail
      apply (validAt_reset _ _ _).mpr
      refine ⟨?_, hout⟩
      change positive.gates.length < (buildConsistency pairs marker base negative.gates).gates.length
      rw [length_buildConsistency, hplen, hnlen]
      omega
    · simp only [buildConsistency, output_emit, length_emit]
      omega

/- Exact semantic and cache-prefix receipt for all consistency branches. -/
theorem eval_buildConsistency {Var : Type v} {M : Type w}
    [(Equational.language Reset.Symbol).Structure M] (valuation : Var → M)
    (pairs : List (ℕ × ℕ)) (marker base : ℕ) (gates : List (Gate Reset.Symbol Var))
    (cache : List M) (values : ℕ → M) (markerValue baseValue : M)
    (hlength : cache.length = gates.length) (hrun : runFrom valuation gates [] = some cache)
    (hmarker : cache[marker]? = some markerValue) (hbase : cache[base]? = some baseValue)
    (hpairs : ∀ pair ∈ pairs, cache[pair.1]? = some (values pair.1) ∧ cache[pair.2]? = some (values pair.2)) :
    ∃ suffix : List M, suffix.length = 3 * pairs.length ∧
      runFrom valuation (buildConsistency pairs marker base gates).gates [] = some (cache ++ suffix) ∧
      (cache ++ suffix)[(buildConsistency pairs marker base gates).output]? =
        some ((pairs.map (fun p => Reset.operation M (Reset.operation M markerValue (values p.1)) (values p.2))).foldr
          (Reset.operation M) baseValue) := by
  induction pairs generalizing gates cache with
  | nil => exact ⟨[], rfl, by simpa only [buildConsistency, List.append_nil] using hrun,
      by simpa only [buildConsistency, List.append_nil, List.map_nil, List.foldr_nil] using hbase⟩
  | cons pair pairs ih =>
    let positive := emit gates (Gate.reset marker pair.1)
    let positiveValue := Reset.operation M markerValue (values pair.1)
    let negative := emit positive.gates (Gate.reset positive.output pair.2)
    let negativeValue := Reset.operation M positiveValue (values pair.2)
    have hpair := hpairs pair (List.mem_cons_self ..)
    have hpEval := eval_reset_of_getElem? valuation cache marker pair.1 markerValue (values pair.1) hmarker hpair.1
    have hpRun : runFrom valuation positive.gates [] = some (cache ++ [positiveValue]) :=
      runFrom_emit valuation gates _ cache positiveValue hrun hpEval
    have hpOut : (cache ++ [positiveValue])[positive.output]? = some positiveValue := by
      change (cache ++ [positiveValue])[gates.length]? = _
      rw [← hlength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    have hnEval := eval_reset_of_getElem? valuation (cache ++ [positiveValue]) positive.output pair.2
      positiveValue (values pair.2) hpOut (lookup_append_of_some _ _ _ _ hpair.2)
    have hnRun : runFrom valuation negative.gates [] = some (cache ++ [positiveValue, negativeValue]) := by
      have he := runFrom_emit valuation positive.gates _ (cache ++ [positiveValue]) negativeValue hpRun hnEval
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using he
    have hnLength : (cache ++ [positiveValue, negativeValue]).length = negative.gates.length := by
      simp only [List.length_append, List.length_cons, List.length_nil, negative, length_emit,
        positive, length_emit, hlength]
    obtain ⟨suffix, hcount, htailRun, htailOut⟩ := ih negative.gates (cache ++ [positiveValue, negativeValue])
      hnLength hnRun (lookup_append_of_some _ _ _ _ hmarker) (lookup_append_of_some _ _ _ _ hbase)
      (fun p hp => by
        have h := hpairs p (List.mem_cons_of_mem _ hp)
        exact ⟨lookup_append_of_some _ _ _ _ h.1, lookup_append_of_some _ _ _ _ h.2⟩)
    have hnOut : (cache ++ [positiveValue, negativeValue])[negative.output]? = some negativeValue := by
      change (cache ++ [positiveValue, negativeValue])[positive.gates.length]? = _
      rw [length_emit, ← hlength, List.getElem?_append_right (by omega)]
      have hi : cache.length + 1 - cache.length = 1 := by omega
      rw [hi]
      rfl
    have hnOut' := lookup_append_of_some _ suffix _ _ hnOut
    have htailLength : ((cache ++ [positiveValue, negativeValue]) ++ suffix).length =
        (buildConsistency pairs marker base negative.gates).gates.length := by
      rw [List.length_append, hnLength, hcount, length_buildConsistency]
    let value := Reset.operation M negativeValue
      ((pairs.map (fun p => Reset.operation M (Reset.operation M markerValue (values p.1)) (values p.2))).foldr
        (Reset.operation M) baseValue)
    have heval := eval_reset_of_getElem? valuation ((cache ++ [positiveValue, negativeValue]) ++ suffix)
      negative.output (buildConsistency pairs marker base negative.gates).output negativeValue
      ((pairs.map (fun p => Reset.operation M (Reset.operation M markerValue (values p.1)) (values p.2))).foldr
        (Reset.operation M) baseValue) hnOut' htailOut
    have hemit := runFrom_emit valuation (buildConsistency pairs marker base negative.gates).gates
      (Gate.reset negative.output (buildConsistency pairs marker base negative.gates).output)
      ((cache ++ [positiveValue, negativeValue]) ++ suffix) value htailRun heval
    refine ⟨[positiveValue, negativeValue] ++ (suffix ++ [value]), ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, List.length_nil, hcount]
      omega
    · simpa only [buildConsistency, negative, positive, List.append_assoc] using hemit
    · change (cache ++ ([positiveValue, negativeValue] ++ (suffix ++ [value])))[(emit
        (buildConsistency pairs marker base negative.gates).gates
        (Gate.reset negative.output (buildConsistency pairs marker base negative.gates).output)).output]? = some value
      have he : cache ++ ([positiveValue, negativeValue] ++ (suffix ++ [value])) =
          (((cache ++ [positiveValue, negativeValue]) ++ suffix) ++ [value]) := by simp only [List.append_assoc]
      rw [he, output_emit, ← htailLength, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl

end KFOL.Circuit

namespace KFOL.Circuit

universe v

@[simp] theorem operationCount_emit_reset {Var : Type v} (gates : List (Gate Reset.Symbol Var)) (l r : ℕ) :
    operationCount (emit gates (Gate.reset l r)).gates = operationCount gates + 1 := by
  simp [operationCount, emit, Gate.reset]

@[simp] theorem operationCount_buildRightComb {Var : Type v} (refs : List ℕ) (base : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    operationCount (buildRightComb refs base gates).gates = operationCount gates + refs.length := by
  induction refs with
  | nil => simp [buildRightComb]
  | cons head refs ih => simp only [buildRightComb, operationCount_emit_reset, ih, List.length_cons]; omega

@[simp] theorem operationCount_buildClause {Var : Type v} (refs : List ℕ) (previous root : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    operationCount (buildClause refs previous root gates).gates = operationCount gates + 2 * refs.length := by
  induction refs generalizing gates with
  | nil => simp [buildClause]
  | cons head refs ih => simp only [buildClause, operationCount_emit_reset, ih, List.length_cons]; omega

@[simp] theorem operationCount_buildCNF {Var : Type v} (clauses : List (List ℕ)) (previous root : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    operationCount (buildCNF clauses previous root gates).gates = operationCount gates + 2 * clauses.flatten.length := by
  induction clauses generalizing previous gates with
  | nil => simp [buildCNF]
  | cons clause clauses ih =>
    simp only [buildCNF, ih, operationCount_buildClause, List.flatten_cons, List.length_append]
    omega

@[simp] theorem operationCount_buildConsistency {Var : Type v} (pairs : List (ℕ × ℕ)) (marker base : ℕ)
    (gates : List (Gate Reset.Symbol Var)) :
    operationCount (buildConsistency pairs marker base gates).gates = operationCount gates + 3 * pairs.length := by
  induction pairs generalizing gates with
  | nil => simp [buildConsistency]
  | cons pair pairs ih => simp only [buildConsistency, operationCount_emit_reset, ih, List.length_cons]; omega

end KFOL.Circuit
