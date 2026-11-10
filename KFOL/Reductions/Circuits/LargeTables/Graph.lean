module

public import KFOL.Reductions.Circuits.LargeTables

/-! The original shared graph for the exponentially large canonical table.
Exactly one cached previous output is used at both literal branches. -/

@[expose] public section
namespace KFOL.Circuit.LargeTables

def build : ℕ → BuildResult Reset.Symbol Variable
  | 0 => emit [.input markerName,.input rootName] (Gate.reset 0 1)
  | n+1 =>
      let previous := build n
      let positive := emit previous.gates (.input (rail n true))
      let negative := emit positive.gates (.input (rail n false))
      buildClause [positive.output,negative.output] previous.output 1 negative.gates

def graph (n : ℕ) : Equation Reset.Symbol Variable :=
  ⟨(build n).gates,(build n).output,(build n).output⟩

theorem length_build (n : ℕ) : (build n).gates.length = 6*n+3 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [build,length_buildClause,length_emit,List.length_cons,List.length_nil]
    rw [ih]
    omega

private theorem operationCount_emit_input (gates : List (Gate Reset.Symbol Variable)) (j : Variable) :
    operationCount (emit gates (.input j)).gates = operationCount gates := by
  simp [emit,operationCount]

theorem operationCount_build (n : ℕ) : operationCount (build n).gates = 4*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [build,operationCount_buildClause,operationCount_emit_input,List.length_cons,List.length_nil]
    rw [ih]
    omega

theorem valid_build (n : ℕ) : ValidFrom 0 (build n).gates ∧ (build n).output < (build n).gates.length := by
  induction n with
  | zero =>
    refine ⟨validFrom_emit _ _ ⟨trivial,trivial,trivial⟩ ((validAt_reset _ _ _).mpr ⟨by decide,by decide⟩),by decide⟩
  | succ n ih =>
    let previous := build n
    let positive := emit previous.gates (.input (rail n true))
    let negative := emit positive.gates (.input (rail n false))
    have hp : ValidFrom 0 positive.gates := validFrom_emit _ _ ih.1 trivial
    have hn : ValidFrom 0 negative.gates := validFrom_emit _ _ hp trivial
    have hl : negative.gates.length = previous.gates.length + 2 := by simp [negative,positive]
    have hpout : positive.output = previous.gates.length := rfl
    have hnout : negative.output = previous.gates.length+1 := by simp [negative,positive]
    have hlen : previous.gates.length = 6*n+3 := length_build n
    change ValidFrom 0 (buildClause [positive.output,negative.output] previous.output 1 negative.gates).gates ∧ _
    apply valid_buildClause _ _ _ _ hn
    · have h : previous.output < previous.gates.length := ih.2
      omega
    · omega
    · intro ref hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> omega

theorem graph_wellFormed (n : ℕ) : (graph n).WellFormed :=
  ⟨(valid_build n).1,(valid_build n).2,(valid_build n).2⟩

theorem graph_gate_count (n : ℕ) : (graph n).gates.length = 6*n+3 := length_build n

theorem graph_reset_gate_count (n : ℕ) : operationCount (graph n).gates = 4*n+1 := operationCount_build n

theorem graph_input_gate_count (n : ℕ) :
    (graph n).gates.countP (fun gate => match gate with | .input _ => true | .func _ _ => false) = 2*n+2 := by
  have count (gates : List (Gate Reset.Symbol Variable)) :
      gates.countP (fun gate => match gate with | .input _ => true | .func _ _ => false) +
        operationCount gates = gates.length := by
    induction gates with
    | nil => rfl
    | cons gate gates ih =>
      cases gate <;> simp [operationCount] at * <;> omega
  have h := count (graph n).gates
  rw [graph_reset_gate_count,graph_gate_count] at h
  omega

/-- Count actual reference edges, including repeated references as separate
edges. There is no hidden expansion of shared source gates. -/
theorem graph_edge_count (n : ℕ) :
    ((graph n).gates.map (fun gate => gate.references.length)).sum = 8*n+2 := by
  have count (gates : List (Gate Reset.Symbol Variable)) :
      (gates.map (fun gate => gate.references.length)).sum = 2*operationCount gates := by
    induction gates with
    | nil => rfl
    | cons gate gates ih =>
      cases gate with
      | input j => simpa [operationCount] using ih
      | func symbol refs =>
        cases symbol
        have hc : operationCount (Gate.func Reset.Symbol.reset refs :: gates) = operationCount gates+1 := by
          simp [operationCount]
        simp only [List.map_cons,Gate.length_references_func,List.sum_cons,hc,ih]
        omega
  rw [count,graph_reset_gate_count]
  omega

private theorem lookup_append {M : Type} (cache suffix : List M) (index : ℕ) (value : M)
    (h : cache[index]? = some value) : (cache ++ suffix)[index]? = some value := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

private theorem lookup_appended {M : Type} (cache : List M) (value : M) :
    (cache ++ [value])[cache.length]? = some value := by
  rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]
  rfl

/-- Exact graph/cache receipt in the term algebra, so the exponentially large
term is a proved unfolding of this particular linear graph. -/
theorem build_unfold (n : ℕ) :
    let _ := Equational.termStructure Reset.Symbol Variable
    ∃ cache : List (Reset.Term Variable),
      cache.length = (build n).gates.length ∧
      runFrom (FirstOrder.Language.Term.var : Variable → Reset.Term Variable) (build n).gates [] = some cache ∧
      cache[(build n).output]? = some (tree n) ∧ cache[1]? = some (.var rootName) := by
  let _ := Equational.termStructure Reset.Symbol Variable
  induction n with
  | zero =>
    let cache : List (Reset.Term Variable) := [.var markerName,.var rootName]
    have hr : runFrom (FirstOrder.Language.Term.var : Variable → Reset.Term Variable)
        ([.input markerName,.input rootName] : List (Gate Reset.Symbol Variable)) [] = some cache := rfl
    have he := eval_reset_of_getElem? FirstOrder.Language.Term.var cache 0 1
      (.var markerName) (.var rootName) rfl rfl
    have hout := runFrom_emit FirstOrder.Language.Term.var _ (Gate.reset 0 1) cache
      (Reset.operation (Reset.Term Variable) (.var markerName) (.var rootName)) hr he
    refine ⟨cache ++ [tree 0],rfl,?_,rfl,rfl⟩
    exact hout
  | succ n ih =>
    obtain ⟨cache,hlength,hrun,hprevious,hroot⟩ := ih
    let previous := build n
    change cache.length = previous.gates.length at hlength
    let positive := emit previous.gates (.input (rail n true))
    let negative := emit positive.gates (.input (rail n false))
    let p : Reset.Term Variable := .var (rail n true)
    let q : Reset.Term Variable := .var (rail n false)
    let cachedPrefix := (cache ++ [p]) ++ [q]
    have hp : runFrom (FirstOrder.Language.Term.var : Variable → Reset.Term Variable) positive.gates [] = some (cache ++ [p]) :=
      runFrom_emit _ _ _ _ _ hrun rfl
    have hn : runFrom (FirstOrder.Language.Term.var : Variable → Reset.Term Variable) negative.gates [] = some cachedPrefix :=
      runFrom_emit _ _ _ _ _ hp rfl
    have hcachedPrefixLength : cachedPrefix.length = negative.gates.length := by
      simp only [cachedPrefix,List.length_append,List.length_singleton,negative,positive,length_emit]
      omega
    have hlookupP : cachedPrefix[positive.output]? = some p := by
      apply lookup_append _ _ _ _
      change (cache ++ [p])[previous.gates.length]? = some p
      change cache.length = previous.gates.length at hlength
      rw [← hlength]
      exact lookup_appended cache p
    have hlookupQ : cachedPrefix[negative.output]? = some q := by
      change ((cache ++ [p]) ++ [q])[(emit previous.gates (.input (rail n true))).gates.length]? = some q
      have hl : (cache ++ [p]).length = (emit previous.gates (.input (rail n true))).gates.length := by
        simp only [List.length_append,List.length_singleton,length_emit]
        omega
      rw [← hl]
      exact lookup_appended _ q
    have hprevious' : cachedPrefix[previous.output]? = some (tree n) :=
      lookup_append _ _ _ _ (lookup_append _ _ _ _ hprevious)
    have hroot' : cachedPrefix[1]? = some (.var rootName) :=
      lookup_append _ _ _ _ (lookup_append _ _ _ _ hroot)
    let values : ℕ → Reset.Term Variable := fun index => if index = positive.output then p else q
    have hne : negative.output ≠ positive.output := by
      simp only [negative,positive,output_emit,length_emit]
      omega
    have hrefs : ∀ ref ∈ [positive.output,negative.output], cachedPrefix[ref]? = some (values ref) := by
      intro ref hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · simpa only [values,ite_true] using hlookupP
      · simpa only [values,ite_eq_right hne] using hlookupQ
    obtain ⟨suffix,hcount,hsrun,hsoutput⟩ := eval_buildClause FirstOrder.Language.Term.var
      [positive.output,negative.output] previous.output 1 negative.gates cachedPrefix values
      (tree n) (.var rootName) hcachedPrefixLength hn hprevious' hroot' hrefs
    have he : ((([positive.output,negative.output].map values).map
        (Reset.operation (Reset.Term Variable) (tree n))).foldr
        (Reset.operation (Reset.Term Variable)) (.var rootName)) = tree (n+1) := by
      simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,values,
        ite_true,ite_eq_right hne]
      rfl
    rw [he] at hsoutput
    refine ⟨cachedPrefix ++ suffix,?_,hsrun,hsoutput,lookup_append _ _ _ _ hroot'⟩
    change (cachedPrefix ++ suffix).length = (buildClause [positive.output,negative.output] previous.output 1 negative.gates).gates.length
    simp only [List.length_append,hcachedPrefixLength,hcount,length_buildClause]

/-- The two outputs designate the same shared graph output; its canonical
minimal-guard table is the ordinary table of this exact unfolded reset term. -/
theorem graph_unfold (n : ℕ) : (graph n).unfold = some (tree n,tree n) := by
  let _ := Equational.termStructure Reset.Symbol Variable
  obtain ⟨cache,_,hrun,hout,_⟩ := build_unfold n
  change ((runFrom (FirstOrder.Language.Term.var : Variable → Reset.Term Variable) (build n).gates []).bind fun values =>
    values[(build n).output]?.bind fun left =>
      values[(build n).output]?.bind fun right => some (left,right)) = _
  rw [hrun]
  change cache[(build n).output]?.bind _ = _
  rw [hout]
  rfl

/-- An explicit linear-size acyclic reset DAG whose actual canonical marker
table has at least 2^n incomparable minimal prerequisites. -/
theorem linear_graph_exponential_table (n : ℕ) :
    (graph n).WellFormed ∧
    (graph n).gates.length = 6*n+3 ∧
    operationCount (graph n).gates = 4*n+1 ∧
    (graph n).unfold = some (tree n,tree n) ∧
    2^n ≤ ((tree n).table markerName).card :=
  ⟨graph_wellFormed n,graph_gate_count n,graph_reset_gate_count n,graph_unfold n,exponential_table n⟩

end KFOL.Circuit.LargeTables
