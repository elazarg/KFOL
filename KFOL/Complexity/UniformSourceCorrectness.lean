module

public import KFOL.Complexity.UniformSourceSamples

/-! # Completing isolated source probes to exact rows

Each source bit fixes one winner predicate at its canonical probe. A
certificate gives the other predicates there. One exact interpolation
word must satisfy all of these completions simultaneously. -/

@[expose] public section
namespace KFOL.Complexity.UniformSourceSamples

open AddressedSourceOutput AddressTableOutput Core.ProfileBudgets Core.Sources TablePeeling
attribute [local instance] Equational.coreStructure

noncomputable def rowValue (x : Input) (hk : 0 < x.1) (i : ℕ) (j : Fin x.2.1) :
    WinnerSet (Fin x.1) := readMenu hk (inputMenu x i j.val)

private theorem block_of_head (x : Input) (shape : x.2.2.length = x.2.1*x.1^x.2.1) (j : Fin x.2.1) :
    block x = x.1^x.2.1 := by
  apply Nat.min_eq_left
  rw [shape]
  exact Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt j.isLt)

private theorem locations (x : Input) (hk : 0 < x.1) (shape : x.2.2.length = x.2.1*x.1^x.2.1)
    (j : Fin x.2.1) (sig : Fin (x.1^x.2.1)) :
    let i := j.val*x.1^x.2.1+sig.val
    head x i = j.val ∧ signature x i = sig.val := by
  dsimp only
  have size := block_of_head x shape j
  constructor
  · rw [head,size,Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.pow_pos hk),Nat.div_eq_of_lt sig.isLt,Nat.zero_add]
  · simp [signature,size,Nat.mod_eq_of_lt sig.isLt]

private theorem index_lt (x : Input) (shape : x.2.2.length = x.2.1*x.1^x.2.1)
    (j : Fin x.2.1) (sig : Fin (x.1^x.2.1)) : j.val*x.1^x.2.1+sig.val < x.2.2.length := by
  rw [shape]
  calc
    _ < j.val*x.1^x.2.1+x.1^x.2.1 := Nat.add_lt_add_left sig.isLt _
    _ = (j.val+1)*x.1^x.2.1 := (Nat.succ_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ j.isLt

private theorem observer_code (x : Input) (hk : 0 < x.1) (shape : x.2.2.length = x.2.1*x.1^x.2.1)
    {r : Fin x.1} {h : Fin x.2.1} {p : Pattern r h} {sig : Fin (x.1^x.2.1)} (code : Codes r h p sig) :
    observer x (h.val*x.1^x.2.1+sig.val) = r.val := by
  obtain ⟨headOK,sigOK⟩ := locations x hk shape h sig
  rw [observer,sigOK,headOK,observer_digit code]

private theorem read_probe (x : Input) (three : Fin 3 ↪ Fin x.1)
    (shape : x.2.2.length = x.2.1*x.1^x.2.1) {r : Fin x.1} {h : Fin x.2.1} {p : Pattern r h}
    {sig : Fin (x.1^x.2.1)} (code : Codes r h p sig) :
    rowValue x (Nat.zero_lt_of_lt r.isLt) (h.val*x.1^x.2.1+sig.val) = probe three r h p := by
  funext j
  have hk := Nat.zero_lt_of_lt r.isLt
  obtain ⟨headOK,sigOK⟩ := locations x hk shape h sig
  have regs : (allowed (inputMenu x (h.val*x.1^x.2.1+sig.val) j.val) : Set (Fin x.1)) =
      (probe three r h p j).val := by
    ext k
    change k.val ∈ (List.range x.1).filter _ ↔ _
    simp only [List.mem_filter,List.mem_range,k.isLt,true_and]
    simpa only [observer,sigOK,headOK] using flag_correct three r h p sig code j k
  have active := regs.symm ▸ (probe three r h p j).property
  apply Subtype.ext
  change (readMenu _ _).val = _
  rw [readMenu,dite_eq_left active]
  exact regs

private theorem samples_len (p : Proof) : (samples p).2.length = p.1.2.2.length := by simp [samples]

private theorem sample_values (p : Proof) (hk : 0 < p.1.1) (q : Fin (samples p).2.length) :
    TablePeeling.values hk (samples p) q = rowValue p.1 hk q.val := by
  funext j
  change readMenu hk (((samples p).2[q.val].1).getD j.val []) = _
  simp only [samples,List.getElem_map,List.getElem_range]
  have small : j.val < p.1.2.1 := j.isLt
  simp [rowValue,List.getD_eq_getElem?_getD,small]

private theorem sample_bounds (p : Proof) (q : Fin (samples p).2.length) (r : Fin p.1.1) :
    r ∈ bounds p.1.1 (samples p) q ↔ p.2.getD (q.val*p.1.1+r.val) false = true := by
  simp [bounds,allowed,samples,outputMenu]

/-- At fixed encoded owner count the direct list contains only the input
probes, irrespective of the size of the full table. -/
theorem source_iff_completion (x : Input) (three : Fin 3 ↪ Fin x.1) :
    x.2 ∈ AddressedSourceOutput.language three ↔ ∃ w : List Bool,
      w.length = width x ∧ consistent (x,w) = true ∧
        TablePeeling.Accepts (Nat.zero_lt_of_lt (three 0).isLt) (samples (x,w)) := by
  classical
  let d := x.2.1
  have hk : 0 < x.1 := Nat.zero_lt_of_lt (three 0).isLt
  have pos : 0 < x.1^x.2.1 := Nat.pow_pos hk
  constructor
  · rintro ⟨shape,t,agrees⟩
    let v (i : ℕ) := t.realize (rowValue x hk i)
    let w := (List.range (x.2.2.length*x.1)).map fun z =>
      decide (∃ r : Fin x.1, r.val = z%x.1 ∧ r ∈ (v (z/x.1)).val)
    have len : w.length = x.2.2.length*x.1 := by simp [w]
    have atBit (i : ℕ) (hi : i < x.2.2.length) (r : Fin x.1) :
        w.getD (i*x.1+r.val) false = true ↔ r ∈ (v i).val := by
      have ix : i*x.1+r.val < x.2.2.length*x.1 := calc
        _ < i*x.1+x.1 := Nat.add_lt_add_left r.isLt _
        _ = (i+1)*x.1 := (Nat.succ_mul ..).symm
        _ ≤ _ := Nat.mul_le_mul_right _ hi
      rw [List.getD_eq_getElem _ _ (len ▸ ix)]
      have div : (i*x.1+r.val)/x.1 = i := by
        rw [Nat.add_comm,Nat.add_mul_div_right _ _ hk,Nat.div_eq_of_lt r.isLt,Nat.zero_add]
      simp only [w,List.getElem_map,List.getElem_range,div,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt r.isLt,
        decide_eq_true_eq]
      exact ⟨fun ⟨s,e,h⟩ => (Fin.ext e : s = r) ▸ h, fun h => ⟨r,rfl,h⟩⟩
    refine ⟨w,len.trans (Nat.mul_comm ..), (consistent_iff (x,w)).mpr ⟨shape,?_⟩,t,?_⟩
    · intro i hi
      change i < x.2.2.length at hi
      let h : Fin d := ⟨i/x.1^x.2.1,(Nat.div_lt_iff_lt_mul pos).mpr (shape ▸ hi)⟩
      let sig : Fin (x.1^x.2.1) := ⟨i%x.1^x.2.1,Nat.mod_lt _ pos⟩
      obtain ⟨r,p,code⟩ := codes_exhaust hk h sig
      have eq : h.val*x.1^x.2.1+sig.val = i := Nat.div_add_mod' ..
      have obs := observer_code x hk shape code
      have probeOK := read_probe x three shape code
      have hit := agrees r h p sig code
      rw [eq] at obs probeOK hit
      change x.2.2.getD i false = w.getD (i*x.1+observer x i) false
      rw [obs]
      apply Bool.eq_iff_iff.mpr
      have here : v i = t.realize (probe three r h p) := congrArg t.realize probeOK
      rw [← here] at hit
      exact hit.trans (atBit i hi r).symm
    · intro q
      have e := congrArg (fun ν : Fin x.2.1 → WinnerSet (Fin x.1) => (t.realize ν).val) (sample_values (x,w) hk q)
      apply e.trans
      ext r
      exact ((atBit q.val (samples_len (x,w) ▸ q.isLt) r).symm).trans (sample_bounds (x,w) q r).symm
  · rintro ⟨w,_,cert,t,word⟩
    obtain ⟨shape,checks⟩ := (consistent_iff _).mp cert
    refine ⟨shape,t,fun r h p sig code => ?_⟩
    let i := h.val*x.1^x.2.1+sig.val
    have hi : i < x.2.2.length := index_lt x shape h sig
    let q : Fin (samples (x,w)).2.length := ⟨i,(samples_len (x,w)).symm ▸ hi⟩
    have eq := checks i hi
    change x.2.2.getD i false = w.getD (i*x.1+observer x i) false at eq
    have obs : observer x i = r.val := observer_code x hk shape code
    rw [obs] at eq
    have align := (sample_values (x,w) hk q).trans (show rowValue x hk q.val = probe three r h p from
      read_probe x three shape code)
    have real := (congrArg (fun ν : Fin x.2.1 → WinnerSet (Fin x.1) => (t.realize ν).val) align).symm.trans (word q)
    change x.2.2.getD i false = true ↔ r ∈ (t.realize (probe three r h p)).val
    rw [eq,real]
    exact (sample_bounds (x,w) q r).symm

end KFOL.Complexity.UniformSourceSamples
