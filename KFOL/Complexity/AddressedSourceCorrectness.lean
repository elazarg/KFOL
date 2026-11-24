module

public import KFOL.Complexity.AddressedSourceOutput
public import KFOL.Core.ProfileBudgets.Folds

/-! # Exact semantics of the polynomial-time source projection -/

@[expose] public section
namespace KFOL.Complexity.AddressedSourceOutput

open Core.Sources Core.ProfileBudgets AddressTableOutput
attribute [local instance] Equational.coreStructure

/-- The marked coordinate stores the observer. At each other coordinate
the observer names the neutral status and the other roles name atoms. -/
def code {K d : ℕ} (r : Fin K) (h : Fin d) (p : Pattern r h) (j : Fin d) : Fin K :=
  if hj : j = h then r else
    match p ⟨j,hj⟩ with
    | .neutral => r
    | .atom s => s.val

def Codes {K d : ℕ} (r : Fin K) (h : Fin d) (p : Pattern r h) (i : Fin (K^d)) : Prop :=
  ∀ j : Fin d, digit K i.val j.val = (code r h p j).val

/-- Each observation occurs at a unique numerical signature in its block. -/
theorem codes_unique {K d : ℕ} (r : Fin K) (h : Fin d) (p : Pattern r h) :
    ∃! i : Fin (K^d), Codes r h p i := by
  have pos : 0 < K := Nat.zero_lt_of_lt r.isLt
  obtain ⟨i, eq⟩ := (digits_bijective K d pos).surjective (code r h p)
  have hi : Codes r h p i := fun j => congrArg Fin.val (congrFun eq j)
  refine ⟨i,hi,fun u hu => ?_⟩
  apply Fin.ext
  exact digit_ext pos u.isLt i.isLt (fun _ hj => (hu ⟨_,hj⟩).trans (hi ⟨_,hj⟩).symm)

/-- Every numerical signature is an actual head/observer/pattern triple. -/
theorem codes_exhaust {K d : ℕ} (pos : 0 < K) (h : Fin d) (i : Fin (K^d)) :
    ∃ (r : Fin K) (p : Pattern r h), Codes r h p i := by
  let color (j : Fin d) : Fin K := ⟨digit K i.val j.val,Nat.mod_lt _ pos⟩
  let r := color h
  let p : Pattern r h := fun j => if eq : color j.val = r then .neutral else .atom ⟨color j.val,eq⟩
  refine ⟨r,p,fun j => ?_⟩
  by_cases same : j = h
  · subst j; simp [code,r,color]
  · by_cases neutral : color j = r
    · simpa only [code, dite_eq_right same, p, dite_eq_left neutral] using congrArg Fin.val neutral
    · simp [code,same,p,neutral,color]

private theorem observer_digit {K d : ℕ} {r : Fin K} {h : Fin d} {p : Pattern r h}
    {i : Fin (K^d)} (cs : Codes r h p i) : digit K i.val h.val = r.val := by
  simpa [code] using cs h

private theorem flag_correct {K d : ℕ} (three : Fin 3 ↪ Fin K) (r : Fin K) (h : Fin d)
    (p : Pattern r h) (i : Fin (K^d)) (cs : Codes r h p i) (j : Fin d) (s : Fin K) :
    probeFlag (digit K i.val h.val) (digit K i.val j.val) s.val (decide (j.val = h.val)) = true ↔
      s ∈ (probe three r h p j).val := by
  rw [observer_digit cs, cs j]
  classical
  by_cases same : j = h
  · subst j
    simp [probeFlag, code, Fin.ext_iff]
  · rw [probe_other three r h p j same]
    have dif : j.val ≠ h.val := fun eq => same (Fin.ext eq)
    cases pc : p ⟨j,same⟩ with
    | neutral =>
      simp [code,same,pc,probeFlag,dif,representative,PlayerView.representative,Fin.ext_iff]
    | atom s' =>
      have foreign : s'.val.val ≠ r.val := fun eq => s'.property (Fin.ext eq)
      simp [code,same,pc,probeFlag,dif,foreign,representative,Fin.ext_iff]

/-- Read the standard winner-table order directly through its binary masks. -/
structure WinnerRows (K d : ℕ) (rows : List AddressedEnvelope.Names)
    (F : (Fin d → WinnerSet (Fin K)) → WinnerSet (Fin K)) : Prop where
  length : rows.length = (2^K - 1)^d
  entry : ∀ i < rows.length, ∀ v : Fin d → WinnerSet (Fin K),
    (∀ j r, (mask K i j.val).testBit r.val = true ↔ r ∈ (v j).val) →
      ∀ r : Fin K, r.val ∈ rows.getD i [] ↔ r ∈ (F v).val

private theorem is_blockSize {K d : ℕ} {rows : List AddressedEnvelope.Names}
    (len : rows.length = (2^K - 1)^d) : blockSize K (d,rows) = K^d := by
  apply Nat.min_eq_left
  rw [len]
  have h := Nat.lt_two_pow_self (n := K)
  exact Nat.pow_le_pow_left (by omega) _

private theorem sameInput_iff {K d : ℕ} (three : Fin 3 ↪ Fin K) (r : Fin K) (h : Fin d)
    (p : Pattern r h) (sig : Fin (K^d)) (cs : Codes r h p sig) (i : ℕ) :
    sameInput K d i h.val sig.val = true ↔
      ∀ j : Fin d, ∀ s : Fin K, (mask K i j.val).testBit s.val = true ↔ s ∈ (probe three r h p j).val := by
  simp only [sameInput,List.all_eq_true,List.mem_range,decide_eq_true_eq]
  constructor
  · intro all j s
    rw [all j.val j.isLt s.val s.isLt]
    exact flag_correct three r h p sig cs j s
  · intro all j hj s hs
    apply Bool.eq_iff_iff.mpr
    exact (all ⟨j,hj⟩ ⟨s,hs⟩).trans (flag_correct three r h p sig cs ⟨j,hj⟩ ⟨s,hs⟩).symm

theorem lookup_correct {K d : ℕ} (three : Fin 3 ↪ Fin K) {rows : List AddressedEnvelope.Names}
    {F : (Fin d → WinnerSet (Fin K)) → WinnerSet (Fin K)} (ht : WinnerRows K d rows F)
    (r : Fin K) (h : Fin d) (p : Pattern r h) (sig : Fin (K^d)) (cs : Codes r h p sig) :
    lookup K (d,rows) h.val sig.val = true ↔ r ∈ (F (probe three r h p)).val := by
  classical
  simp only [lookup, List.any_eq_true,List.mem_range,Bool.and_eq_true, AddressedEnvelope.member_iff,
    observer_digit cs]
  constructor
  · rintro ⟨i,hi,matchPoint,win⟩
    exact (ht.entry i hi _ ((sameInput_iff three r h p sig cs i).mp matchPoint) r).mp win
  · intro win
    let v := probe three r h p
    let flags (j : Fin d) (s : Fin K) := decide (s ∈ (v j).val)
    have present (j : Fin d) : ∃ s, flags j s = true := by
      obtain ⟨s,hs⟩ := (v j).property
      exact ⟨s,decide_eq_true hs⟩
    obtain ⟨i,ok,_⟩ := tuple_index_unique K d (Nat.zero_lt_of_lt r.isLt) flags present
    have atPoint (j : Fin d) (s : Fin K) : (mask K i.val j.val).testBit s.val = true ↔ s ∈ (v j).val := by
      rw [ok j s]
      exact decide_eq_true_iff
    have hi : i.val < rows.length := by rw [ht.length]; exact i.isLt
    exact ⟨i.val,hi,(sameInput_iff three r h p sig cs i.val).mpr atPoint,(ht.entry _ hi v atPoint r).mpr win⟩

theorem projected_length {K d : ℕ} {rows : List AddressedEnvelope.Names}
    (len : rows.length = (2^K - 1)^d) : (project K (d,rows)).2.length = d*K^d := by
  simp only [project,List.length_map,List.length_range,is_blockSize len]

theorem projected_bit {K d : ℕ} (three : Fin 3 ↪ Fin K) {rows : List AddressedEnvelope.Names}
    {F : (Fin d → WinnerSet (Fin K)) → WinnerSet (Fin K)} (ht : WinnerRows K d rows F)
    (r : Fin K) (h : Fin d) (p : Pattern r h) (sig : Fin (K^d)) (cs : Codes r h p sig) :
    (project K (d,rows)).2.getD (h.val*K^d+sig.val) false = true ↔ r ∈ (F (probe three r h p)).val := by
  have pos : 0 < K^d := Nat.pow_pos (Nat.zero_lt_of_lt r.isLt)
  have bound : h.val*K^d + sig.val < d*K^d := by
    calc h.val*K^d + sig.val < h.val*K^d + K^d := Nat.add_lt_add_left sig.isLt _
         _ = (h.val+1)*K^d := (Nat.succ_mul _ _).symm
         _ ≤ d*K^d := Nat.mul_le_mul_right _ h.isLt
  have num : (h.val*K^d+sig.val) / K^d = h.val := by
    rw [Nat.mul_comm h.val, Nat.mul_add_div pos, Nat.div_eq_of_lt sig.isLt, Nat.add_zero]
  have rem : (h.val*K^d+sig.val) % K^d = sig.val := by simp [Nat.mod_eq_of_lt sig.isLt]
  rw [List.getD_eq_getElem _ _ (by rwa [projected_length ht.length])]
  simp only [project,List.getElem_map,List.getElem_range,is_blockSize ht.length,num,rem]
  exact lookup_correct three ht r h p sig cs

open scoped Classical

/-- The actual encoded source-table recognition language for a fixed set
of roles. Its output has one Boolean entry per isolated source probe. -/
def language {K : ℕ} (three : Fin 3 ↪ Fin K) : Set (ℕ × List Bool) := {data |
  data.2.length = data.1*K^data.1 ∧ ∃ t : CoreTerm (Fin K) (Fin data.1),
    ∀ (r : Fin K) (h : Fin data.1) (p : Pattern r h) (s : Fin (K^data.1)), Codes r h p s →
      (data.2.getD (h.val*K^data.1+s.val) false = true ↔ r ∈ (t.realize (probe three r h p)).val)}

/-- The projected table admits a word precisely when its source probes
are those of a word. This applies equally to both formula truth values. -/
theorem project_mem_iff {K d : ℕ} (three : Fin 3 ↪ Fin K) {rows : List AddressedEnvelope.Names}
    {F : (Fin d → WinnerSet (Fin K)) → WinnerSet (Fin K)} (ht : WinnerRows K d rows F) :
    project K (d,rows) ∈ language three ↔ ∃ t : CoreTerm (Fin K) (Fin d),
      ∀ (r : Fin K) (j : Fin d) (p : Pattern r j), r ∈ (t.realize (probe three r j p)).val ↔
        r ∈ (F (probe three r j p)).val := by
  constructor
  · rintro ⟨_,t,agrees⟩
    refine ⟨t,fun r j p => ?_⟩
    obtain ⟨s,h,_⟩ := codes_unique r j p
    exact (agrees r j p s h).symm.trans (projected_bit three ht r j p s h)
  · rintro ⟨t,agrees⟩
    exact ⟨projected_length ht.length,t,fun r j p s h =>
      (projected_bit three ht r j p s h).trans (agrees r j p).symm⟩


private def pullPattern {K : ℕ} {V W : Type*} (e : V ≃ W) {r : Fin K} (h : W) (p : Pattern r h) :
    Pattern r (e.symm h) := fun i => p ⟨e i.val,fun eq => i.property (e.eq_symm_apply.mpr eq)⟩

private theorem probe_pull {K : ℕ} {V W : Type*} (e : V ≃ W) (three : Fin 3 ↪ Fin K)
    (r : Fin K) (h : W) (p : Pattern r h) :
    probe three r (e.symm h) (pullPattern e h p) = fun i => probe three r h p (e i) := by
  classical
  funext i
  by_cases eq : i = e.symm h
  · subst i
    simp
  · have dif : e i ≠ h := fun same => eq (e.eq_symm_apply.mpr same)
    rw [probe_other _ _ _ _ _ eq, probe_other _ _ _ _ _ dif]
    rfl

/-- Projection commutes with the coordinate bijection used by the compiler.
The right side uses the native operation, before naming its variables by
positions in the full and source tables. -/
theorem project_native_iff {K d : ℕ} {V : Type*} (three : Fin 3 ↪ Fin K) (rank : V ≃ Fin d)
    {rows : List AddressedEnvelope.Names} {F : (V → WinnerSet (Fin K)) → WinnerSet (Fin K)}
    (ht : WinnerRows K d rows (fun v => F (fun j => v (rank j)))) :
    project K (d,rows) ∈ language three ↔ ∃ t : CoreTerm (Fin K) V,
      ∀ (r : Fin K) (j : V) (p : Pattern r j), r ∈ (t.realize (probe three r j p)).val ↔
        r ∈ (F (probe three r j p)).val := by
  rw [project_mem_iff three ht]
  constructor
  · rintro ⟨t,agrees⟩
    refine ⟨t.relabel rank.symm,fun r j p => ?_⟩
    rw [FirstOrder.Language.Term.realize_relabel]
    have h := agrees r (rank j) (pullPattern rank.symm j p)
    have pull : probe three r (rank j) (pullPattern rank.symm j p) =
        fun a => probe three r j p (rank.symm a) := probe_pull rank.symm three r j p
    simpa only [pull, Equiv.symm_apply_apply, Function.comp_def] using h
  · rintro ⟨t,agrees⟩
    refine ⟨t.relabel rank,fun r j p => ?_⟩
    rw [FirstOrder.Language.Term.realize_relabel]
    simpa only [probe_pull rank, Function.comp_def] using agrees r (rank.symm j) (pullPattern rank j p)

end KFOL.Complexity.AddressedSourceOutput
