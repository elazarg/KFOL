module

public import KFOL.Complexity.ExplicitSourceHardness
public import KFOL.Complexity.TablePeelingFrontend
public import Complexity.Computability.Complexity.Classes.Space.Closure

/-! # Polynomial-space transfer from explicit winners to explicit source bits

At fixed K the complete winner table has polynomial size in a well-formed
source table. Guess its K membership bits per row, check that a core word
realizes it, and compare the actual projected bits to the input.
-/

@[expose] public section
namespace KFOL.Complexity.ExplicitSourceSpace

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity AddressTableOutput
open AddressedPoint AddressedSourceOutput FullSparseEvaluation Core.ProfileBudgets
attribute [local instance] Equational.coreStructure

abbrev Source := ℕ × List Bool
abbrev ProofInput := Source × List Bool
abbrev proofEncoding := encPair sourceEncoding encBits

def rowCount (k : ℕ) (s : Source) : ℕ := min ((2^k-1)^s.1) ((s.2.length+1)^k)
def width (k : ℕ) (s : Source) : ℕ := rowCount k s * k

def unpack (k : ℕ) (p : ProofInput) : TableInput :=
  (p.1.1, (List.range (p.2.length / k)).map fun i =>
    (List.range k).filter fun r => p.2.getD (i*k+r) false)

theorem width_poly (k : ℕ) : ComputableInPolyTime (width k) sourceEncoding encUnary := by
  let bitlen := length_bits.comp (snd encUnary encBits)
  have cap := (unary_pow k).comp (unary_add' bitlen (const 1))
  have count := binary_pow' (const (2^k-1)) (fst encUnary encBits)
  have actual := binary_min_unary' cap count
  apply (unary_mul' actual (const k)).of_enc_eq
  intro s
  simp [width,rowCount,Nat.min_comm]

private theorem bin_menu : ComputableInPolyTime (fun m : List ℕ => m) (encList encUnary)
    AddressedEnvelope.namesEncoding := by
  rw [show (fun m : List ℕ => m) = List.map (fun r : ℕ => r) by funext m; exact (List.map_id' m).symm]
  exact ComputableInPolyTime.map unary_to_binary

theorem unpack_poly (k : ℕ) : ComputableInPolyTime (unpack k) proofEncoding AddressedPoint.tableEncoding := by
  let word := snd sourceEncoding encBits
  have count := unary_div.comp ((length_bits.comp word).prod (const k))
  refine ((fst encUnary encBits).comp (fst sourceEncoding encBits)).prod ?_
  apply mapWithInput (f := fun p i => (List.range k).filter fun r => p.2.getD (i*k+r) false)
    (ComputableInPolyTime.range.comp count)
  apply bin_menu.comp
  apply filterWithInput (test := fun (p : ProofInput × ℕ) r => p.1.2.getD (p.2*k+r) false)
    (const (encOut := encList encUnary) (List.range k))
  let pre := fst (encPair proofEncoding encUnary) encUnary
  exact bitsGetDWithInput ((word.comp (fst proofEncoding encUnary)).comp pre)
    (unary_add' (unary_mul' ((snd proofEncoding encUnary).comp pre) (const k)) (snd _ _)) false

private theorem actual_count {k : ℕ} (hk : 2 ≤ k) (s : Source) (shape : s.2.length = s.1*k^s.1) :
    rowCount k s = (2^k-1)^s.1 := by
  unfold rowCount
  apply Nat.min_eq_left
  calc
    (2^k-1)^s.1 ≤ (k^k)^s.1 := Nat.pow_le_pow_left ((Nat.sub_le ..).trans (Nat.pow_le_pow_left hk k)) _
    _ = (k^s.1)^k := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (s.2.length+1)^k := by
      apply Nat.pow_le_pow_left
      rw [shape]
      cases s.1 with
      | zero => simp
      | succ d => rw [Nat.succ_mul]; omega

private noncomputable def canonical {k d : ℕ} (hk : 0 < k) (t : CoreTerm (Fin k) (Fin d)) (i : ℕ) :=
  t.realize (fun j : Fin d => TablePeeling.readMenu hk (menu k i j.val))

private theorem canonical_eq {k d : ℕ} (hk : 0 < k) (t : CoreTerm (Fin k) (Fin d))
    (i : ℕ) (v : Fin d → WinnerSet (Fin k)) (h : ∀ j, Represents (menu k i j.val) (v j)) :
    canonical hk t i = t.realize v := by
  have same (j : Fin d) := (represents_equal_iff (TablePeeling.read_represents hk i j.val) (h j)).mp rfl
  exact congrArg (fun w => t.realize w) (funext same)

private theorem winnerRows_of_raw {k d : ℕ} {xs : Menus} (ht : RawAccepts k (d,xs)) :
    ∃ t : CoreTerm (Fin k) (Fin d), WinnerRows k d xs (fun v => t.realize v) := by
  obtain ⟨len,t,hit⟩ := ht
  refine ⟨t,len,?_⟩
  intro i hi v bits r
  apply represents_mem (hit i (len ▸ hi) v _) r
  intro j
  apply represents_ext
  · exact fun u mem => ((menu_mem ..).mp mem).1
  · intro a
    exact ((menu_mem ..).trans (and_iff_right a.isLt)).trans (bits j a)

private theorem fits_iff {k : ℕ} (three : Fin 3 ↪ Fin k) (s : Source) :
    s ∈ language three ↔ ∃ w : List Bool, w.length = width k s ∧
      RawAccepts k (unpack k (s,w)) ∧ project k (unpack k (s,w)) = s := by
  classical
  have big : 3 ≤ k := by simpa using Fintype.card_le_of_embedding three
  have hk : 0 < k := by omega
  constructor
  · rintro ⟨shape,t,agrees⟩
    let n := (2^k-1)^s.1
    let w := (List.range (n*k)).map fun ix =>
      decide (∃ r : Fin k, r.val = ix%k ∧ r ∈ (canonical hk t (ix/k)).val)
    have len : w.length = n*k := by simp [w]
    have bound := actual_count (by omega : 2 ≤ k) s shape
    have outlen : (unpack k (s,w)).2.length = n := by simp [unpack,len,Nat.mul_div_cancel _ hk]
    have atBit (i : ℕ) (hi : i < n) (r : Fin k) :
        w.getD (i*k+r.val) false = true ↔ r ∈ (canonical hk t i).val := by
      have ix : i*k+r.val < n*k := calc
        i*k+r.val < i*k+k := Nat.add_lt_add_left r.isLt _
        _ = (i+1)*k := (Nat.succ_mul i k).symm
        _ ≤ n*k := Nat.mul_le_mul_right _ hi
      rw [List.getD_eq_getElem _ _ (len ▸ ix)]
      have quot : (i*k+r.val)/k = i := by rw [Nat.mul_comm i k,Nat.mul_add_div hk,Nat.div_eq_of_lt r.isLt,Nat.add_zero]
      simp only [w,List.getElem_map,List.getElem_range,decide_eq_true_eq,
        Nat.mul_add_mod_of_lt r.isLt,quot]
      exact ⟨fun ⟨s,h,hv⟩ => Fin.ext h ▸ hv,fun hv => ⟨r,rfl,hv⟩⟩
    have rep (i : ℕ) (hi : i < n) :
        Represents ((unpack k (s,w)).2.getD i []) (canonical hk t i) := by
      rw [List.getD_eq_getElem _ _ (outlen ▸ hi)]
      apply represents_ext
      · intro j hj
        simp only [unpack,List.getElem_map,List.getElem_range,List.mem_filter,List.mem_range] at hj
        exact hj.1
      · intro r
        simp only [unpack,List.getElem_map,List.getElem_range,List.mem_filter,List.mem_range,r.isLt,true_and]
        exact atBit i hi r
    have raw : RawAccepts k (unpack k (s,w)) := by
      refine ⟨outlen,t,fun i hi v fits => ?_⟩
      exact canonical_eq hk t i v fits ▸ rep i hi
    have rows : WinnerRows k s.1 (unpack k (s,w)).2 (fun v => t.realize v) := by
      refine ⟨outlen,fun i hi v bits r => ?_⟩
      have named (j : Fin s.1) : Represents (menu k i j.val) (v j) := by
        apply represents_ext
        · exact fun u hu => ((menu_mem ..).mp hu).1
        · intro a
          exact ((menu_mem ..).trans (and_iff_right a.isLt)).trans (bits j a)
      rw [← canonical_eq hk t i v named]
      exact represents_mem (rep i (outlen ▸ hi)) r
    refine ⟨w,by simpa [width,bound,n] using len,raw,Prod.ext rfl ?_⟩
    apply List.ext_getElem
    · exact (projected_length rows.length).trans shape.symm
    · intro j h1 h2
      have pos : 0 < k^s.1 := Nat.pow_pos hk
      have jd : j / k^s.1 < s.1 := (Nat.div_lt_iff_lt_mul pos).mpr (shape ▸ h2)
      let h : Fin s.1 := ⟨_,jd⟩
      let sig : Fin (k^s.1) := ⟨j % k^s.1,Nat.mod_lt _ pos⟩
      obtain ⟨r,p,code⟩ := codes_exhaust hk h sig
      have idx : h.val*k^s.1+sig.val = j := Nat.div_add_mod' _ _
      have yes := (projected_bit three rows r h p sig code).trans (agrees r h p sig code).symm
      rw [idx] at yes
      change (project k (unpack k (s,w))).2.getD j false = true ↔ s.2.getD j false = true at yes
      rw [List.getD_eq_getElem _ _ h1,List.getD_eq_getElem _ _ h2] at yes
      exact Bool.eq_iff_iff.mpr yes
  · rintro ⟨w,_,raw,eq⟩
    obtain ⟨t,rows⟩ := winnerRows_of_raw raw
    rw [← eq]
    apply (project_mem_iff three rows).mpr
    exact ⟨t,fun _ _ _ => Iff.rfl⟩

theorem mem_PSPACE_of_winner {k : ℕ} (three : Fin 3 ↪ Fin k)
    (full : {p | RawAccepts k p} ∈ PSPACE AddressedPoint.tableEncoding) :
    language three ∈ PSPACE sourceEncoding := by
  have real : {p : ProofInput | RawAccepts k (unpack k p)} ∈ PSPACE proofEncoding :=
    PolyTimeReducible.mem_PSPACE ⟨_,unpack_poly k,fun _ => Iff.rfl⟩ full
  have equal : {p : ProofInput | project k (unpack k p) = p.1} ∈ P proofEncoding :=
    ⟨_,decide_eq' ((project_poly k).comp (unpack_poly k)) (fst _ _),fun _ => by simp⟩
  have both := inter_mem_PSPACE real (P_subset_PSPACE equal)
  convert setOf_exists_mem_PSPACE both (width_poly k) using 1
  ext s
  exact fits_iff three s

end KFOL.Complexity.ExplicitSourceSpace
