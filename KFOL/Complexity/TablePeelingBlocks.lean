module

public import KFOL.Core.ExactSplit

/-! # Encoding an exact split into one prover move

The first K bits are an owner header. The remaining pairs of bits give
the two child goals in row-major order. -/

@[expose] public section
namespace KFOL.Complexity.TablePeelingBlocks

open Core.ExactSplit

variable {K n : ℕ}

def goalAt (G : Goal (Fin n) (Fin K)) (i k : ℕ) : Bool :=
  if hi : i < n then if hk : k < K then decide ((⟨i,hi⟩,⟨k,hk⟩) ∈ G) else false else false

def pack (owner : Fin K) (L R : Goal (Fin n) (Fin K)) : List Bool :=
  (List.range (K + 2*n*K)).map fun z =>
    if z < K then decide (z = owner.val) else
      let field := z-K
      let entry := field/2
      goalAt (if field%2 = 1 then R else L) (entry/K) (entry%K)

@[simp] theorem pack_length (owner : Fin K) (L R : Goal (Fin n) (Fin K)) :
    (pack owner L R).length = K + 2*n*K := by simp [pack]

theorem pack_header (owner : Fin K) (L R : Goal (Fin n) (Fin K)) (k : Fin K) :
    (pack owner L R).getD k.val false = decide (k.val = owner.val) := by
  have h : k.val < K+2*n*K := Nat.lt_of_lt_of_le k.isLt (Nat.le_add_right _ _)
  simp [pack,List.getD_eq_getElem?_getD,h,k.isLt]

theorem pack_child (owner : Fin K) (L R : Goal (Fin n) (Fin K)) (side : Bool) (i : Fin n) (k : Fin K) :
    (pack owner L R).getD (K+2*(i.val*K+k.val)+side.toNat) false =
      decide ((i,k) ∈ (if side then R else L)) := by
  have hi := i.isLt
  have hk := k.isLt
  have positive : 0 < K := Nat.zero_lt_of_lt hk
  have le := Nat.mul_le_mul_right K (show i.val+1 ≤ n from hi)
  rw [Nat.add_mul,Nat.one_mul] at le
  have lim : i.val*K+k.val < n*K := by omega
  have sb : side.toNat < 2 := by cases side <;> decide
  have idx : K+2*(i.val*K+k.val)+side.toNat < K+2*n*K := by rw [Nat.mul_assoc]; omega
  have high : ¬(K+2*(i.val*K+k.val)+side.toNat < K) := by omega
  have field : K+2*(i.val*K+k.val)+side.toNat-K = 2*(i.val*K+k.val)+side.toNat := by omega
  have div : (i.val*K+k.val)/K = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ positive, Nat.div_eq_of_lt hk, Nat.zero_add]
  have modp : (i.val*K+k.val)%K = k.val := by simp [Nat.mod_eq_of_lt hk]
  simp only [pack,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range idx,
    Option.map_some,Option.getD_some,ite_eq_right high,field]
  have de : (2*(i.val*K+k.val)+side.toNat)/2 = i.val*K+k.val := by omega
  have mo : (2*(i.val*K+k.val)+side.toNat)%2 = side.toNat := by omega
  rw [de,mo,div,modp]
  cases side <;> simp [goalAt,i.isLt,k.isLt]

/-- A header produced by pack selects exactly the designated owner. -/
theorem header_select (owner : Fin K) (L R : Goal (Fin n) (Fin K)) :
    ((List.range K).filter fun j => (pack owner L R).getD j false).headD 0 = owner.val := by
  let xs := (List.range K).filter fun j => (pack owner L R).getD j false
  have own : owner.val ∈ xs := List.mem_filter.mpr
    ⟨List.mem_range.mpr owner.isLt,(pack_header owner L R owner).trans (decide_eq_true rfl)⟩
  have only (j) (h : j ∈ xs) : j = owner.val := by
    obtain ⟨inRange,hit⟩ := List.mem_filter.mp h
    let k : Fin K := ⟨j,List.mem_range.mp inRange⟩
    exact of_decide_eq_true ((pack_header owner L R k).symm.trans hit)
  change xs.headD 0 = _
  cases hx : xs with
  | nil => rw [hx] at own; exact False.elim (List.not_mem_nil own)
  | cons a tail => exact only a (hx ▸ List.mem_cons_self)

end KFOL.Complexity.TablePeelingBlocks
