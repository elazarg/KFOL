module

public import KFOL.Complexity.CoreExtractionArrays
public import KFOL.Complexity.FullTermFoldRuntime

/-! # The complete uniform original syntax validator is a native polynomial machine -/

@[expose] public section

namespace KFOL.Complexity.CoreExtraction

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

/-- The original finite arities determine which actual child flags are read. -/
def validNode (K : ℕ) (operation : Operation) (children : List Bool) : Bool :=
  match operation with
  | ⟨_,.winner role⟩ => decide (role < K)
  | ⟨_,.choice owner⟩ => decide (owner < K) && children.getD 0 false && children.getD 1 false
  | ⟨_,.rename forward⟩ => validArray K forward && children.getD 0 false

theorem fold_valid (K : ℕ) (raw : Raw) :
    FullTermFold.fold (fun _ _ => true) validNode K raw = valid K raw := by
  induction raw with
  | var name => rfl
  | @func n operation children ih =>
    cases operation <;> simp [FullTermFold.fold,validNode,valid,List.ofFn_succ,ih]

theorem validNode_polyTime : ComputableInPolyTime
    (fun p : ℕ × (Operation × List Bool) => validNode p.1 p.2.1 p.2.2)
    (encPair encNat (encPair FullTermMachines.operationEncoding (encList encBool))) encBool := by
  let input := encPair encNat (encPair FullTermMachines.operationEncoding (encList encBool))
  have hK : ComputableInPolyTime (fun p : ℕ × (Operation × List Bool) => p.1) input encNat := by fun_prop
  have hop : ComputableInPolyTime (fun p : ℕ × (Operation × List Bool) => p.2.1)
      input FullTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime (fun p : ℕ × (Operation × List Bool) => p.2.2)
      input (encList encBool) := by fun_prop
  have hrole := FullTermMachines.roleLabel_polyTime.comp hop
  have hforward := FullTermMachines.forwardArray_polyTime.comp hop
  have hkind := FullTermMachines.operationKind_polyTime.comp hop
  have hless := binary_lt' hrole hK
  have harray := validArray_polyTime.comp (hK.prod hforward)
  have hzero := (listGetD (encA := encBool) false).comp (hc.prod (const 0))
  have hone := (listGetD (encA := encBool) false).comp (hc.prod (const 1))
  let branch (kind : Fin 3) (p : ℕ × (Operation × List Bool)) : Bool :=
    if kind = 0 then decide (FullTermMachines.roleLabel p.2.1 < p.1)
    else if kind = 1 then validArray p.1 (FullTermMachines.forwardArray p.2.1) && p.2.2.getD 0 false
    else decide (FullTermMachines.roleLabel p.2.1 < p.1) && p.2.2.getD 0 false && p.2.2.getD 1 false
  have hb (kind : Fin 3) : ComputableInPolyTime (branch kind) input encBool := by
    fin_cases kind
    · exact hless
    · exact bool_and' harray hzero
    · exact bool_and' (bool_and' hless hzero) hone
  have h := hkind.finite_cases (branch := branch) hb
  convert h using 1
  funext p
  rcases p with ⟨K,⟨⟨n,symbol⟩,children⟩⟩
  cases symbol <;> rfl

/-- Complete raw validation is polynomial in actual original tree bytes and
binary K. No number derived from K is used as a list traversal clock. -/
theorem valid_polyTime : ComputableInPolyTime
    (fun p : ℕ × Raw => valid p.1 p.2)
    (encPair encNat FullTermMachines.termEncoding) encBool := by
  have hbool (value : Bool) : (encBool value).length = 1 := by cases value <;> rfl
  have h := FullTermFold.fold_polyTime (contextEncoding := encNat) (valueEncoding := encBool)
    (fun _ _ => true) validNode (const true) validNode_polyTime 1 0
    (by intro K raw; rw [hbool]; simp) false
  convert h using 1
  funext p
  exact (fold_valid p.1 p.2).symm

end KFOL.Complexity.CoreExtraction
