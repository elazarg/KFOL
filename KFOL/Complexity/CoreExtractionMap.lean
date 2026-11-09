module

public import KFOL.Complexity.CoreExtractionValidation
public import KFOL.Algorithms.FullTermCode.Core
public import KFOL.Complexity.CoreExtractionBounds

/-! # Native raw constructor and label-map callbacks for uniform core extraction -/

@[expose] public section

namespace KFOL.Complexity.CoreExtraction

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

/-- Raw constructors write their original operation code and unframed actual
children, without enumerating a role-dependent operation alphabet. -/
theorem rawWinner_polyTime : ComputableInPolyTime rawWinner encNat FullTermMachines.termEncoding := by
  have h := FullTermMachines.construct_polyTime.comp
    (FullTermMachines.winnerOperation_polyTime.prod (const []))
  exact h.of_enc_eq (fun _ => rfl)

theorem rawChoice_polyTime : ComputableInPolyTime
    (fun p : ℕ × (Raw × Raw) => rawChoice p.1 p.2.1 p.2.2)
    (encPair encNat (encPair FullTermMachines.termEncoding FullTermMachines.termEncoding))
    FullTermMachines.termEncoding := by
  let input := encPair encNat (encPair FullTermMachines.termEncoding FullTermMachines.termEncoding)
  have howner : ComputableInPolyTime (fun p : ℕ × (Raw × Raw) => p.1) input encNat := by fun_prop
  have hl : ComputableInPolyTime (fun p : ℕ × (Raw × Raw) => p.2.1) input FullTermMachines.termEncoding := by fun_prop
  have hr : ComputableInPolyTime (fun p : ℕ × (Raw × Raw) => p.2.2) input FullTermMachines.termEncoding := by fun_prop
  have h := FullTermMachines.construct_polyTime.comp
    ((FullTermMachines.choiceOperation_polyTime.comp howner).prod (cons' hl (cons' hr (const []))))
  exact h.of_enc_eq (fun _ => rfl)

theorem rawRename_polyTime : ComputableInPolyTime
    (fun p : List ℕ × Raw => rawRename p.1 p.2)
    (encPair arrayEncoding FullTermMachines.termEncoding) FullTermMachines.termEncoding := by
  have hf := fst arrayEncoding FullTermMachines.termEncoding
  have hc := snd arrayEncoding FullTermMachines.termEncoding
  have h := FullTermMachines.construct_polyTime.comp
    ((FullTermMachines.renameOperation_polyTime.comp hf).prod (cons' hc (const [])))
  exact h.of_enc_eq (fun _ => rfl)

/-- Labels are looked up only in the physically stored context array. -/
def mapNode (forward : List ℕ) (operation : Operation) (children : List Raw) : Raw :=
  match operation with
  | ⟨_,.winner role⟩ => rawWinner (forward.getD role 0)
  | ⟨_,.choice owner⟩ => rawChoice (forward.getD owner 0)
      (children.getD 0 (.var 0)) (children.getD 1 (.var 0))
  | ⟨_,.rename original⟩ => rawRename original (children.getD 0 (.var 0))

theorem fold_mapRoles (forward : List ℕ) (raw : Raw) :
    FullTermFold.fold (fun _ name => .var name) mapNode forward raw = mapRoles forward raw := by
  induction raw with
  | var name => rfl
  | @func n operation children ih =>
    cases operation <;> simp [FullTermFold.fold,mapNode,mapRoles,List.ofFn_succ,ih]

theorem mapNode_polyTime : ComputableInPolyTime
    (fun p : List ℕ × (Operation × List Raw) => mapNode p.1 p.2.1 p.2.2)
    (encPair arrayEncoding (encPair FullTermMachines.operationEncoding (encList FullTermMachines.termEncoding)))
    FullTermMachines.termEncoding := by
  let input := encPair arrayEncoding (encPair FullTermMachines.operationEncoding (encList FullTermMachines.termEncoding))
  have hforward : ComputableInPolyTime (fun p : List ℕ × (Operation × List Raw) => p.1) input arrayEncoding := by fun_prop
  have hop : ComputableInPolyTime (fun p : List ℕ × (Operation × List Raw) => p.2.1)
      input FullTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime (fun p : List ℕ × (Operation × List Raw) => p.2.2)
      input (encList FullTermMachines.termEncoding) := by fun_prop
  have hlabel := FullTermMachines.roleLabel_polyTime.comp hop
  have hlookup := arrayLookup_polyTime.comp (hforward.prod hlabel)
  have horiginal := FullTermMachines.forwardArray_polyTime.comp hop
  have hkind := FullTermMachines.operationKind_polyTime.comp hop
  have hzero := (listGetD (encA := FullTermMachines.termEncoding) (.var 0)).comp (hc.prod (const 0))
  have hone := (listGetD (encA := FullTermMachines.termEncoding) (.var 0)).comp (hc.prod (const 1))
  have hwinner := rawWinner_polyTime.comp hlookup
  have hchoice := rawChoice_polyTime.comp (hlookup.prod (hzero.prod hone))
  have hrename := rawRename_polyTime.comp (horiginal.prod hzero)
  let branch (kind : Fin 3) (p : List ℕ × (Operation × List Raw)) : Raw :=
    if kind=0 then rawWinner (p.1.getD (FullTermMachines.roleLabel p.2.1) 0)
    else if kind=1 then rawRename (FullTermMachines.forwardArray p.2.1) (p.2.2.getD 0 (.var 0))
    else rawChoice (p.1.getD (FullTermMachines.roleLabel p.2.1) 0)
      (p.2.2.getD 0 (.var 0)) (p.2.2.getD 1 (.var 0))
  have hb (kind : Fin 3) : ComputableInPolyTime (branch kind) input FullTermMachines.termEncoding := by
    fin_cases kind
    · exact hwinner
    · exact hrename
    · exact hchoice
  have h := hkind.finite_cases (branch := branch) hb
  convert h using 1
  funext p
  rcases p with ⟨forward,⟨⟨n,symbol⟩,children⟩⟩
  cases symbol <;> rfl

/-- Actual stored-array label transport has a native polynomial machine with
its concrete quadratic storage proof discharged. -/
theorem mapRoles_polyTime : ComputableInPolyTime
    (fun p : List ℕ × Raw => mapRoles p.1 p.2)
    (encPair arrayEncoding FullTermMachines.termEncoding) FullTermMachines.termEncoding := by
  have hleaf := FullTermMachines.var_polyTime.comp (snd arrayEncoding encNat)
  have h := FullTermFold.fold_polyTime (contextEncoding := arrayEncoding)
    (valueEncoding := FullTermMachines.termEncoding) (fun _ name => .var name) mapNode
    hleaf mapNode_polyTime 100 2
    (by intro forward raw; rw [fold_mapRoles]; exact encode_mapRoles_bound forward raw) (.var 0)
  convert h using 1
  funext p
  exact (fold_mapRoles p.1 p.2).symm

end KFOL.Complexity.CoreExtraction
