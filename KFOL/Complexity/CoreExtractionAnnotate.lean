module

public import KFOL.Complexity.CoreExtractionMap
public import KFOL.Complexity.CoreExtractionStorage

/-! # Native full original-tree annotation and checked core extraction -/

@[expose] public section

namespace KFOL.Complexity.CoreExtraction

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode

def fallbackAnnotation : Annotation := (.var 0,false,[])

def annotateNode (_ : Unit) (operation : Operation) (children : List Annotation) : Annotation :=
  match operation with
  | ⟨_,.winner role⟩ => (rawWinner role,false,[])
  | ⟨_,.choice owner⟩ =>
      let left := children.getD 0 fallbackAnnotation
      let right := children.getD 1 fallbackAnnotation
      (rawChoice owner left.1 right.1,left.2.1 && right.2.1,left.2.2 ++ right.2.2)
  | ⟨_,.rename forward⟩ =>
      let child := children.getD 0 fallbackAnnotation
      (mapRoles forward child.1,child.2.1,child.2.2.map (Action.compose (some forward)))

theorem fold_annotate (raw : Raw) :
    FullTermFold.fold (fun _ name => (.var name,true,[none])) annotateNode () raw = annotate raw := by
  induction raw with
  | var name => rfl
  | @func n operation children ih =>
    cases operation <;> simp [FullTermFold.fold,annotateNode,annotate,List.ofFn_succ,ih]

theorem annotateNode_polyTime : ComputableInPolyTime
    (fun p : Unit × (Operation × List Annotation) => annotateNode p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair FullTermMachines.operationEncoding (encList annotationEncoding))) annotationEncoding := by
  let input := encPair encUnit (encPair FullTermMachines.operationEncoding (encList annotationEncoding))
  let tailEncoding := encPair encBool (encList actionEncoding)
  have hop : ComputableInPolyTime (fun p : Unit × (Operation × List Annotation) => p.2.1)
      input FullTermMachines.operationEncoding := by fun_prop
  have hchildren : ComputableInPolyTime (fun p : Unit × (Operation × List Annotation) => p.2.2)
      input (encList annotationEncoding) := by fun_prop
  have hl := (listGetD (encA := annotationEncoding) fallbackAnnotation).comp (hchildren.prod (const 0))
  have hr := (listGetD (encA := annotationEncoding) fallbackAnnotation).comp (hchildren.prod (const 1))
  have hlcore := (fst FullTermMachines.termEncoding tailEncoding).comp hl
  have hrcore := (fst FullTermMachines.termEncoding tailEncoding).comp hr
  have hlflag := (fst encBool (encList actionEncoding)).comp ((snd FullTermMachines.termEncoding tailEncoding).comp hl)
  have hrflag := (fst encBool (encList actionEncoding)).comp ((snd FullTermMachines.termEncoding tailEncoding).comp hr)
  have hlactions := (snd encBool (encList actionEncoding)).comp ((snd FullTermMachines.termEncoding tailEncoding).comp hl)
  have hractions := (snd encBool (encList actionEncoding)).comp ((snd FullTermMachines.termEncoding tailEncoding).comp hr)
  have hrole := FullTermMachines.roleLabel_polyTime.comp hop
  have hforward := FullTermMachines.forwardArray_polyTime.comp hop
  have hkind := FullTermMachines.operationKind_polyTime.comp hop
  have hwinner : ComputableInPolyTime
      (fun p : Unit × (Operation × List Annotation) =>
        (rawWinner (FullTermMachines.roleLabel p.2.1),false,([] : List Action))) input annotationEncoding :=
    (rawWinner_polyTime.comp hrole).prod ((const false).prod (const []))
  have hchoice := (rawChoice_polyTime.comp (hrole.prod (hlcore.prod hrcore))).prod
    ((bool_and' hlflag hrflag).prod (listAppend' hlactions hractions))
  have hforward' : ComputableInPolyTime
      (fun p : (Unit × (Operation × List Annotation)) × Action =>
        some (FullTermMachines.forwardArray p.1.2.1)) (encPair input actionEncoding) actionEncoding :=
    (optionSome arrayEncoding).comp (hforward.comp (fst input actionEncoding))
  have haction := snd input actionEncoding
  have hcompose := compose_polyTime.comp (hforward'.prod haction)
  have hmap := mapWithInput
    (f := fun (p : Unit × (Operation × List Annotation)) action =>
      Action.compose (some (FullTermMachines.forwardArray p.2.1)) action)
    hlactions hcompose
  have hrename := (mapRoles_polyTime.comp (hforward.prod hlcore)).prod (hlflag.prod hmap)
  let branch (kind : Fin 3) (p : Unit × (Operation × List Annotation)) : Annotation :=
    if kind=0 then (rawWinner (FullTermMachines.roleLabel p.2.1),false,[])
    else if kind=1 then
      let child := p.2.2.getD 0 fallbackAnnotation
      (mapRoles (FullTermMachines.forwardArray p.2.1) child.1,child.2.1,
        child.2.2.map (Action.compose (some (FullTermMachines.forwardArray p.2.1))))
    else
      let left := p.2.2.getD 0 fallbackAnnotation
      let right := p.2.2.getD 1 fallbackAnnotation
      (rawChoice (FullTermMachines.roleLabel p.2.1) left.1 right.1,
        left.2.1 && right.2.1,left.2.2 ++ right.2.2)
  have hb (kind : Fin 3) : ComputableInPolyTime (branch kind) input annotationEncoding := by
    fin_cases kind
    · exact hwinner
    · exact hrename
    · exact hchoice
  have h := hkind.finite_cases (branch := branch) hb
  convert h using 1
  funext p
  rcases p with ⟨contextUnit,⟨⟨n,symbol⟩,children⟩⟩
  cases contextUnit
  cases symbol <;> rfl

/-- The actual cached full-tree traversal is polynomial, with every repeated
occurrence and explicit permutation-array byte charged. Its storage premise
is discharged by the proved original-byte cubic bound. -/
theorem annotate_polyTime : ComputableInPolyTime annotate FullTermMachines.termEncoding annotationEncoding := by
  have hname := snd encUnit encNat
  have hleaf : ComputableInPolyTime
      (fun p : Unit × ℕ => ((.var p.2 : Raw),true,([none] : List Action)))
      (encPair encUnit encNat) annotationEncoding :=
    (FullTermMachines.var_polyTime.comp hname).prod ((const true).prod (const [none]))
  have h := FullTermFold.fold_polyTime (contextEncoding := encUnit) (valueEncoding := annotationEncoding)
    (fun _ name => (.var name,true,[none])) annotateNode hleaf annotateNode_polyTime 100 3
    (by
      intro contextUnit raw
      rw [fold_annotate]
      exact (annotation_encoding_bound raw).trans
        (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 3))) fallbackAnnotation
  have hin : ComputableInPolyTime (fun raw : Raw => ((),raw)) FullTermMachines.termEncoding
      (encPair encUnit FullTermMachines.termEncoding) :=
    (const ()).prod (id' (encIn := FullTermMachines.termEncoding))
  have hc := h.comp hin
  convert hc using 1
  funext raw
  exact (fold_annotate raw).symm

/-- The original raw checked extraction, including failure and its complete
output core code, has an actual native deterministic polynomial machine. -/
theorem extractRaw_polyTime : ComputableInPolyTime extractRaw FullTermMachines.termEncoding
    (encOption FullTermMachines.termEncoding) := by
  have hcore := (fst FullTermMachines.termEncoding (encPair encBool (encList actionEncoding))).comp annotate_polyTime
  have htail := (snd FullTermMachines.termEncoding (encPair encBool (encList actionEncoding))).comp annotate_polyTime
  have hflag := (fst encBool (encList actionEncoding)).comp htail
  have hactions := (snd encBool (encList actionEncoding)).comp htail
  have htest := isIdentity_polyTime.comp (snd FullTermMachines.termEncoding actionEncoding)
  have hall := allWithInput (test := fun (_ : Raw) action => Action.isIdentity action) hactions htest
  have h := (bool_and' hflag hall).ite ((optionSome FullTermMachines.termEncoding).comp hcore) (const none)
  exact h

end KFOL.Complexity.CoreExtraction
