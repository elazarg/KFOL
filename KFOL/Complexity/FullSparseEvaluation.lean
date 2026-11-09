module
public import KFOL.Complexity.FullTermFoldRuntime
public import KFOL.Algorithms.FullTermCode.Validation
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
@[expose] public section
namespace KFOL.Complexity.FullSparseEvaluation
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
abbrev Value := List ℕ
abbrev valueEncoding := encList encNat
abbrev Context := List ℕ × List ℕ
abbrev contextEncoding := encPair (encList encNat) (encList encNat)

def leaf (context : Context) (name : ℕ) : Value :=
  let index := 2 * context.1.idxOf name
  [context.2.getD index 0, context.2.getD (index+1) 0]

def singletonB (owner : ℕ) (value : Value) : Bool :=
  !value.isEmpty && value.all (fun r => decide (r = owner))
def choice (owner : ℕ) (left right : Value) : Value :=
  if singletonB owner left || singletonB owner right then [owner] else left ++ right

def rename (array : List ℕ) (value : Value) : Value := value.map (fun role => array.getD role 0)

def node (_ : Context) (operation : Operation) (children : List Value) : Value :=
  match operation with
  | ⟨_,.winner role⟩ => [role]
  | ⟨_,.choice owner⟩ => choice owner (children.getD 0 [0]) (children.getD 1 [0])
  | ⟨_,.rename array⟩ => rename array (children.getD 0 [0])

def evaluate (context : Context) (tree : Raw) : Value := FullTermFold.fold leaf node context tree

theorem leaf_polyTime : ComputableInPolyTime (fun p : Context × ℕ => leaf p.1 p.2)
    (encPair contextEncoding encNat) valueEncoding := by
  have hnames : ComputableInPolyTime (fun p : Context × ℕ => p.1.1) (encPair contextEncoding encNat) (encList encNat) := by fun_prop
  have hvalues : ComputableInPolyTime (fun p : Context × ℕ => p.1.2) (encPair contextEncoding encNat) (encList encNat) := by fun_prop
  have hi := unary_mul' (const 2) (idxOfWithInput hnames (snd contextEncoding encNat))
  have hi' := unary_add.comp (hi.prod (const 1))
  have hfirst := (listGetD (encA := encNat) (encL := valueEncoding) 0).comp (hvalues.prod hi)
  have hsecond := (listGetD (encA := encNat) (encL := valueEncoding) 0).comp (hvalues.prod hi')
  exact cons' hfirst (cons' hsecond (const []))

theorem singleton_polyTime : ComputableInPolyTime (fun p : ℕ × Value => singletonB p.1 p.2)
    (encPair encNat valueEncoding) encBool := by
  have hvalue := snd encNat valueEncoding
  have hnonempty := bool_not.comp ((ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listIsEmpty (encA := encNat))).comp hvalue)
  have hr := snd (encPair encNat valueEncoding) encNat
  have ho : ComputableInPolyTime (fun p : (ℕ × Value) × ℕ => p.1.1) (encPair (encPair encNat valueEncoding) encNat) encNat := by fun_prop
  have hall := allWithInput (test := fun (p : ℕ × Value) r => decide (r = p.1)) hvalue (decide_eq' hr ho)
  exact bool_and' hnonempty hall

theorem choice_polyTime : ComputableInPolyTime (fun p : ℕ × (Value × Value) => choice p.1 p.2.1 p.2.2)
    (encPair encNat (encPair valueEncoding valueEncoding)) valueEncoding := by
  let input := encPair encNat (encPair valueEncoding valueEncoding)
  have ho := fst encNat (encPair valueEncoding valueEncoding)
  have hl : ComputableInPolyTime (fun p : ℕ × (Value × Value) => p.2.1) input valueEncoding := by fun_prop
  have hr : ComputableInPolyTime (fun p : ℕ × (Value × Value) => p.2.2) input valueEncoding := by fun_prop
  have htest := bool_or.comp (((singleton_polyTime.comp (ho.prod hl))).prod (singleton_polyTime.comp (ho.prod hr)))
  exact htest.ite (cons' ho (const [])) (listAppend' hl hr)

theorem lookup_polyTime : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.getD p.2 0)
    (encPair valueEncoding encNat) encNat :=
  .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encA := encNat) (encL := valueEncoding) 0
    (ComputableTidilyInPolyTime.fst _ _) (ComputableTidilyInPolyTime.snd _ _))

theorem rename_polyTime : ComputableInPolyTime (fun p : List ℕ × Value => rename p.1 p.2)
    (encPair valueEncoding valueEncoding) valueEncoding := by
  have harray : ComputableInPolyTime (fun p : (List ℕ × Value) × ℕ => p.1.1)
      (encPair (encPair valueEncoding valueEncoding) encNat) valueEncoding := by fun_prop
  exact mapWithInput (f := fun (p : List ℕ × Value) role => p.1.getD role 0) (snd _ _)
    (lookup_polyTime.comp (harray.prod (snd _ _)))

theorem node_polyTime : ComputableInPolyTime (fun p : Context × (Operation × List Value) => node p.1 p.2.1 p.2.2)
    (encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))) valueEncoding := by
  let input := encPair contextEncoding (encPair FullTermMachines.operationEncoding (encList valueEncoding))
  have hop : ComputableInPolyTime (fun p : Context × (Operation × List Value) => p.2.1) input FullTermMachines.operationEncoding := by fun_prop
  have hchildren : ComputableInPolyTime (fun p : Context × (Operation × List Value) => p.2.2) input (encList valueEncoding) := by fun_prop
  have hleft := (listGetD (encA := valueEncoding) (encL := encList valueEncoding) [0]).comp (hchildren.prod (const 0))
  have hright := (listGetD (encA := valueEncoding) (encL := encList valueEncoding) [0]).comp (hchildren.prod (const 1))
  have hrole := FullTermMachines.roleLabel_polyTime.comp hop
  have hwinner := cons' hrole (const [])
  have hchoice := choice_polyTime.comp (hrole.prod (hleft.prod hright))
  have hrename := rename_polyTime.comp ((FullTermMachines.forwardArray_polyTime.comp hop).prod hleft)
  have hk := FullTermMachines.operationKind_polyTime.comp hop
  have h := (decide_eq' hk (const (0:Fin 3))).ite hwinner ((decide_eq' hk (const (1:Fin 3))).ite hrename hchoice)
  convert h using 1
  funext p
  rcases p with ⟨context,⟨n,symbol⟩,children⟩
  cases symbol <;> rfl
end KFOL.Complexity.FullSparseEvaluation
