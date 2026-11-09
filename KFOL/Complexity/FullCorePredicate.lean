module
public import KFOL.Complexity.FullTermFoldRuntime
public import KFOL.Algorithms.FullTermCode.View
@[expose] public section
namespace KFOL.Complexity.FullCorePredicate
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
private def leaf (_ : Unit) (_ : ℕ) : Bool := true
private def node (_ : Unit) (operation : Operation) (children : List Bool) : Bool :=
  decide (FullTermMachines.operationKind operation = 2) && children.all id

def check : Raw → Bool
  | .var _ => true
  | .func (.winner _) _ => false
  | .func (.choice _) children => check (children 0) && check (children 1)
  | .func (.rename _) _ => false
private theorem fold_check (tree : Raw) : FullTermFold.fold leaf node () tree = check tree := by
  induction tree with
  | var => rfl
  | @func n symbol children ih =>
    cases symbol <;> simp [FullTermFold.fold, node, check, ih, FullTermMachines.operationKind, List.ofFn_succ]
private theorem node_polyTime : ComputableInPolyTime
    (fun p : Unit × (Operation × List Bool) => node p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair FullTermMachines.operationEncoding (encList encBool))) encBool := by
  let input := encPair encUnit (encPair FullTermMachines.operationEncoding (encList encBool))
  have hop : ComputableInPolyTime (fun p : Unit × (Operation × List Bool) => p.2.1) input FullTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime (fun p : Unit × (Operation × List Bool) => p.2.2) input (encList encBool) := by fun_prop
  have hall := allWithInput (test := fun (_ : Unit × (Operation × List Bool)) b => b) hc (snd input encBool)
  exact bool_and' (decide_eq' (FullTermMachines.operationKind_polyTime.comp hop) (const (2:Fin 3))) hall

theorem check_polyTime : ComputableInPolyTime check FullTermMachines.termEncoding encBool := by
  have hf := FullTermFold.fold_polyTime (contextEncoding := encUnit) (valueEncoding := encBool)
    leaf node (const true) node_polyTime 1 0 (by intros; simp [encBool_apply]) false
  have h := hf.comp ((const ()).prod (id' (encIn := FullTermMachines.termEncoding)))
  convert h using 1
  funext tree
  exact (fold_check tree).symm

theorem check_view_iff {K : ℕ} (term : KFOL.Term (Fin K) ℕ) : check (view term) = true ↔ term.IsCore := by
  induction term <;> simp_all [view,check,KFOL.Term.IsCore]
end KFOL.Complexity.FullCorePredicate
