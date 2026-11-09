module
public import KFOL.Complexity.FullTermSize
public import KFOL.Complexity.FullTermFoldRuntime
@[expose] public section
namespace KFOL.Complexity.FullTermSize
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
private def leaf (_ : Unit) (j : ℕ) : List ℕ := [j]
private def node (_ : Unit) (operation : Operation) (children : List (List ℕ)) : List ℕ :=
  if FullTermMachines.operationKind operation = 1 then FullTermMachines.forwardArray operation ++ children.flatten
  else FullTermMachines.roleLabel operation :: children.flatten
private theorem fold_labels (tree : Raw) : FullTermFold.fold leaf node () tree = labels tree := by
  induction tree with
  | var => rfl
  | @func n symbol children ih =>
    cases symbol <;> simp [FullTermFold.fold, node, labels, ih, FullTermMachines.operationKind,
      FullTermMachines.forwardArray, FullTermMachines.roleLabel, List.ofFn_succ]
private theorem leaf_polyTime : ComputableInPolyTime (fun p : Unit × ℕ => leaf p.1 p.2)
    (encPair encUnit encNat) (encList encNat) := cons' (snd _ _) (const [])
private theorem node_polyTime : ComputableInPolyTime
    (fun p : Unit × (Operation × List (List ℕ)) => node p.1 p.2.1 p.2.2)
    (encPair encUnit (encPair FullTermMachines.operationEncoding (encList (encList encNat)))) (encList encNat) := by
  let input := encPair encUnit (encPair FullTermMachines.operationEncoding (encList (encList encNat)))
  have hop : ComputableInPolyTime (fun p : Unit × (Operation × List (List ℕ)) => p.2.1) input FullTermMachines.operationEncoding := by fun_prop
  have hc : ComputableInPolyTime (fun p : Unit × (Operation × List (List ℕ)) => p.2.2) input (encList (encList encNat)) := by fun_prop
  have hf := flatMapWithInput (f := fun (_ : Unit × (Operation × List (List ℕ))) (xs : List ℕ) => xs) hc
    (snd input (encList encNat))
  have ha := FullTermMachines.forwardArray_polyTime.comp hop
  have hr := FullTermMachines.roleLabel_polyTime.comp hop
  have ht := decide_eq' (FullTermMachines.operationKind_polyTime.comp hop) (const (1:Fin 3))
  have h := ht.ite (listAppend' ha hf) (cons' hr hf)
  convert h using 1
  funext p
  simp only [node, Function.comp_def, decide_eq_true_eq, List.flatMap_id']

theorem labels_polyTime : ComputableInPolyTime labels FullTermMachines.termEncoding (encList encNat) := by
  have hf := FullTermFold.fold_polyTime (contextEncoding := encUnit) (valueEncoding := encList encNat)
    leaf node leaf_polyTime node_polyTime 1 1 (by
      intro context tree
      cases context
      rw [fold_labels]
      have h := labels_weight_le_encode tree
      change ((encList encNat) (labels tree)).length ≤ _ at h
      simp only [Nat.one_mul, pow_one]
      omega) []
  have h := hf.comp ((const ()).prod (id' (encIn := FullTermMachines.termEncoding)))
  convert h using 1
  funext tree
  exact (fold_labels tree).symm
end KFOL.Complexity.FullTermSize
