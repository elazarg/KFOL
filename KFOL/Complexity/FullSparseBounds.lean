module
public import KFOL.Complexity.FullSparseEvaluation
public import Mathlib.Data.List.GetD
public import KFOL.Complexity.FullTermSize
@[expose] public section
namespace KFOL.Complexity.FullSparseEvaluation
open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FullTermCode
open FullTermSize

@[simp] theorem evaluate_var (context : Context) (j : ℕ) : evaluate context (.var j) = leaf context j := rfl
@[simp] theorem evaluate_winner (context : Context) (role : ℕ) (children : Fin 0 → Raw) :
    evaluate context (.func (.winner role) children) = [role] := rfl
@[simp] theorem evaluate_choice (context : Context) (owner : ℕ) (children : Fin 2 → Raw) :
    evaluate context (.func (.choice owner) children) =
      choice owner (evaluate context (children 0)) (evaluate context (children 1)) := by
  simp [evaluate, FullTermFold.fold, node, List.ofFn_succ]
@[simp] theorem evaluate_rename (context : Context) (array : List ℕ) (children : Fin 1 → Raw) :
    evaluate context (.func (.rename array) children) = rename array (evaluate context (children 0)) := by
  simp [evaluate, FullTermFold.fold, node, List.ofFn_succ]

theorem length_evaluate (context : Context) (tree : Raw) : (evaluate context tree).length ≤ 2 * nodes tree := by
  induction tree with
  | var j => simp [leaf, nodes]
  | @func n symbol children ih =>
    cases symbol with
    | winner role => simp [nodes]
    | choice owner =>
      rw [evaluate_choice]
      unfold choice
      split
      · simp only [List.length_singleton,nodes]
        omega
      · have hl := ih 0
        have hr := ih 1
        simp only [List.length_append, nodes]
        omega
    | rename array =>
      rw [evaluate_rename]
      have hc := ih 0
      simp only [rename, List.length_map, nodes]
      omega

theorem getD_mem_or_zero (values : List ℕ) (index : ℕ) : values.getD index 0 = 0 ∨ values.getD index 0 ∈ values := by
  by_cases hi : index < values.length
  · right
    rw [List.getD_eq_getElem values 0 hi]
    exact List.getElem_mem hi
  · left
    exact List.getD_eq_default _ _ (Nat.le_of_not_gt hi)

theorem mem_evaluate (context : Context) (tree : Raw) (role : ℕ) (hrole : role ∈ evaluate context tree) :
    role = 0 ∨ role ∈ context.2 ∨ role ∈ labels tree := by
  induction tree with
  | var j =>
    simp only [evaluate_var, leaf, List.mem_cons, List.not_mem_nil, or_false] at hrole
    rcases hrole with rfl | rfl
    · exact (getD_mem_or_zero context.2 _).imp_right Or.inl
    · exact (getD_mem_or_zero context.2 _).imp_right Or.inl
  | @func n symbol children ih =>
    cases symbol with
    | winner stored =>
      simp only [evaluate_winner, List.mem_singleton] at hrole
      exact Or.inr (Or.inr (by simp [labels, hrole]))
    | choice owner =>
      rw [evaluate_choice] at hrole
      unfold choice at hrole
      split at hrole
      · simp only [List.mem_singleton] at hrole
        exact Or.inr (Or.inr (by simp [labels, hrole]))
      · rcases List.mem_append.mp hrole with hl | hr
        · rcases ih 0 hl with he | hc | hs
          · exact Or.inl he
          · exact Or.inr (Or.inl hc)
          · exact Or.inr (Or.inr (by simp [labels, hs]))
        · rcases ih 1 hr with he | hc | hs
          · exact Or.inl he
          · exact Or.inr (Or.inl hc)
          · exact Or.inr (Or.inr (by simp [labels, hs]))
    | rename array =>
      rw [evaluate_rename] at hrole
      obtain ⟨input, _, rfl⟩ := List.mem_map.mp hrole
      rcases getD_mem_or_zero array input with he | hm
      · exact Or.inl he
      · exact Or.inr (Or.inr (List.mem_append_left _ hm))

private theorem label_weight_le (values : List ℕ) (label : ℕ) (hlabel : label ∈ values) :
    2 * (encNat label).length + 1 ≤ weight values := by
  rw [weight, length_encList]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨label,hlabel,rfl⟩)

private theorem sum_weight_le (values : List ℕ) (bound : ℕ)
    (h : ∀ label ∈ values, 2 * (encNat label).length + 1 ≤ bound) : weight values ≤ values.length * bound := by
  induction values with
  | nil => simp
  | cons label rest ih =>
    have hl := h label (by simp)
    have hr := ih (fun r hm => h r (by simp [hm]))
    simp only [weight_cons, List.length_cons, encNat_apply] at hl hr ⊢
    nlinarith

/-- Every duplicate output role is charged; no finite carrier enumeration or
maximum binary role label enters this quadratic complete annotation bound. -/
theorem evaluate_weight_le (context : Context) (tree : Raw) :
    weight (evaluate context tree) ≤ 2 * ((contextEncoding context).length + (encode tree).length + 1)^2 := by
  let budget := (contextEncoding context).length + (encode tree).length + 1
  have hall : ∀ role ∈ evaluate context tree, 2 * (encNat role).length + 1 ≤ budget := by
    intro role hrole
    have hm := mem_evaluate context tree role hrole
    have hw : 2 * (encNat role).length + 1 ≤ weight (0 :: (context.2 ++ labels tree)) := by
      apply label_weight_le
      simp only [List.mem_cons, List.mem_append]
      exact hm
    have hp := labels_weight_le_encode tree
    rw [weight_cons, weight_append] at hw
    change 2 * (encNat role).length + 1 ≤ 1 + (weight context.2 + weight (labels tree)) at hw
    have hc : weight context.2 ≤ (contextEncoding context).length := by
      simp only [weight, contextEncoding, length_encPair]
      omega
    change 2 * (encNat role).length + 1 ≤ (contextEncoding context).length + (encode tree).length + 1
    omega
  have hs := sum_weight_le (evaluate context tree) budget hall
  have hn := length_evaluate context tree
  have hc := nodes_le_encode tree
  have hbudget : (encode tree).length ≤ budget := by
    change (encode tree).length ≤ (contextEncoding context).length + (encode tree).length + 1
    omega
  change weight (evaluate context tree) ≤ 2 * budget^2
  nlinarith

theorem evaluate_polyTime : ComputableInPolyTime (fun p : Context × Raw => evaluate p.1 p.2)
    (encPair contextEncoding FullTermMachines.termEncoding) valueEncoding :=
  FullTermFold.fold_polyTime leaf node leaf_polyTime node_polyTime 2 2 evaluate_weight_le []
end KFOL.Complexity.FullSparseEvaluation
