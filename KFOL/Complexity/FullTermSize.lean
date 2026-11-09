module
public import KFOL.Complexity.FullTermMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
public import Mathlib.Tactic.Linarith
@[expose] public section
namespace KFOL.Complexity.FullTermSize
open KFOL.FullTermCode Turing.MultiTapeTM

/-- All original binary names and every stored array entry, retaining repeats. -/
def labels : Raw → List ℕ
  | .var j => [j]
  | .func (.winner role) _ => [role]
  | .func (.choice owner) children => owner :: (labels (children 0) ++ labels (children 1))
  | .func (.rename array) children => array ++ labels (children 0)

def nodes : Raw → ℕ
  | .var _ => 1
  | .func (.winner _) _ => 1
  | .func (.choice _) children => 1 + nodes (children 0) + nodes (children 1)
  | .func (.rename _) children => 1 + nodes (children 0)

def weight (values : List ℕ) : ℕ := (encList encNat values).length
@[simp] theorem weight_nil : weight [] = 0 := rfl
@[simp] theorem weight_cons (j : ℕ) (values : List ℕ) : weight (j :: values) = 2*j.bits.length+1+weight values := by
  simp only [weight, length_encList, List.map_cons, List.sum_cons, encNat_apply]
@[simp] theorem weight_append (xs ys : List ℕ) : weight (xs ++ ys) = weight xs + weight ys := by
  simp only [weight, length_encList, List.map_append, List.sum_append]

theorem weight_le_dictionary (values : List ℕ) : weight values ≤ (Algorithms.LabelDictionary.encode values).length := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [weight_cons]
    simp only [Algorithms.LabelDictionary.encode, List.map_cons, List.flatten_cons, List.length_append,
      Words.delimit_length, Words.BinaryNatCode.encode] at ih ⊢
    omega

theorem labels_weight_le_encode (tree : Raw) : weight (labels tree) ≤ (encode tree).length := by
  induction tree with
  | var j => simp [labels, encode_var, Words.delimit_length, Words.BinaryNatCode.encode]
  | @func n symbol children ih =>
    cases symbol with
    | winner role =>
      simp only [labels, weight_cons, weight_nil, encode_func, encodeOperation, List.ofFn_zero, List.flatten_nil,
        List.length_cons, List.length_append, Words.delimit_length, Words.BinaryNatCode.encode]
      omega
    | choice owner =>
      have hl := ih 0
      have hr := ih 1
      simp only [labels, weight_cons, weight_append, encode_func, encodeOperation, List.ofFn_succ,
        List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
        List.length_append, Words.delimit_length, Words.BinaryNatCode.encode]
      simp only [show (Fin.succ (0 : Fin 1) : Fin 2) = 1 from rfl]
      nlinarith
    | rename array =>
      have hc := ih 0
      have hw := weight_le_dictionary array
      simp only [labels, weight_append, encode_func, encodeOperation, List.ofFn_succ,
        List.ofFn_zero, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_cons,
        List.length_append, Words.delimit_length]
      nlinarith

theorem nodes_le_encode (tree : Raw) : nodes tree ≤ (encode tree).length := by
  induction tree with
  | var j => simp [nodes, encode_var]
  | @func n symbol children ih =>
    cases symbol with
    | winner role => simp [nodes, encode_func]
    | choice owner =>
      have hl := ih 0
      have hr := ih 1
      simp only [nodes, encode_func, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.length_cons, List.length_append]
      simp only [show (Fin.succ (0 : Fin 1) : Fin 2) = 1 from rfl]
      omega
    | rename array =>
      have hc := ih 0
      simp only [nodes, encode_func, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
        List.flatten_nil, List.append_nil, List.length_cons, List.length_append]
      omega

theorem label_bytes_le_encode (tree : Raw) (j : ℕ) (hj : j ∈ labels tree) : (encNat j).length ≤ (encode tree).length :=
  (SizedListEncoding.length_elem_le (encA := encNat) (encL := encList encNat) (labels tree) j hj).trans
    (labels_weight_le_encode tree)

theorem length_labels_le_encode (tree : Raw) : (labels tree).length ≤ (encode tree).length :=
  (length_le_length_encList encNat _).trans (labels_weight_le_encode tree)
end KFOL.Complexity.FullTermSize
