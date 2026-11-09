module
public import KFOL.Complexity.FiniteFoldMachine
public import Mathlib.Algebra.Order.BigOperators.Group.List
/-! # Polynomial storage for cached original-tree evaluation -/

@[expose] public section
namespace KFOL.Complexity.FiniteFoldMachine
open Turing.MultiTapeTM
open KFOL.FiniteTermCode
variable {σ : ℕ → Type} [Fintype (Operation σ)]
variable {Context Value : Type}
variable {contextEncoding : Context ↪ List Bool} {valueEncoding : Value ↪ List Bool}

private theorem length_le_weight {α : Type} (weight : α → ℕ) (values : List α)
    (h : ∀ value ∈ values, 1 ≤ weight value) : values.length ≤ (values.map weight).sum := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    have hv := h value (List.mem_cons_self ..)
    have hs := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

private theorem encoded_list_bound {α : Type} (encoding : α ↪ List Bool) (values : List α)
    (bound : ℕ) (h : ∀ value ∈ values, (encoding value).length ≤ bound) :
    (encList encoding values).length ≤ values.length * (2 * bound + 1) := by
  induction values with
  | nil => simp
  | cons value values ih =>
    have hv := h value (List.mem_cons_self ..)
    have hs := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [encList_cons, List.length_append, length_frame, List.length_cons]
    nlinarith

private theorem frameWeight_pos (frame : Frame σ Value) : 1 ≤ frameWeight frame := by
  unfold frameWeight
  omega

private theorem cache_length_le (frame : Frame σ Value) {cache : Cached σ Value} (hc : cache ∈ frame.2) :
    (encode σ cache.1).length ≤ frameWeight frame := by
  have hm : (encode σ cache.1).length ∈ frame.2.map (fun cache => (encode σ cache.1).length) :=
    List.mem_map.mpr ⟨cache, hc, rfl⟩
  have hs := List.le_sum_of_mem hm
  unfold frameWeight
  omega

/-- Every intermediate machine state has polynomial encoded size from its
original input budget and the mathematical annotation bound. -/
theorem encoded_state_bound (leaf : Context → ℕ → Value)
    (node : Context → Operation σ → List Value → Value) (context : Context)
    (state : State σ Value) (c degree budget : ℕ)
    (hfold : ∀ term : Equational.Term σ ℕ,
      (valueEncoding (fold leaf node context term)).length ≤
        c * ((contextEncoding context).length + (encode σ term).length + 1)^degree)
    (hvalid : stateValid leaf node context state)
    (hbudget : (contextEncoding context).length + stateWeight state ≤ budget) :
    (stateEncoding valueEncoding state).length ≤
      32 * (budget + 1)^3 * (c * (budget + 1)^degree + 1) := by
  let bound := c * (budget + 1)^degree
  have hcache : ∀ cache : Cached σ Value, cachedValid leaf node context cache →
      (contextEncoding context).length + (encode σ cache.1).length ≤ budget →
      (cachedEncoding valueEncoding cache).length ≤ 2 * budget + 1 + bound := by
    intro cache hv hb
    have hs := hfold cache.1
    have hm : ((contextEncoding context).length + (encode σ cache.1).length + 1)^degree ≤
        (budget + 1)^degree := Nat.pow_le_pow_left (by omega) degree
    have hc : (valueEncoding cache.2).length ≤ bound := by
      rw [hv]
      exact hs.trans (Nat.mul_le_mul_left c hm)
    simp only [cachedEncoding, length_encPair]
    change 2 * (encode σ cache.1).length + 1 + (valueEncoding cache.2).length ≤ _
    omega
  cases state with
  | none => simp [stateEncoding]
  | some data =>
    rcases data with ⟨stack, focus, rest⟩
    have hstate : (contextEncoding context).length +
        (stack.map frameWeight).sum + focus.elim 0 (fun cache => (encode σ cache.1).length) +
        rest.length ≤ budget := by
      simpa only [stateWeight, Option.elim_some, dataWeight, Nat.add_assoc] using hbudget
    have hframes : ∀ frame ∈ stack, frameWeight frame ≤ (stack.map frameWeight).sum := by
      intro frame hf
      exact List.le_sum_of_mem (List.mem_map.mpr ⟨frame, hf, rfl⟩)
    have hstackLength : stack.length ≤ budget :=
      (length_le_weight frameWeight stack (fun frame _ => frameWeight_pos frame)).trans (by omega)
    have hframeEncoding : ∀ frame ∈ stack,
        (frameEncoding valueEncoding frame).length ≤
          2 * budget + 1 + budget * (2 * (2 * budget + 1 + bound) + 1) := by
      intro frame hf
      have hw := hframes frame hf
      have hchildren : frame.2.length ≤ budget := by
        have hl := length_le_weight (fun cache : Cached σ Value => (encode σ cache.1).length)
          frame.2 (fun cache _ => length_encode_pos cache.1)
        have hp : (frame.2.map (fun cache => (encode σ cache.1).length)).sum ≤ frameWeight frame := by
          unfold frameWeight
          omega
        omega
      have hc : ∀ cache ∈ frame.2, (cachedEncoding valueEncoding cache).length ≤ 2 * budget + 1 + bound := by
        intro cache hm
        apply hcache cache (hvalid.1 frame hf cache hm)
        have ht := cache_length_le frame hm
        omega
      have hl := encoded_list_bound (cachedEncoding valueEncoding) frame.2 _ hc
      have ho : (encodeOperation σ frame.1).length ≤ budget := by
        have hp : (encodeOperation σ frame.1).length ≤ frameWeight frame := by
          simp only [frameWeight, Words.delimit_length]
          omega
        omega
      have hl' := hl.trans (Nat.mul_le_mul_right _ hchildren)
      simp only [frameEncoding, length_encPair]
      change 2 * (encodeOperation σ frame.1).length + 1 +
        (encList (cachedEncoding valueEncoding) frame.2).length ≤ _
      omega
    have hs := encoded_list_bound (frameEncoding valueEncoding) stack _ hframeEncoding
    have hs' := hs.trans (Nat.mul_le_mul_right _ hstackLength)
    have hfocus : (encOption (cachedEncoding valueEncoding) focus).length ≤ 2 * budget + 2 + bound := by
      cases focus with
      | none => simp
      | some cache =>
        simp only [Option.elim_some] at hstate
        have hc := hcache cache (hvalid.2 cache rfl) (by omega)
        simp only [encOption_some, List.length_cons]
        omega
    simp only [stateEncoding, encOption_some, List.length_cons, dataEncoding, length_encPair]
    change (2 * (encList (frameEncoding valueEncoding) stack).length + 1 +
      (2 * (encOption (cachedEncoding valueEncoding) focus).length + 1 + rest.length)) + 1 ≤
      32 * (budget + 1)^3 * (bound + 1)
    have hr : rest.length ≤ budget := by omega
    nlinarith [Nat.zero_le (budget^3 * bound), Nat.zero_le (budget^2 * bound),
      Nat.zero_le (budget * bound), Nat.zero_le (budget^3), Nat.zero_le (budget^2)]
end KFOL.Complexity.FiniteFoldMachine
