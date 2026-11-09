module

public import KFOL.Algorithms.FiniteTermCode
public import KFOL.Complexity.Dictionary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-! # Native constructors for a fixed finite dependent signature

Each constructor preserves the generic original prefix format. The alphabet
and its maximum arity are fixed parameters; no uniform-signature bound is claimed.
-/

@[expose] public section

namespace KFOL.Complexity.FiniteTermMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

variable {σ : ℕ → Type} [Fintype (Operation σ)]

noncomputable def termEncoding : Equational.Term σ ℕ ↪ List Bool :=
  ⟨encode σ, encode_injective⟩

noncomputable def operationEncoding : Operation σ ↪ List Bool :=
  ⟨encodeOperation σ, fun p q h => by
    have he := congrArg (decodeOperation σ) h
    simpa only [decodeOperation_encodeOperation, Option.some.injEq] using he⟩

@[fun_prop] theorem encode_polyTime : ComputableInPolyTime
    (encode σ) termEncoding encBits := .of_eq (fun _ => rfl)

@[fun_prop] theorem var_polyTime : ComputableInPolyTime
    (fun j : ℕ => (.var j : Equational.Term σ ℕ)) encNat termEncoding := by
  have h := bitsCons (const false) (Framing.delimit_polyTime.comp Dictionary.encode_polyTime)
  exact h.of_enc_eq (fun _ => rfl)

/-- A fixed operation accepts a list of children, filling missing children with
variable zero and ignoring surplus children. The parser separately checks arity. -/
noncomputable def construct (operation : Operation σ) (children : List (Equational.Term σ ℕ)) :
    Equational.Term σ ℕ := .func operation.2 (fun i => children.getD i.val (.var 0))

@[fun_prop] theorem construct_fixed_polyTime (operation : Operation σ) :
    ComputableInPolyTime (construct operation) (encList termEncoding) termEncoding := by
  have hchild : ∀ i : Fin operation.1, ComputableInPolyTime
      (fun children : List (Equational.Term σ ℕ) => encode σ (children.getD i.val (.var 0)))
      (encList termEncoding) encBits := by
    intro i
    exact encode_polyTime.comp ((listGetD (encA := termEncoding) (.var 0 : Equational.Term σ ℕ)).comp (id'.prod (const i.val)))
  have hchildren := ComputableInPolyTime.ofFn hchild
  have hword := bitsCons (const true)
    (bitsAppend (const (Words.delimit (encodeOperation σ operation))) (bitsFlatten hchildren))
  exact hword.of_enc_eq (fun _ => rfl)

/-- Operation lookup is a native finite case distinction, charging the stored
operation code and complete original child list. -/
@[fun_prop] theorem construct_polyTime : ComputableInPolyTime
    (fun p : Operation σ × List (Equational.Term σ ℕ) => construct p.1 p.2)
    (encPair operationEncoding (encList termEncoding)) termEncoding := by
  exact (fst operationEncoding (encList termEncoding)).finite_cases
    (fun operation => (construct_fixed_polyTime operation).comp (snd _ _))

omit [Fintype (Operation σ)] in
/-- Every original function node is the arity-correct specialization. -/
theorem construct_ofFn {n : ℕ} (function : σ n) (children : Fin n → Equational.Term σ ℕ) :
    construct (⟨n, function⟩ : Operation σ) (List.ofFn children) = .func function children := by
  unfold construct
  congr 1
  funext i
  simp

/-- Complete strict operation decoding is membership in the fixed finite
canonical code alphabet, so malformed large indices never become loop clocks. -/
theorem decodeOperation_polyTime : ComputableInPolyTime
    (decodeOperation σ) encBits (encOption operationEncoding) := by
  classical
  let alphabet : List (Operation σ) := Finset.univ.toList
  have hmem : ∀ operation, operation ∈ alphabet := by simp [alphabet]
  have hflag : ComputableInPolyTime (fun word : List Bool =>
      alphabet.any (fun operation => decide (word = encodeOperation σ operation))) encBits encBool := by
    have h := anyWithInput (test := fun (word : List Bool) (code : List Bool) => decide (word = code))
      (const (alphabet.map (encodeOperation σ))) (decide_eq' (fst encBits encBits) (snd encBits encBits))
    simpa only [List.any_map, Function.comp_def] using h
  have h := hflag.ite ((optionSome encBits).comp id') (const none)
  apply h.of_enc_eq
  intro word
  cases hd : decodeOperation σ word with
  | none =>
    have hn : alphabet.any (fun operation => decide (word = encodeOperation σ operation)) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      obtain ⟨operation, _, hb⟩ := List.any_eq_true.mp hb
      have he : word = encodeOperation σ operation := of_decide_eq_true hb
      have heq := congrArg (decodeOperation σ) he
      rw [hd, decodeOperation_encodeOperation] at heq
      contradiction
    rw [hn]
    rfl
  | some operation =>
    have he : encodeOperation σ operation = word := encodeOperation_of_decodeOperation hd
    have hy : alphabet.any (fun operation => decide (word = encodeOperation σ operation)) = true := by
      exact List.any_eq_true.mpr ⟨operation, hmem operation, decide_eq_true he.symm⟩
    rw [hy]
    change true :: encodeOperation σ operation = true :: word
    exact congrArg (List.cons true) he

end KFOL.Complexity.FiniteTermMachines
