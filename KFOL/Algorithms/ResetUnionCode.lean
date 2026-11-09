module

public import KFOL.Definitions.Reductions
public import KFOL.Algorithms.Words

/-! # Exact original prefix codes for native reset/union trees -/

@[expose] public section

namespace KFOL.ResetUnion

namespace Term

universe v
variable {Var : Type v}

@[simp] theorem size_var (j : Var) : size (.var j) = 1 := rfl
@[simp] theorem size_reset (s t : Term Var) : (s.reset t).size = 1 + s.size + t.size := rfl
@[simp] theorem size_union (s t : Term Var) : (s.union t).size = 1 + s.size + t.size := rfl

@[elab_as_elim] theorem induction_binary {P : Term Var → Prop}
    (var : ∀ j, P (.var j))
    (reset : ∀ s t, P s → P t → P (Term.reset s t))
    (union : ∀ s t, P s → P t → P (Term.union s t)) (t : Term Var) : P t := by
  induction t with
  | var j => exact var j
  | @func n f args ih =>
    cases f with
    | reset =>
      have he : FirstOrder.Language.Term.func Symbol.reset args = Term.reset (args 0) (args 1) := by
        congr 1
        funext i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;> rfl
      rw [he]
      exact reset _ _ (ih 0) (ih 1)
    | union =>
      have he : FirstOrder.Language.Term.func Symbol.union args = Term.union (args 0) (args 1) := by
        congr 1
        funext i
        have hi : i = 0 ∨ i = 1 := by omega
        rcases hi with rfl | rfl <;> rfl
      rw [he]
      exact union _ _ (ih 0) (ih 1)

end Term

namespace Code

open KFOL.Words

@[simp] theorem encode_var (j : ℕ) : encode (.var j) = false :: delimit (BinaryNatCode.encode j) := rfl
@[simp] theorem encode_reset (s t : Term ℕ) :
    encode (s.reset t) = true :: false :: (encode s ++ encode t) := rfl
@[simp] theorem encode_union (s t : Term ℕ) :
    encode (s.union t) = true :: true :: (encode s ++ encode t) := rfl

theorem size_le_length_encode (t : Term ℕ) : t.size ≤ (encode t).length := by
  induction t using Term.induction_binary with
  | var j => simp [encode_var]
  | reset s t hs ht => simp only [Term.size_reset, encode_reset, List.length_cons, List.length_append]; omega
  | union s t hs ht => simp only [Term.size_union, encode_union, List.length_cons, List.length_append]; omega

/-- Every valid subtree parses with size-bounded fuel, preserving any suffix. -/
theorem parse_encode (t : Term ℕ) (rest : List Bool) (fuel : ℕ)
    (hf : t.size ≤ fuel) : parse fuel (encode t ++ rest) = some (t, rest) := by
  induction t using Term.induction_binary generalizing rest fuel with
  | var j =>
    cases fuel with
    | zero => simp at hf
    | succ fuel => simp [parse, encode_var]
  | reset s t hs ht =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [Term.size_reset] at hf
      simp only [encode_reset, List.cons_append, List.append_assoc, parse]
      simp [hs (encode t ++ rest) fuel (by omega), ht rest fuel (by omega)]
  | union s t hs ht =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      simp only [Term.size_union] at hf
      simp only [encode_union, List.cons_append, List.append_assoc, parse]
      simp [hs (encode t ++ rest) fuel (by omega), ht rest fuel (by omega)]

/-- Successful parsing reconstructs the complete original prefix and suffix. -/
theorem encode_append_of_parse {fuel : ℕ} {word rest : List Bool} {t : Term ℕ}
    (h : parse fuel word = some (t, rest)) : encode t ++ rest = word := by
  induction fuel generalizing word rest t with
  | zero => cases h
  | succ fuel ih =>
    cases word with
    | nil => cases h
    | cons b word =>
      cases b with
      | false =>
        simp only [parse] at h
        obtain ⟨⟨name, tail⟩, hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨j, hj, he⟩ := Option.bind_eq_some_iff.mp h
        cases Option.some.inj he
        have hn := (BinaryNatCode.decode?_eq_some_iff name j).mp hj
        simp only [encode_var, List.cons_append, ← hn]
        exact congrArg (List.cons false) (eq_delimit_append_of_unpair?_eq_some hp).symm
      | true =>
        cases word with
        | nil => cases h
        | cons operation word =>
          simp only [parse] at h
          obtain ⟨⟨s, tail⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨⟨u, suffix⟩, hu, he⟩ := Option.bind_eq_some_iff.mp h
          cases Option.some.inj he
          cases operation <;>
            simp only [Bool.false_eq_true, ite_false, ite_true, encode_reset, encode_union,
              List.cons_append, List.append_assoc, ih hu, ih hs]

@[simp] theorem decode_encode (t : Term ℕ) : decode (encode t) = some t := by
  unfold decode
  have hp := parse_encode t [] (encode t).length (size_le_length_encode t)
  simp only [List.append_nil] at hp
  rw [hp]
  rfl

theorem encode_of_decode {word : List Bool} {t : Term ℕ} (h : decode word = some t) : encode t = word := by
  unfold decode at h
  obtain ⟨⟨s, rest⟩, hs, h⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.isEmpty then some s else none) = some t at h
  split at h
  next hr =>
    cases Option.some.inj h
    have hr : rest = [] := List.isEmpty_iff.mp hr
    simpa only [hr, List.append_nil] using encode_append_of_parse hs
  next => cases h

theorem encode_injective : Function.Injective encode := by
  intro s t he
  have h := congrArg decode he
  simpa only [decode_encode, Option.some.injEq] using h

@[simp] theorem decodeEquation_encodeEquation (equation : Equation) :
    decodeEquation (encodeEquation equation) = some equation := by
  rcases equation with ⟨s, t⟩
  simp [decodeEquation, encodeEquation]

theorem encodeEquation_injective : Function.Injective encodeEquation := by
  intro s t he
  have h := congrArg decodeEquation he
  simpa only [decodeEquation_encodeEquation, Option.some.injEq] using h

end Code
end KFOL.ResetUnion
