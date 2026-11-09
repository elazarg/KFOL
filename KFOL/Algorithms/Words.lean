/-
Framing proofs adapted from ComplexityLib v1, revision 257ad90.
Copyright (c) 2025-2026 Samuel Schlesinger and Bolton Bailey.
Released under Apache 2.0 license; see LICENSES/Apache-2.0.txt.
-/
module

public import KFOL.Definitions.Encoding

/-! # Backend-independent binary names and complete framing

The paper codec preserves its existing two-bit separator. Native machine
encodings are connected by separate efficiency proofs, never identified with it.
-/

@[expose] public section

namespace KFOL.Words

namespace BinaryNatCode

@[simp] theorem value_bits (n : ℕ) : value n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn, value, ih]

@[simp] theorem length_encode (n : ℕ) : (encode n).length = n.size :=
  Nat.size_eq_bits_len n

@[simp] theorem decode?_encode (n : ℕ) : decode? (encode n) = some n := by
  simp [decode?, encode]

theorem decode?_eq_some_iff (bits : List Bool) (n : ℕ) :
    decode? bits = some n ↔ bits = encode n := by
  constructor
  · intro h
    change (if (value bits).bits = bits then some (value bits) else none) = some n at h
    split at h
    next hc => cases h; exact hc.symm
    next => cases h
  · rintro rfl
    exact decode?_encode n

end BinaryNatCode

@[simp] theorem delimit_nil : delimit [] = [false, true] := rfl

@[simp] theorem delimit_cons (b : Bool) (l : List Bool) :
    delimit (b :: l) = b :: b :: delimit l := by
  simp [delimit]

@[simp] theorem delimit_length (l : List Bool) : (delimit l).length = 2 * l.length + 2 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [delimit_cons, List.length_cons, ih]; omega

/-- `unpair?` reads back the framing written by `delimit`: parsing one block off the front
    of any input recovers the payload and the remaining suffix. -/
@[simp] theorem unpair?_delimit_append (x y : List Bool) :
    unpair? (delimit x ++ y) = some (x, y) := by
  induction x with
  | nil => simp [unpair?]
  | cons b x ih => cases b <;> simp [unpair?, ih]

/-- Soundness of the parser: a successful parse decomposes the input as the parsed payload's
    framing followed by the leftover suffix. -/
theorem eq_delimit_append_of_unpair?_eq_some :
    ∀ {z x y : List Bool}, unpair? z = some (x, y) → z = delimit x ++ y
  | [], _, _, h => by simp [unpair?] at h
  | [b], _, _, h => by cases b <;> simp [unpair?] at h
  | false :: true :: rest, x, y, h => by
    simp only [unpair?, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | false :: false :: rest, x, y, h => by
    simp only [unpair?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : false :: p₁ = x ∧ p₂ = y := by simpa [Prod.ext_iff] using heq
    simp only [eq_delimit_append_of_unpair?_eq_some hp, delimit_cons, List.cons_append]
  | true :: true :: rest, x, y, h => by
    simp only [unpair?, Option.map_eq_some_iff] at h
    obtain ⟨⟨p₁, p₂⟩, hp, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : true :: p₁ = x ∧ p₂ = y := by simpa [Prod.ext_iff] using heq
    simp only [eq_delimit_append_of_unpair?_eq_some hp, delimit_cons, List.cons_append]
  | true :: false :: rest, _, _, h => by simp [unpair?] at h

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      delimit_length]
    omega

private theorem undelimitBlocksAux_flatten_delimit (l : List (List Bool)) :
    ∀ fuel, l.length ≤ fuel → undelimitBlocksAux fuel ((l.map delimit).flatten) = some l := by
  induction l with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons b t ih =>
    intro fuel hfuel
    rw [List.length_cons] at hfuel
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hd, tl, hcons⟩ : ∃ hd tl, delimit b ++ (t.map delimit).flatten = hd :: tl := by
      cases b <;> exact ⟨_, _, rfl⟩
    simp only [List.map_cons, List.flatten_cons, hcons, undelimitBlocksAux]
    rw [← hcons, unpair?_delimit_append]
    simp [ih fuel (by omega)]

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    undelimitBlocks ((l.map delimit).flatten) = some l :=
  undelimitBlocksAux_flatten_delimit l _ (length_le_length_flatten_delimit l)

@[simp] theorem pair_length (x y : List Bool) :
    (pair x y).length = 2 * x.length + 2 + y.length := by
  simp [pair]

@[simp] theorem unpair?_pair (x y : List Bool) : unpair? (pair x y) = some (x, y) :=
  unpair?_delimit_append x y

theorem eq_pair_of_unpair?_eq_some {z x y : List Bool} (h : unpair? z = some (x, y)) :
    z = pair x y := eq_delimit_append_of_unpair?_eq_some h

theorem unpair?_eq_some_iff {z x y : List Bool} :
    unpair? z = some (x, y) ↔ z = pair x y :=
  ⟨eq_pair_of_unpair?_eq_some, fun h => h ▸ unpair?_pair x y⟩

end KFOL.Words
