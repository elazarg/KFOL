module

public import KFOL.Complexity.TablePeelingSpace

/-! # Translating a bounded binary owner count to unary

Each nonnullary complete table has at least one entry per owner. The
declared owner count can therefore be converted to unary after a length
check even on malformed inputs, where the count may be arbitrarily large.
-/

@[expose] public section
namespace KFOL.Complexity.ExplicitOwnerEncoding

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity
open Core.ProfileBudgets AddressedPoint AddressedSourceOutput

variable {A : Type} {e : A ↪ List Bool} {L : Set (ℕ × A)}

/-- A language with an explicit unary upper bound on its first component
has the same PSPACE classification for unary and binary integer headers. -/
theorem complete_binary {limit : A → ℕ} (poly : ComputableInPolyTime limit e encUnary)
    (bounded : ∀ x ∈ L, x.1 ≤ limit x.2) (zero : ∀ a, (0,a) ∉ L)
    (unary : PSPACEComplete (encPair encUnary e) L) :
    PSPACEComplete (encPair encNat e) L := by
  let clip (x : ℕ × A) := if x.1 ≤ limit x.2 then min (limit x.2) x.1 else 0
  have clipped : ComputableInPolyTime clip (encPair encNat e) encUnary := by
    let k := fst encNat e
    let bound := poly.comp (snd encNat e)
    simpa only [clip,Function.comp_apply,decide_eq_true_eq] using
      (binary_le' k (unary_to_binary.comp bound)).ite (binary_min_unary' bound k) (const 0)
  have down : PolyTimeReducible (encPair encNat e) (encPair encUnary e) L L := by
    refine ⟨fun x => (clip x,x.2),clipped.prod (snd _ _),fun x => ?_⟩
    by_cases ok : x.1 ≤ limit x.2
    · simp only [clip,ite_eq_left ok,Nat.min_eq_right ok,Prod.mk.eta]
    · simp only [clip,ite_eq_right ok]
      exact ⟨fun yes => (ok (bounded x yes)).elim, fun yes => (zero x.2 yes).elim⟩
  have up : PolyTimeReducible (encPair encUnary e) (encPair encNat e) L L :=
    ⟨fun x => (x.1,x.2),(unary_to_binary.comp (fst _ _)).prod (snd _ _),fun _ => Iff.rfl⟩
  exact ⟨down.mem_PSPACE unary.1,unary.2.trans up⟩

private theorem arity_pos {K d : ℕ} (t : CoreTerm (Fin K) (Fin d)) : 0 < d := by
  induction t using Core.induction_choice with
  | var j => exact Nat.zero_lt_of_lt j.isLt
  | choice _ _ _ hx _ => exact hx

theorem winner_bound {k : ℕ} {p : TableInput} (yes : RawAccepts k p) : k ≤ p.2.length := by
  obtain ⟨hlen,t,_⟩ := yes
  have arity := arity_pos t
  have base : k ≤ 2^k-1 := by have : k < 2^k := Nat.lt_two_pow_self; omega
  rw [hlen]
  obtain rfl | pos := Nat.eq_zero_or_pos k
  · exact Nat.zero_le _
  exact base.trans (le_self_pow₀ (by omega) arity.ne')

theorem source_bound {k : ℕ} (three : Fin 3 ↪ Fin k) {p : ℕ × List Bool}
    (yes : p ∈ AddressedSourceOutput.language three) : k ≤ p.2.length := by
  obtain ⟨hlen,t,_⟩ := yes
  have arity := arity_pos t
  have pos := (three 0).isLt
  rw [hlen]
  exact (le_self_pow₀ (by omega : 1 ≤ k) arity.ne').trans (Nat.le_mul_of_pos_left _ arity)

end KFOL.Complexity.ExplicitOwnerEncoding
