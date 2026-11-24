module

public import KFOL.Complexity.ExplicitTableUniform

/-! # Recognition with binary arity and owner count

A positive instance has at least as many entries as its arity. Thus the
verifier can cap the arity before converting it to unary, even on an
incorrectly declared table. The language and the order of its entries
are the same for the two header encodings.
-/

@[expose] public section
namespace KFOL.Complexity.ExplicitTableBinaryHeaders

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Complexity

private def swap {A : Type} (x : ℕ × (ℕ × A)) := (x.2.1,x.1,x.2.2)

private theorem swap_poly {A : Type} (k d : ℕ ↪ List Bool) (body : A ↪ List Bool) :
    ComputableInPolyTime swap (encPair k (encPair d body)) (encPair d (encPair k body)) :=
  ((fst d body).comp (snd k _)).prod ((fst k _).prod ((snd d body).comp (snd k _)))

private theorem swap_complete {A : Type} (k d : ℕ ↪ List Bool) (body : A ↪ List Bool)
    (L : Set (ℕ × (ℕ × A))) (h : PSPACEComplete (encPair k (encPair d body)) L) :
    PSPACEComplete (encPair d (encPair k body)) {x | swap x ∈ L} := by
  have back : PolyTimeReducible (encPair d (encPair k body)) (encPair k (encPair d body))
      {x | swap x ∈ L} L := ⟨_,swap_poly d k body,fun _ => Iff.rfl⟩
  have forth : PolyTimeReducible (encPair k (encPair d body)) (encPair d (encPair k body))
      L {x | swap x ∈ L} := ⟨_,swap_poly k d body,fun _ => Iff.rfl⟩
  exact ⟨back.mem_PSPACE h.1,h.2.trans forth⟩

private theorem binary_arity {A : Type} {e : A ↪ List Bool} {L : Set (ℕ × (ℕ × A))}
    {size : A → ℕ} (readSize : ComputableInPolyTime size e encUnary)
    (bound : ∀ x ∈ L, x.2.1 ≤ size x.2.2) (zero : ∀ k a, (k,0,a) ∉ L)
    (known : PSPACEComplete (encPair encNat (encPair encUnary e)) L) :
    PSPACEComplete (encPair encNat (encPair encNat e)) L := by
  let S : Set (ℕ × (ℕ × A)) := {x | swap x ∈ L}
  have binary : PSPACEComplete (encPair encNat (encPair encNat e)) S :=
    ExplicitOwnerEncoding.complete_binary (L := S) (limit := fun x => size x.2)
      (readSize.comp (snd encNat e)) (fun x hx => bound (swap x) hx)
      (fun x => zero x.1 x.2) (swap_complete encNat encUnary e L known)
  exact swap_complete encNat encNat e S binary

abbrev winnerEncoding := encPair encNat (encPair encNat AddressedPoint.menusEncoding)
abbrev sourceEncoding := encPair encNat (encPair encNat encBits)

/-- The complete operation table has binary owner count and binary arity. -/
theorem winner_complete : PSPACEComplete winnerEncoding TablePeelingWinnerUniform.language := by
  apply binary_arity (size := fun rows : AddressedPoint.Menus => rows.length) _ _ _
    ExplicitTableUniform.winner_complete
  · exact .of_tidy (ComputableTidilyInPolyTime.length AddressedEnvelope.namesEncoding)
  · intro x yes
    obtain ⟨hk,len,_⟩ := yes
    rw [len]
    have base : 2 ≤ 2^x.1-1 := by
      have h := Nat.lt_two_pow_self (n := x.1)
      omega
    exact (Nat.le_of_lt (Nat.lt_two_pow_self (n := x.2.1))).trans (Nat.pow_le_pow_left base _)
  · rintro k rows ⟨_,_,t,_⟩
    exact (Nat.lt_irrefl 0) (ExplicitOwnerEncoding.arity_pos t)

/-- The packed table of source probes has binary owner count and binary arity. -/
theorem source_complete : PSPACEComplete sourceEncoding UniformSourceSpace.language := by
  apply binary_arity (size := List.length (α := Bool)) length_bits _ _
    ExplicitTableUniform.source_complete
  · rintro x ⟨h,len,_⟩
    rw [len]
    exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  · rintro k bits ⟨_,_,t,_⟩
    exact (Nat.lt_irrefl 0) (ExplicitOwnerEncoding.arity_pos t)

end KFOL.Complexity.ExplicitTableBinaryHeaders
