module

public import KFOL.Complexity.OwnerTermMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-! # Native construction of exact owner paths from recorded frames -/

@[expose] public section

namespace KFOL.Complexity.OwnerTermMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

variable {Role : Type} [Fintype Role]

abbrev Frame := ℕ × ℕ
abbrev frameEncoding := encPair encNat encNat
abbrev PathInput (Role : Type) := ℕ × (List Frame × Owner.Term Role ℕ)
noncomputable abbrev pathEncoding :=
  encPair encNat (encPair (encList frameEncoding) (termEncoding (Role := Role)))

private def wrap (owner : Role) (root : ℕ) (term : Owner.Term Role ℕ) (frame : Frame) : Owner.Term Role ℕ :=
  Owner.Term.guarded owner (.var root) (Owner.Term.step term (.var frame.1)) (.var frame.2)

private theorem wrap_polyTime (owner : Role) : ComputableInPolyTime
    (fun p : (ℕ × Owner.Term Role ℕ) × Frame => wrap owner p.1.1 p.1.2 p.2)
    (encPair (encPair encNat termEncoding) frameEncoding) termEncoding := by
  let input := encPair (encPair encNat (termEncoding (Role := Role))) frameEncoding
  have hr : ComputableInPolyTime (fun p : (ℕ × Owner.Term Role ℕ) × Frame => p.1.1) input encNat := by fun_prop
  have ht : ComputableInPolyTime (fun p : (ℕ × Owner.Term Role ℕ) × Frame => p.1.2) input termEncoding := by fun_prop
  have hw : ComputableInPolyTime (fun p : (ℕ × Owner.Term Role ℕ) × Frame => p.2.1) input encNat := by fun_prop
  have hz : ComputableInPolyTime (fun p : (ℕ × Owner.Term Role ℕ) × Frame => p.2.2) input encNat := by fun_prop
  exact (guarded_polyTime owner).comp ((var_polyTime.comp hr).prod
    ((step_polyTime.comp (ht.prod (var_polyTime.comp hw))).prod (var_polyTime.comp hz)))

private theorem length_var (j : ℕ) :
    ((termEncoding (Role := Role)) (.var j)).length = 2 * (encNat j).length + 3 := by
  simp [termEncoding, FiniteTermMachines.termEncoding, encode_var, encNat_apply,
    Words.BinaryNatCode.encode]

private theorem wrap_growth (owner : Role) (root : ℕ) (term : Owner.Term Role ℕ) (frame : Frame) :
    (termEncoding (wrap owner root term frame)).length ≤ (termEncoding term).length +
      (2 * (encNat root).length + 2 * (frameEncoding frame).length +
        resetHeader (Role := Role) + guardedHeader owner + 9) := by
  simp only [wrap, length_guarded, length_step, length_var, frameEncoding, length_encPair]
  omega

omit [Fintype Role] in
private theorem pathBody_fold (owner : Role) (root : ℕ) (frames : List Frame) (fill : Owner.Term Role ℕ) :
    Owner.Term.pathBody owner root frames fill = frames.foldr (fun frame term => wrap owner root term frame) fill := by
  induction frames generalizing fill with
  | nil => rfl
  | cons frame frames ih => simp only [Owner.Term.pathBody, List.foldr_cons, wrap, ih]

/-- Exact source path-body construction; each stored frame contains only one
recursive occurrence, so the accumulator grows additively. -/
theorem pathBody_polyTime (owner : Role) : ComputableInPolyTime
    (fun input : PathInput Role => Owner.Term.pathBody owner input.1 input.2.1 input.2.2)
    pathEncoding termEncoding := by
  let input := pathEncoding (Role := Role)
  have hr : ComputableInPolyTime (fun p : PathInput Role => p.1) input encNat := fst _ _
  have hframes : ComputableInPolyTime (fun p : PathInput Role => p.2.1) input
      (encList frameEncoding) := by fun_prop
  have hfill : ComputableInPolyTime (fun p : PathInput Role => p.2.2) input termEncoding := by fun_prop
  have hreverse := (ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse frameEncoding)).comp hframes
  have hroot : ComputableInPolyTime (fun p : ((PathInput Role) × Owner.Term Role ℕ) × Frame => p.1.1.1)
      (encPair (encPair input termEncoding) frameEncoding) encNat := by fun_prop
  have hstate : ComputableInPolyTime (fun p : ((PathInput Role) × Owner.Term Role ℕ) × Frame => p.1.2)
      (encPair (encPair input termEncoding) frameEncoding) termEncoding := by fun_prop
  have hframe := snd (encPair input (termEncoding (Role := Role))) frameEncoding
  have hstep := (wrap_polyTime owner).comp ((hroot.prod hstate).prod hframe)
  have hbound := ((hr.polyBounded_length.mul (PolyBounded.const 2)).add
    (hframes.polyBounded_length.mul (PolyBounded.const 2))).add
    (PolyBounded.const (resetHeader (Role := Role) + guardedHeader owner + 9))
  have h := foldlWithInput_of_bounded_growth (list := fun p : PathInput Role => p.2.1.reverse)
    (init := fun p => p.2.2) (step := fun p term frame => wrap owner p.1 term frame)
    hfill ⟨hreverse, hstep, inferInstance, inferInstance⟩
    (growth := fun p => 2 * (encNat p.1).length + 2 * (encList frameEncoding p.2.1).length +
      resetHeader (Role := Role) + guardedHeader owner + 9)
    ⟨by convert hbound using 1; simp [Nat.mul_comm, Nat.add_assoc], ?_⟩
  · convert h using 1
    funext p
    rw [List.foldl_reverse, pathBody_fold]
  · intro p state frame hframe
    have hf := SizedListEncoding.length_elem_le (encA := frameEncoding)
      (encL := encList frameEncoding) p.2.1 frame (List.mem_reverse.mp hframe)
    have hg := wrap_growth owner p.1 state frame
    omega

/-- Add the report's initial reset frame to the exact path body. -/
theorem pathTerm_polyTime (owner : Role) : ComputableInPolyTime
    (fun input : PathInput Role => Owner.Term.pathTerm owner input.1 input.2.1 input.2.2)
    pathEncoding termEncoding := by
  have hr : ComputableInPolyTime (fun p : PathInput Role => p.1)
      pathEncoding encNat := fst _ _
  exact step_polyTime.comp ((pathBody_polyTime owner).prod (var_polyTime.comp hr))

end KFOL.Complexity.OwnerTermMachines
