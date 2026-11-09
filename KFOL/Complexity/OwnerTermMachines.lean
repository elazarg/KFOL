module

public import KFOL.Complexity.FiniteTermMachines
public import KFOL.Definitions.Owner

/-! # Owner syntax as a finite-signature specialization

Reset and ternary guarded choice use the same finite-signature codec and native
constructors. The finite owner alphabet is fixed in these runtime statements.
-/

@[expose] public section

namespace KFOL.Complexity.OwnerTermMachines

open Turing.MultiTapeTM ComputableInPolyTime
open KFOL.FiniteTermCode

variable {Role : Type} [Fintype Role]

def operationEquiv : Operation (Owner.Symbol Role) ≃ Option Role where
  toFun p := match p with
    | ⟨_, .reset⟩ => none
    | ⟨_, .guarded owner⟩ => some owner
  invFun p := match p with
    | none => ⟨2, .reset⟩
    | some owner => ⟨3, .guarded owner⟩
  left_inv p := by cases p with | mk n symbol => cases symbol <;> rfl
  right_inv p := by cases p <;> rfl

noncomputable instance operationFintype : Fintype (Operation (Owner.Symbol Role)) :=
  Fintype.ofEquiv (Option Role) (operationEquiv (Role := Role)).symm

noncomputable abbrev termEncoding : Owner.Term Role ℕ ↪ List Bool :=
  FiniteTermMachines.termEncoding

@[fun_prop] theorem var_polyTime : ComputableInPolyTime
    (fun j : ℕ => (.var j : Owner.Term Role ℕ)) encNat termEncoding :=
  FiniteTermMachines.var_polyTime

@[fun_prop] theorem step_polyTime : ComputableInPolyTime
    (fun p : Owner.Term Role ℕ × Owner.Term Role ℕ => Owner.Term.step p.1 p.2)
    (encPair termEncoding termEncoding) termEncoding := by
  have hl := cons' (fst (termEncoding (Role := Role)) (termEncoding (Role := Role)))
    (cons' (snd (termEncoding (Role := Role)) (termEncoding (Role := Role))) (const []))
  have h := (FiniteTermMachines.construct_fixed_polyTime
    (⟨2, .reset⟩ : Operation (Owner.Symbol Role))).comp hl
  convert h using 1
  funext p
  unfold Owner.Term.step FiniteTermMachines.construct
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 := by omega
  rcases hi with rfl | rfl <;> simp

@[fun_prop] theorem guarded_polyTime (owner : Role) : ComputableInPolyTime
    (fun p : Owner.Term Role ℕ × (Owner.Term Role ℕ × Owner.Term Role ℕ) =>
      Owner.Term.guarded owner p.1 p.2.1 p.2.2)
    (encPair termEncoding (encPair termEncoding termEncoding)) termEncoding := by
  let input := encPair (termEncoding (Role := Role))
    (encPair (termEncoding (Role := Role)) (termEncoding (Role := Role)))
  have hx := fst (termEncoding (Role := Role))
    (encPair (termEncoding (Role := Role)) (termEncoding (Role := Role)))
  have hy : ComputableInPolyTime
      (fun p : Owner.Term Role ℕ × (Owner.Term Role ℕ × Owner.Term Role ℕ) => p.2.1)
      input termEncoding := by fun_prop
  have hz : ComputableInPolyTime
      (fun p : Owner.Term Role ℕ × (Owner.Term Role ℕ × Owner.Term Role ℕ) => p.2.2)
      input termEncoding := by fun_prop
  have hl := cons' hx (cons' hy (cons' hz (const [])))
  have h := (FiniteTermMachines.construct_fixed_polyTime
    (⟨3, .guarded owner⟩ : Operation (Owner.Symbol Role))).comp hl
  convert h using 1
  funext p
  unfold Owner.Term.guarded FiniteTermMachines.construct
  congr 1
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp

noncomputable def resetHeader : ℕ :=
  1 + (Words.delimit (encodeOperation (Owner.Symbol Role) ⟨2, .reset⟩)).length

noncomputable def guardedHeader (owner : Role) : ℕ :=
  1 + (Words.delimit (encodeOperation (Owner.Symbol Role) ⟨3, .guarded owner⟩)).length

theorem length_step (s t : Owner.Term Role ℕ) :
    (termEncoding (Owner.Term.step s t)).length =
      (termEncoding s).length + (termEncoding t).length + resetHeader (Role := Role) := by
  simp [termEncoding, FiniteTermMachines.termEncoding, Owner.Term.step, encode_func,
    resetHeader, List.ofFn_succ, add_comm, add_left_comm, add_assoc]

theorem length_guarded (owner : Role) (x y z : Owner.Term Role ℕ) :
    (termEncoding (Owner.Term.guarded owner x y z)).length =
      (termEncoding x).length + (termEncoding y).length + (termEncoding z).length + guardedHeader owner := by
  simp [termEncoding, FiniteTermMachines.termEncoding, Owner.Term.guarded, encode_func,
    guardedHeader, List.ofFn_succ, add_comm, add_left_comm, add_assoc]

end KFOL.Complexity.OwnerTermMachines
