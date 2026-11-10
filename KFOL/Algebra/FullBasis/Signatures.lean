module

public import KFOL.Algebra.FullBasis.Transfer
public import Mathlib.Data.Fintype.Perm

/-! # The two genuine signatures and the embedded core copy -/

@[expose] public section
namespace KFOL.Envelope
universe u v w
variable {Role : Type u} {M : Type v} {Var : Type w}
variable [(Equational.language (Equational.CoreSymbol Role)).Structure M]

omit [(Equational.language (Equational.CoreSymbol Role)).Structure M] in
theorem card_carrier [DecidableEq Role] [Fintype Role] [Fintype M] :
    Fintype.card (Carrier Role M) = 1 + (Fintype.card Role).factorial * Fintype.card M := by
  simp [Carrier, Fintype.card_perm, Nat.add_comm]

theorem public_eval_decode (t : Equational.Term (Equational.PublicSymbol Role) Var)
    (valuation : Var → Carrier Role M) :
    let _ := publicStructureOf (Role := Role) (M := M)
    eval valuation (Equational.Public.decode t) = t.realize valuation := by
  let _ := publicStructureOf (Role := Role) (M := M)
  induction t with
  | var => rfl
  | @func n f args ih =>
    cases f with
    | winner => rfl
    | choice r => exact congrArg₂ (choice r) (ih 0) (ih 1)

theorem public_small_identities (three : Fin 3 ↪ Role) (fallback : M) (n : ℕ)
    (small : ∀ e : Equational.Identity (Equational.CoreSymbol Role), e.arity ≤ n + 1 →
      (let _ := Equational.coreStructure Role; e.Holds (WinnerSet Role)) → e.Holds M)
    (e : Equational.Identity (Equational.PublicSymbol Role)) (arity : e.arity ≤ n)
    (valid : let _ := Equational.publicStructure Role; e.Holds (WinnerSet Role)) :
    let _ := publicStructureOf (Role := Role) (M := M); e.Holds (Carrier Role M) := by
  let _ := publicStructureOf (Role := Role) (M := M)
  change ∀ valuation : Fin e.arity → Carrier Role M,
    e.lhs.realize valuation = e.rhs.realize valuation
  intro valuation
  rw [← public_eval_decode, ← public_eval_decode]
  apply equation_of_core_identities three fallback
  · intro v
    simpa only [Equational.Public.eval_decode] using valid v
  · intro s t h v
    apply core_equation_fintype (n + 1) small _ s t h v
    simpa only [Fintype.card_option, Fintype.card_fin] using Nat.add_le_add_right arity 1

/-- The identity-labelled copy is an actual core subalgebra, for arbitrary
payload operations. Hence no failed core identity is repaired by the envelope. -/
theorem eval_core_copy (t : Equational.Term (Equational.CoreSymbol Role) Var)
    (valuation : Var → M) :
    eval (fun j => some (1,valuation j)) (Equational.Core.decode t) =
      some (1,t.realize valuation) := by
  classical
  induction t using Core.induction_choice with
  | var => rfl
  | choice r s t hs ht =>
    rw [Core.realize_choice]
    simp only [Core.choiceTerm, Equational.Core.decode, ite_true, one_ne_zero,
      ite_false, eval, hs, ht, choice, ite_true, inv_one, Equiv.Perm.one_apply]

theorem core_variety_of_full [Nonempty M]
    (h : let _ := Equational.fullStructure Role
      let _ := structureOf (Role := Role) (M := M)
      Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) (Carrier Role M)) :
    let _ := Equational.coreStructure Role
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M := by
  let _ := Equational.coreStructure Role
  let _ := Equational.fullStructure Role
  let _ := structureOf (Role := Role) (M := M)
  refine ⟨inferInstance, ?_⟩
  intro e he valuation
  let lifted : Equational.Identity (Equational.FullSymbol Role) :=
    ⟨e.arity, Equational.Full.encode (Equational.Core.decode e.lhs),
      Equational.Full.encode (Equational.Core.decode e.rhs)⟩
  have hl : lifted.Holds (WinnerSet Role) := by
    intro v
    simpa only [lifted, ← Equational.Full.eval_decode, Equational.Full.decode_encode,
      Equational.Core.eval_decode] using he v
  have hv := h.2 lifted hl (fun j => some (1,valuation j))
  rw [← eval_decode, ← eval_decode] at hv
  simp only [lifted, Equational.Full.decode_encode, eval_core_copy,
    Option.some.injEq, Prod.mk.injEq, true_and] at hv
  exact hv

theorem core_variety_of_public [Nonempty M]
    (h : let _ := Equational.publicStructure Role
      let _ := publicStructureOf (Role := Role) (M := M)
      Equational.InVariety (Equational.PublicSymbol Role) (WinnerSet Role) (Carrier Role M)) :
    let _ := Equational.coreStructure Role
    Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M := by
  let _ := Equational.coreStructure Role
  let _ := Equational.publicStructure Role
  let _ := publicStructureOf (Role := Role) (M := M)
  refine ⟨inferInstance, ?_⟩
  intro e he valuation
  let lifted : Equational.Identity (Equational.PublicSymbol Role) :=
    ⟨e.arity, Equational.Public.ofCore e.lhs, Equational.Public.ofCore e.rhs⟩
  have hl : lifted.Holds (WinnerSet Role) := by
    intro v
    simpa only [lifted, ← Equational.Public.eval_decode, Equational.Public.decode_ofCore,
      Equational.Core.eval_decode] using he v
  have hv := h.2 lifted hl (fun j => some (1,valuation j))
  rw [← public_eval_decode, ← public_eval_decode] at hv
  simp only [lifted, Equational.Public.decode_ofCore, eval_core_copy,
    Option.some.injEq, Prod.mk.injEq, true_and] at hv
  exact hv

/-- The envelope preserves and reflects membership in the generated
varieties. Its two expansions use the same independently specified carrier. -/
theorem variety_iff [Nonempty M] (three : Fin 3 ↪ Role) :
    let _ := Equational.coreStructure Role
    let _ := Equational.publicStructure Role
    let _ := Equational.fullStructure Role
    let _ := structureOf (Role := Role) (M := M)
    let _ := publicStructureOf (Role := Role) (M := M)
    (Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M ↔
      Equational.InVariety (Equational.PublicSymbol Role) (WinnerSet Role) (Carrier Role M)) ∧
    (Equational.InVariety (Equational.CoreSymbol Role) (WinnerSet Role) M ↔
      Equational.InVariety (Equational.FullSymbol Role) (WinnerSet Role) (Carrier Role M)) := by
  let _ := Equational.coreStructure Role
  let _ := Equational.publicStructure Role
  let _ := Equational.fullStructure Role
  let _ := structureOf (Role := Role) (M := M)
  let _ := publicStructureOf (Role := Role) (M := M)
  refine ⟨⟨?_,core_variety_of_public⟩,⟨?_,core_variety_of_full⟩⟩
  · intro h
    refine ⟨inferInstance,?_⟩
    intro e he
    exact public_small_identities three (Classical.arbitrary M) e.arity
      (fun f _ hf => h.2 f hf) e (Nat.le_refl _) he
  · intro h
    refine ⟨inferInstance,?_⟩
    intro e he
    exact full_small_identities three (Classical.arbitrary M) e.arity
      (fun f _ hf => h.2 f hf) e (Nat.le_refl _) he

end KFOL.Envelope
